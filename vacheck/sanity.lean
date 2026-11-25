import Lean.AddDecl
import Lean.CoreM
import Lean.Data.Json.Parser
import Lean.Util.FoldConsts
import LeanExport.Parse

/-!
The sanity helper of vacheck: for each pair of a theorem and a definition in its statement, whether
the kernel accepts the developer's own proof with the definition replaced by a variable of its type.

    sanity TARGETS EXPORT

TARGETS holds one JSON line `[i, j, theorem, definition]` per pair, as `vacheck sanity-targets`
writes it: two indices, then two names as the JSON arrays of their components (a string for
`Name.str`, a number for `Name.num`). For each line, in order, the helper prints `i j` and a verdict:
- `any`: the kernel accepts `∀ x : τ, S[x/X]`, proved by `fun x => p[x/X]`, where `X : τ` is the
  definition and `p : S` the theorem. The claim holds whatever `X` is.
- `needed`: the kernel rejects it.
- `skipped`: no verdict. The theorem is not a theorem of the export, or the definition is not a
  definition without universe parameters, or the replay failed or spent `replayHeartbeats`, or the
  re-check reached a limit (its `heartbeats`, the kernel's recursion depth or memory, an interrupt),
  or the re-checks before it spent `totalHeartbeats`.

It replays only what the pairs need: the closure of their theorems and definitions. Every limit is
counted in heartbeats, the same on every run, so two honest checks of one export give the same
verdicts.

It exits 0 with one verdict per line, or 1 with one line on stderr when a file cannot be read or a
line of TARGETS is not of that shape. Names cross only as data; the output holds only indices.

It ships inside vacheck.pyz (`vacheck sanity-source` prints it). The check job compiles it with the
project's toolchain, `lean -c`, then `leanc -lLeanExport`, and runs it in the sandbox. As a safety
net, well above what the budgets allow (about 4 minutes of replay and 4 of re-checks on v4.36.0),
it has 30 minutes and 8 GiB of memory, a cgroup's `memory.max`: under an address-space limit
(`ulimit -v`, even 4 GiB) the Lean runtime cannot start its threads. A helper stopped there, or that
exits with anything but 0, is read as every pair skipped (`vacheck analyze --sanity-stopped`), and
result.json says `"sanity": "stopped"`: the sanity step never fails a check.
-/

open Lean

/-- The kernel heartbeats, in thousands, one re-check may use: Lean's default `maxHeartbeats`. The
kernel counts them itself, one per step of its type checker, and stops the re-check past them. -/
def heartbeats : Nat := 200000

/-- The kernel's recursion depth for a re-check: Lean's default `maxRecDepth` (the kernel allows 16
times as deep). -/
def recDepth : Nat := 512

/-- The heartbeats, in thousands, that the re-checks together may use, as `IO.getNumHeartbeats`
counts them: small allocations, about four per kernel heartbeat. Once the re-checks so far have
spent them, every pair left is skipped, so the count is the same on every run. A million is about
two minutes of re-checking on v4.36.0, and the last re-check may spend up to `heartbeats` past it. -/
def totalHeartbeats : Nat := 1000000

/-- A name from the JSON array of its components: strings for `Name.str`, numbers for `Name.num`.
As `nameOf` in the action's Reference.lean. -/
def nameOf (j : Json) : Except String Name := do
  let comps ← j.getArr?
  if comps.isEmpty then throw "a name without components"
  comps.foldlM (init := .anonymous) fun n c =>
    match c with
    | .str s => pure (n.str s)
    | .num k =>
      if k.exponent == 0 && k.mantissa ≥ 0 then pure (n.num k.mantissa.toNat)
      else throw "a name component that is not a natural number"
    | _ => throw "a name component that is neither a string nor a number"

/-- A natural number: a JSON number with no decimal places, at least 0 (Lean reads `1e2` as 100). -/
def natOf : Json → Except String Nat
  | .num k => if k.exponent == 0 && k.mantissa ≥ 0 then pure k.mantissa.toNat else throw "not a natural number"
  | _ => throw "not a number"

/-- One line of TARGETS. -/
structure Target where
  i : Nat
  j : Nat
  thm : Name
  defn : Name

def targetOf (line : String) : Except String Target := do
  match ← Json.parse line with
  | .arr #[i, j, t, d] => return ⟨← natOf i, ← natOf j, ← nameOf t, ← nameOf d⟩
  | _ => throw "not [i, j, theorem, definition]"

/-- The kernel adds these three with `Quot` itself. -/
def quotTargets : List Name := [``Quot.mk, ``Quot.lift, ``Quot.ind]

/-- The names of `map` that `roots` reach through the constants each one uses, closed as `replay`
needs: an inductive type with its whole block and its constructors, a constructor or a recursor
with its types, the quotient with `Eq`, and a use of `Quot.mk`, `Quot.lift` or `Quot.ind` as one of
`Quot`. -/
def closure (map : Std.HashMap Name ConstantInfo) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[]
  for r in roots do
    todo := todo.push r
  repeat
    let some n := todo.back? | break
    todo := todo.pop
    if seen.contains n then continue
    let some ci := map[n]? | continue
    seen := seen.insert n
    let more := match ci with
      | .inductInfo v => v.all ++ v.ctors
      | .ctorInfo v => [v.induct]
      | .recInfo v => v.all
      | .quotInfo _ => [``Eq]
      | _ => []
    for m in ci.getUsedConstantsAsSet.toList ++ more do
      let m := if quotTargets.contains m then ``Quot else m
      unless seen.contains m do todo := todo.push m
  return seen

/-! The replay of what the pairs need: the closure of their theorems and definitions, sent to the
kernel as `leanchecker --from-export` sends an export, by `Lean.Replay`'s algorithm (Lean 4,
src/Lean/Replay.lean, Apache-2.0, adapted): each declaration after those it names, an inductive
type with its block, its constructors and recursors compared with those the kernel made. Two changes:
- `String.ofList` and `Char.ofNat` go first, as lean4#15853 has it: the kernel unfolds string
  literals to them, and no declaration names them.
- Every declaration is added with `replayHeartbeats`, in one task. The kernel's count of heartbeats
  is the thread's, set to zero only as a task starts, so the budget bounds the replay as a whole,
  and a replay past it stops at the same declaration on every run. -/

/-- The kernel heartbeats, in thousands, that the replay of what the pairs need may use in all. -/
def replayHeartbeats : Nat := 500000

namespace Replay

structure State where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}

abbrev M := ReaderT (Std.HashMap Name ConstantInfo) <| StateRefT State IO

/-- Whether `name` is still to replay; if so, it is pending from now on. -/
def isTodo (name : Name) : M Bool := do
  if (← get).remaining.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  return false

/-- The kernel's limits for the replay: `replayHeartbeats` in all, and no depth limit, as leanchecker
has none. -/
def options : Options := maxRecDepth.set (maxHeartbeats.set {} replayHeartbeats) 0

def addDecl (d : Declaration) : M Unit := do
  match Kernel.Environment.addDecl (← get).env options d with
  | .ok env => modify fun s => { s with env }
  | .error .deterministicTimeout => throw <| .userError "the replay ran out of heartbeats"
  | .error _ => throw <| .userError "the kernel rejects a declaration"

mutual
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read)[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    -- A mutual block may have taken care of it.
    if (← get).pending.contains name then
      match ci with
      | .defnInfo info => addDecl (.defnDecl info)
      | .thmInfo info =>
        -- A duplicate theorem, as an import of the module system may give, is added once.
        if let some (.thmInfo info') := (← get).env.find? ci.name then
          if info.name == info'.name && info.type == info'.type && info.levelParams == info'.levelParams
              && info.all == info'.all then
            return
        addDecl (.thmDecl info)
      | .axiomInfo info => addDecl (.axiomDecl info)
      | .opaqueInfo info => addDecl (.opaqueDecl info)
      | .inductInfo info =>
        let all ← info.all.mapM fun n => do pure ((← read)[n]!)
        for o in all do
          modify fun s => { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => do
          pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do pure ((← read)[n]!))
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstantsAsSet
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name, type := ci.type, ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        addDecl (.inductDecl info.levelParams info.numParams types false)
      | .ctorInfo info =>
        modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
      | .recInfo info =>
        modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
      | .quotInfo _ =>
        -- Quot.lift and Quot.ind have types that name Eq.
        replayConstant ``Eq
        addDecl .quotDecl
      modify fun s => { s with pending := s.pending.erase name }

partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n
end

/-- The constructors and recursors of the replayed map are those the kernel made. -/
def checkPostponed : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.find? ctor, (← read)[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      unless info == info' do throw <| .userError "a constructor differs from the kernel's"
    | _, _ => throw <| .userError "a constructor is missing"
  for rec in (← get).postponedRecursors do
    match (← get).env.find? rec, (← read)[rec]? with
    | some (.recInfo info), some (.recInfo info') =>
      unless info == info' do throw <| .userError "a recursor differs from the kernel's"
    | _, _ => throw <| .userError "a recursor is missing"

end Replay

/-- The kernel's environment of the map, replayed as above: in a task of its own, so that its
heartbeats start at zero; an error if the kernel rejects a declaration or the budget is spent. -/
def replay (map : Std.HashMap Name ConstantInfo) : IO Kernel.Environment := do
  let env := (← mkEmptyEnvironment).toKernelEnv
  -- Unsafe and partial constants are left out, as leanchecker leaves them out.
  let remaining := map.fold (init := ({} : NameSet)) fun r n ci =>
    if !ci.isUnsafe && !ci.isPartial then r.insert n else r
  let work : IO Kernel.Environment := do
    let (_, s) ← (do
        Replay.replayConstant ``String.ofList
        Replay.replayConstant ``Char.ofNat
        for n in remaining do Replay.replayConstant n
        Replay.checkPostponed : Replay.M Unit).run map |>.run { env, remaining }
    return s.env
  IO.ofExcept (← IO.wait (← IO.asTask work))

/-- A name for the re-checked theorem that the environment does not hold. -/
def freshName (env : Kernel.Environment) : Name := Id.run do
  let mut n := `_vacheck_sanity
  let mut k := 0
  while (env.find? n).isSome do
    k := k + 1
    n := .num `_vacheck_sanity k
  return n

/-- The pair's re-check, the theorem `∀ x : τ, S[x/X] := fun x => p[x/X]` named `name`; none when the
theorem is not a theorem of the export, or the definition not a definition without universe
parameters. -/
def recheckOf (map : Std.HashMap Name ConstantInfo) (name : Name) (t : Target) : Option Declaration := do
  let .thmInfo thm ← map[t.thm]? | none
  let .defnInfo d ← map[t.defn]? | none
  unless d.levelParams.isEmpty do none
  -- The replay accepted the theorem, so its terms hold no free variable that x could capture.
  let x := Expr.fvar ⟨`_vacheck_x⟩
  let abstracted (e : Expr) := (e.replace fun e => if e.isConstOf d.name then some x else none).abstract #[x]
  return .thmDecl {
    name, levelParams := thm.levelParams,
    type := .forallE `x d.type (abstracted thm.type) .default,
    value := .lam `x d.type (abstracted thm.value) .default }

/-- The verdict of the kernel on a re-check, and the heartbeats it spent as `IO.getNumHeartbeats`
counts them.

It runs as a task of its own. The kernel's count of its heartbeats, which `heartbeats` bounds, is
kept per thread and set to zero only as a task starts (`run_task` in the runtime, in v4.35.0 and
v4.36.0): never on the main thread, where the replay spent many. So every re-check has the whole
budget, however many ran before it. `IO.getNumHeartbeats` counts on, through tasks and threads alike,
so the task reads it before and after. -/
def recheck (env : Kernel.Environment) (decl : Declaration) : IO (String × Nat) := do
  let opts := maxRecDepth.set (maxHeartbeats.set {} heartbeats) recDepth
  let task ← IO.asTask do
    let before ← IO.getNumHeartbeats
    let result ← IO.lazyPure fun _ => (Kernel.Environment.addDecl env opts decl).map fun _ => ()
    let spent := (← IO.getNumHeartbeats) - before
    return match result with
      | .ok () => ("any", spent)
      -- Limits, not answers: the kernel gave up.
      | .error .deterministicTimeout | .error .deepRecursion | .error .excessiveMemory
      | .error .interrupted => ("skipped", spent)
      | .error _ => ("needed", spent)
  IO.ofExcept (← IO.wait task)

/-- A message as one line of printable ASCII, at most 300 characters: each run of white space as
one space, any other character outside ASCII's printable ones as `\u{hex}`. -/
def oneLine (s : String) : String :=
  let shown := s.foldl (init := "") fun out c =>
    if c.isWhitespace then (if out.endsWith " " then out else out.push ' ')
    else if ' ' ≤ c && c ≤ '~' then out.push c
    else out ++ "\\u{" ++ String.ofList (Nat.toDigits 16 c.toNat) ++ "}"
  (shown.take 300).copy

def run (targetsFile exportFile : String) : IO Unit := do
  let lines ← IO.FS.lines targetsFile
  let mut targets := #[]
  for line in lines, n in [1:lines.size + 1] do
    match targetOf line with
    | .ok t => targets := targets.push t
    | .error _ => throw <| IO.userError s!"line {n} of the targets is not [i, j, theorem, definition]"
  let exp ← try IO.FS.withFile exportFile .read fun h => LeanExport.parseStream (.ofHandle h)
    catch e => throw <| IO.userError s!"the export cannot be read: {e}"
  if targets.isEmpty then return
  -- Only what the pairs need is replayed: the closure of their theorems and definitions. A replay
  -- that fails, or spends its heartbeats, is no verdict on any pair.
  let map := quotTargets.foldl (init := exp.constMap) (·.erase ·)
  let needed := closure map (targets.toList.flatMap (fun t => [t.thm, t.defn]) ++ [``String.ofList, ``Char.ofNat])
  let env? ← try pure (some (← replay (map.filter fun n _ => needed.contains n))) catch _ => pure none
  let name := env?.map freshName
  let mut out := ""
  let mut spent := 0  -- as IO.getNumHeartbeats counts
  for t in targets do
    let mut verdict := "skipped"
    if let (some env, some name) := (env?, name) then
      if let some decl := recheckOf exp.constMap name t then
        if spent < totalHeartbeats * 1000 then
          let (v, used) ← recheck env decl
          verdict := v
          spent := spent + used
    out := out ++ s!"{t.i} {t.j} {verdict}\n"
  IO.print out

def main (args : List String) : IO UInt32 := do
  try
    let [targetsFile, exportFile] := args | throw <| IO.userError "usage: sanity TARGETS EXPORT"
    run targetsFile exportFile
    return 0
  catch e =>
    IO.eprintln (oneLine s!"sanity: {e}")
    return 1
