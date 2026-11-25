#!/usr/bin/env bash
# Rebuilds tests/fixtures/<case>.ndjson from the Lake projects beside them.
# Needs elan: each project pins leanprover/lean4:v4.36.0 in its lean-toolchain.
#
# `leanexport <Module>` on its own exports everything in scope, all of Init
# included: about 350 MB for a module of three lines. The names after `--`
# are the module's own declarations, so each export holds just those and
# everything they depend on.
set -euo pipefail
cd "$(dirname "$0")/fixtures"

export_case() {
  local case=$1 module=$2
  shift 2
  (
    cd "$case"
    lake build
    # A name leanexport cannot find is a panic; abort on it instead of
    # writing a partial export.
    LEAN_ABORT_ON_PANIC=1 lake env leanexport "$module" -- "$@" > "../$case.ndjson"
  )
  test -s "$case.ndjson"
}

export_case good Good Good.f Good.t1 'Good.«key never leaves»' Good.anyIn_nil Good.pick_lowest
export_case sorry Sorry Sorry.t
export_case axiom Axiom Axiom.magic Axiom.t
export_case native Native Native.t
export_case fakeeq FakeEq Eq Eq.any Eq.rec Eq.recOn FakeEq.t
export_case replaced Replaced Replaced.doubleImpl Replaced.double Replaced.double_eq
export_case weak Weak Weak.prog_safe Weak.sort_example Weak.add_zero_of_valid Weak.sort_length_self Weak.vacuous Weak.no_project Weak.arrow Weak.by_lemma
export_case printed Printed Printed.pos Printed.u2 Printed.u4 Printed.t5
export_case reach Reach Reach.safe Reach.even_two
export_case budget Budget Budget.light Budget.heavy
