# verify

Checks Lean 4 proofs in GitHub Actions and has GitHub sign the result, for the
[Verification Alliance](https://verificationalliance.org) checkmark.

## What the check proves

The workflow builds your Lean 4 project on a GitHub-hosted runner and re-checks every
theorem you claim with independent kernels. Only the axioms `propext`, `Quot.sound` and
`Classical.choice` are allowed, so `sorry`, `native_decide` and your own axioms fail. GitHub
then signs the result for your commit. Nothing from your repository runs on our servers.

Each claim is also checked for signs that it says less than it reads: a statement that names none of the
project's definitions; one whose proof still holds with a definition replaced by any other; a definition that is
always true or ignores an argument; an assumption the proof never uses. These are warnings on the report, not
failures. A warning on a reviewed claim voids the review.

## Two levels

- **Design proved.** The theorems are checked. They say something about a model of your system.
- **Code proved.** Same, and a person at the Verification Alliance has read the build and
  confirmed that the proved definitions are the code that ships. Only that review awards it.

## Use it

Add `.verificationalliance.json` at the repository root:

```json
{"version": 1, "modules": ["MyLib"],
 "claims": [{"says": "Sorting keeps every element.", "theorem": "MyLib.sort_perm", "about": "model"}]}
```

Then call the workflow from `.github/workflows/verify.yml`:

```yaml
on:
  push:
    branches: [main]
permissions:
  contents: read
jobs:
  verify:
    uses: verificationalliance/verify/.github/workflows/lean.yml@d71d686908e66e2bccfda881a7c182aa45de4aae # workflow-9
    permissions:
      contents: read
      id-token: write
      attestations: write
```

Public repositories on github.com only. Lean 4 v4.35.0 or later, with no Lake dependencies, and
the project's `.lake` folder not committed. The jobs that check and sign stop unless the runner
says it is a standard GitHub-hosted `ubuntu-24.04` one, which a runner image made to lie could fake.

If your organisation or repository allows only selected actions, allow the check action
`verificationalliance/verify/.github/actions/check` as well as the workflow: its `check` job runs that
action. The export is kept 7 days, for our re-check of the signed result; a shorter artifact retention
set for your repository or organisation cuts that short, and a re-check after it ends cannot run.

## The build digest

A review that makes a claim "Code proved" holds while the build digest stays the same. The digest
covers every file in the repository at the checked commit except `.git`, wherever the project
folder is, and the manifest. So any change to any file, documentation included, needs a new review.

It is the sha256 of a JSON list, sorted by path, of one entry per file:

- `[path, "file", mode, sha256]` for a file, with its git mode: `100755` when it is executable,
  else `100644`;
- `[path, "link", target]` for a symlink, with its target as written.

A symlink must be a file symlink outside the project folder whose real path is the file its target
names inside the repository, outside `.git`. A symlink to a folder, into `.git`, outside the
repository, or to nothing is refused.

## Releases

Pin the workflow by its full commit SHA, as above. The current release:

- **workflow-9**, `d71d686908e66e2bccfda881a7c182aa45de4aae`, with vacheck 2.0.1 and result schema v2
  (`https://verificationalliance.org/attestations/proof-check/v2`, also the attestation's predicate
  type): each claim carries the sanity checks' warnings, and `sanity` says whether they all ran.
  Its check job runs the check action `.github/actions/check` of this repository, pinned at
  `cb64d5c`, and the export is kept 7 days.

Superseded, still accepted for now: workflow-7 (`ba4c212`, vacheck 1.1.4, schema v1) and workflow-6
(`6512d67`, vacheck 1.1.4, schema v1). Move to workflow-9.

Revoked: workflow-1 (`f209d20`), workflow-2 (`4e66300`), workflow-3 (`7896c82`), workflow-4
(`7b47c83`, never used), workflow-5 (`9ade54f`) and workflow-8 (`8ebc4dc`, never used). Their tags stay as history; a result one of them signed shows as needing a
new check until the workflow runs again on the current release.

Check the parsers locally: `python3 -I tests/test_vacheck.py`

Licence: Apache-2.0.
