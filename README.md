# verify

Checks Lean 4 proofs in GitHub Actions and has GitHub sign the result, for the
[Verification Alliance](https://verificationalliance.org) checkmark.

## What the check proves

The workflow builds your Lean 4 project on a GitHub-hosted runner and re-checks every
theorem you claim with independent kernels. Only the axioms `propext`, `Quot.sound` and
`Classical.choice` are allowed, so `sorry`, `native_decide` and your own axioms fail. GitHub
then signs the result for your commit. Nothing from your repository runs on our servers.

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
    uses: verificationalliance/verify/.github/workflows/lean.yml@7b47c8301cf5c0637b3621bf6cb27b59bd06499d # workflow-4
    permissions:
      contents: read
      id-token: write
      attestations: write
```

Public repositories on github.com only. Lean 4 v4.35.0 or later, with no Lake dependencies, and
the project's `.lake` folder not committed. The jobs that check and sign run only on GitHub's
standard `ubuntu-24.04` runners, never on a larger or self-hosted one.

## Releases

Pin the workflow by its full commit SHA, as above. The current release:

- **workflow-4**, `7b47c8301cf5c0637b3621bf6cb27b59bd06499d`, with vacheck 1.1.2.

Revoked: workflow-1 (`f209d20`), workflow-2 (`4e66300`) and workflow-3 (`7896c82`). Their tags stay
as history; a result one of them signed shows as needing a new check until the workflow runs again
on the current release.

Check the parsers locally: `python3 -I tests/test_vacheck.py`

Licence: Apache-2.0.
