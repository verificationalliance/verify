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
    uses: verificationalliance/verify/.github/workflows/lean.yml@<release-sha>
    permissions:
      contents: read
      id-token: write
      attestations: write
```

Public repositories on github.com only. Lean 4 v4.35.0 or later, with no Lake dependencies.

Check the parsers locally: `python3 -I tests/test_vacheck.py`

Licence: Apache-2.0.
