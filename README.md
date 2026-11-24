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
    uses: verificationalliance/verify/.github/workflows/lean.yml@6512d67903dd322b2d3ff7b9563fb740f2518243 # workflow-6
    permissions:
      contents: read
      id-token: write
      attestations: write
```

Public repositories on github.com only. Lean 4 v4.35.0 or later, with no Lake dependencies, and
the project's `.lake` folder not committed. The jobs that check and sign stop unless the runner
says it is a standard GitHub-hosted `ubuntu-24.04` one, which a runner image made to lie could fake.

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

- **workflow-6**, `6512d67903dd322b2d3ff7b9563fb740f2518243`, with vacheck 1.1.4.

Revoked: workflow-1 (`f209d20`), workflow-2 (`4e66300`), workflow-3 (`7896c82`), workflow-4
(`7b47c83`, never used) and workflow-5 (`9ade54f`). Their tags stay as history; a result one of them signed shows as needing a
new check until the workflow runs again on the current release.

Check the parsers locally: `python3 -I tests/test_vacheck.py`

Licence: Apache-2.0.
