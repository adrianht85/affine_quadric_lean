# Reproduction and evidence

The mathematical corpus is frozen at Hito10: 54 mathematical modules, 56 Lean files including root and Audit, 377 written theorems and 614 inventoried declarations. These are distinct counts; 614 is not a count of theorems or of every automatically generated declaration in Lean's environment.

## Accepted execution evidence

On 30 October 2026 the local Windows executor completed both the original project validation and an isolated clean rebuild of Hito10. The clean run rebuilt all 56 project modules from source (3183 build jobs), with no project .olean/.ilean artifacts initially present; dependency caches were permitted. Clean PASS was 12:18:58 UTC and final verification PASS was 12:18:59 UTC. Original and clean build/direct audit outputs each covered the same 614 distinct accepted names, with no final errors or warnings and only propext, Classical.choice and Quot.sound. Source hashes and nine package revisions were preserved. This was reproduction by the same executor, not independent human review or a separate team's validation.

Unmodified saved direct-audit outputs are included in evidence/hito10-original-audit.log and evidence/hito10-clean-audit.log. They record accepted execution, not a new execution of this public packaging. The accepted archive SHA-256 is d2a72fa167efa4e53bd0153b5a0ecc718d393271656e2873e0b95fa5de81ba35. The unchanged 59-file source manifest SHA-256 is 1f9c96354e9b7333edee2e3e7f7ab6c239007e9eb39b5fdc1c2ea681d40ff430.

## This public source tree

Packaging checks confirm all 59 accepted source/configuration files byte-for-byte, 56 Lean files, the fixed package manifest, exact 614-name coverage in Audit.lean, and allowed dependencies in both saved direct audit outputs. No new theorem has been added and no proof has been edited. A fresh build of this trimmed public tree remains to be executed before its release; do not treat packaging checks as a new kernel run.

## Fresh reproduction

After installing elan, open a fresh checkout/extraction with no .lake directory and run the three README commands. Do not run lake update or change lean-toolchain, lakefile.toml or lake-manifest.json. Dependency cache download is allowed; do not copy project .olean/.ilean files into the fresh tree. Record successful process exit codes and save build output outside the tracked source tree.

For an explicit direct audit, capture the output of:

```sh
lake env lean -DwarningAsError=true AffineQuadric/Audit.lean
```

Then run the integrity/coverage check against that captured text file:

```sh
python3 tools/verify_public.py --audit-log /path/to/audit.log
```

Without --audit-log, the script only checks source hashes, inventory, fixed configuration and prohibited source tokens. With it, it also requires each of the independent 614 accepted names exactly once, recognizes multiline axiom lists and rejects all unrecognized diagnostic output or nonstandard axioms. It does not invoke Lean. The accepted inventory and Audit.lean are deliberately separate inputs; case and Unicode numeric subscripts are preserved.

For example, the retained evidence can be checked with --audit-log evidence/hito10-clean-audit.log. A fresh release validation must use its newly captured audit output instead. Recheck source hashes after compiling and record the exact release commit and evidence hashes. Build success checks proofs under their formal hypotheses; correspondence to the informal paper requires statement-fidelity review.
