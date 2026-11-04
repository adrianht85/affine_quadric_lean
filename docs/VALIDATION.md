# Reproduction and evidence

The frozen Hito10 corpus contains 54 mathematical modules, 56 Lean files
including root and Audit, 377 written theorems and 614 inventoried declarations.
These are different counts: 614 is not a theorem count or a count of every
automatically generated declaration in Lean's environment.

## Accepted execution evidence

The original Hito10 Windows execution and its isolated clean rebuild passed
on 30 October 2026. The clean run rebuilt all 56 project modules from sources
(3183 build jobs); clean PASS was 12:18:58 UTC and final verification PASS
12:18:59 UTC. Original and clean build/direct outputs each covered exactly
614 accepted names, without final errors/warnings and with only propext,
Classical.choice and Quot.sound. This was reproduction by the same executor,
not independent human review.

The two unmodified historical outputs retained in evidence/ are
hito10-original-audit.log and hito10-clean-audit.log. They are Hito10 evidence,
not the new public-tree execution. The accepted Hito10 archive SHA-256 is
d2a72fa167efa4e53bd0153b5a0ecc718d393271656e2873e0b95fa5de81ba35.
The 59-file source/configuration manifest retains SHA-256
1f9c96354e9b7333edee2e3e7f7ab6c239007e9eb39b5fdc1c2ea681d40ff430.

## New public-tree execution — PASS

A single clean build of this trimmed public tree and one new direct audit
completed successfully on 30 October 2026 at 17:38:40 UTC. Environment:
native Windows x86_64, PowerShell 7, Lean 4.24.0
(commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b),
Lake 5.0.0-src+797c613, Git 2.53.0.windows.3 and Python 3.12.14.
The nine actually installed Git revisions matched lake-manifest.json,
including Mathlib f897ebcf72cd16f89ab4577d0c826cd14afaafc7.

The initial public extraction had 74 text/source files, no .lake or inherited
.git and no project .olean/.ilean artifacts. LEAN_PATH and LEAN_SRC_PATH were
cleared. Dependency caches were permitted; project artifacts were checked
absent after acquiring those caches. Exactly 56 distinct project modules were
then recorded as Built from sources (3183 jobs). Build and direct audit each
contained precisely the 614 expected names, with no duplicates, omissions,
final warnings/errors or axioms outside propext, Classical.choice, Quot.sound.

All recorded process return codes were zero. The new direct command was:

    lake env lean -DwarningAsError=true AffineQuadric/Audit.lean

Its captured output was checked with the supplied tools/verify_public.py
--audit-log option. Source/configuration hashes were checked before caching,
after caching and after the build/audit. All 59 remain byte-identical to Hito10;
no proof, Audit.lean, toolchain, lakefile or dependency manifest was changed.
The preserved 377 proofs were not manually re-reviewed in this packaging task.

New complete output hashes:

| Private execution output | SHA-256 |
| --- | --- |
| Build | d493eccbbf3298baa16cc68dadfd61dbe64dee7cca0ddccd7522d2256f43ec27 |
| Direct audit | bf4e87523a53094938eb563c27e71b5892d23a7fd9d2636751b91e4851664c6c |

Raw new logs, process arguments/exit codes, installed revisions, initial
inventory and built-module list are retained in the separate private review
package; they are not mixed into this public source tree. The two public
historical logs are preserved as historical evidence. The public tree contains
no local machine paths or contact dossiers; public author identifiers are
recorded separately in citation metadata. The new run remains reproduction
by the same executor on the same machine, not independent human validation.

## Git bytes and local publication status

A new local Git history was created with the already configured real identity;
no private repository history was imported. With core.autocrlf=true and the
preserved .gitattributes rule "* -text", all 59 working-tree files, first-commit
blobs and a fresh local checkout kept their accepted SHA-256 values.
Final documentation-only edits and manifest refresh do not require another
Lean build; final commit and checkout hashes are recorded in the private review.

At the accepted packaging snapshot of 30 October 2026, no remote URL was
configured and no external/private remote history, ownership, visibility or
accessibility had been verified. No push, release or publication was part of
that accepted validation. These are historical statements about that snapshot.

On 4 November 2026, citation metadata and documentation were updated using
the author's confirmed repository and ORCID:

- Repository: [https://github.com/adrianht85/affine_quadric_lean](https://github.com/adrianht85/affine_quadric_lean).
- Author: [Adrián Henríquez-Tamargo](https://orcid.org/0009-0003-1452-1632).

This documentary update preserves all 59 accepted source/configuration files,
their source manifest, both historical public audit logs and the prior build
and direct-audit evidence. No new Lean compilation or axiom audit is performed
for metadata-only edits. PUBLIC_FILES_SHA256.txt is refreshed for the updated
public documents; it is separate from the frozen source manifest.

The authorized upload target must remain private during this phase. Actual
account, access, visibility, empty-target checks and upload results are recorded
in a separate private operational report, outside this source tree. This page
does not assert those network checks before their execution. The current
commit can be read with git rev-parse HEAD.

Opening is planned for 5 November 2026. This planned date is not an actual
release/publication date. Software DOI, article DOI/URL, release URL and actual
publication date remain pending; software and article DOI are separate. No
tag, release, visibility change or Zenodo deposit is created by this update.
The software MIT license does not assign a license to the article.

## Reproduce the frozen sources

With elan installed, start from a fresh checkout/extraction without .lake and
run the three README commands. Do not run lake update or change frozen files.
Dependency caches may be obtained; do not copy compiled project artifacts.
Capture the build and return code outside the tracked tree, then capture the
direct audit above and run:

    python3 tools/verify_public.py --audit-log /path/to/new-audit.log

Use python on Windows when that command selects an actual Python interpreter.
Without --audit-log, the script checks only source hashes, fixed configuration,
inventory and prohibited tokens. With it, the script requires the independent
614-name inventory exactly once, recognizes multiline axiom lists and rejects
unrecognized diagnostics or nonstandard axioms. It does not invoke Lean and
does not substitute for a kernel run. Rechecking the historical evidence is
useful but is not a new compilation.

Record the actual release commit and new evidence hashes for any later release.
Build success proves the formal statements under their hypotheses; it does not
by itself establish full correspondence with the paper or discharge its
explicit external mathematical dependencies.
