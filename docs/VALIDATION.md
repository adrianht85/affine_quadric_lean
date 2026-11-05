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

During the private upload phase of 4 November 2026, the destination was
required to remain private. Account, access, visibility, empty-target checks
and upload results are retained in a separate private operational report,
outside this source tree. Those checks describe the private upload phase,
not a public opening or software release. The current commit can be read
with git rev-parse HEAD.

The preparation of 4 November 2026 recorded 5 November as a planned opening
date. That plan did not establish an actual opening or release/publication date.

### Documentary preparation — 5 November 2026

Earlier on 5 November 2026, the authenticated account and remote main were
checked against the accepted base `a2bb89fc81adf9d0a6c6998191cf31185b6d9a4e`.
At that point the repository was private; public opening, the first software
release and software archival publication were pending. These historical
checks are separate from the earlier Lean validation. Detailed operational
records remain outside the public source tree.

In that pre-release update, only documentation and metadata were changed.
All 59 protected source/configuration hashes were checked against the accepted
manifest, and the historical evidence above was preserved. No Lean build or
axiom audit was repeated. The reviewed English [version 0.1.0 notes](RELEASE_NOTES_0.1.0.md)
then described the prepared software without establishing a release date,
tag or release commit. Those original release notes remain unchanged.

At that pre-release stage, the paper DOI `10.5281/zenodo.23956688` was reserved
in a Zenodo draft according to the author; the paper had not yet been published.
That metadata update did not verify DOI resolution or access the private draft.
The intended software-to-preprint relation was `isSupplementTo`, with `scheme: doi`
and `resource_type: publication-preprint`. The software DOI, release URL and
actual release/publication dates were then pending, and `date-released` was
not set. That update created no tag or release, changed no visibility and
performed no Zenodo publication. The software MIT license did not assign a
license to the article; the later published preprint has its own license below.

### Public repository status — 5 November 2026

The author made the repository public on 5 November 2026. Anonymous public
access, GitHub visibility and remote main were checked against the accepted
base `822ade22b4697de9ee7dcf2862e08cccf508c76d`. The private phases and their
checks above are retained as historical evidence, not as the current visibility.

At the public-opening check, the author reported enabling the GitHub–Zenodo
integration. The first software release and archive were still pending; the
paper DOI was still described as reserved, the software DOI was pending, and
`date-released` was not set. That opening-status update created no tags or
releases, performed no Zenodo publication and did not change visibility.
These are historical facts about the opening phase, before the publications below.

### Published release and archives — 5 November 2026

The repository is public. [Software 0.1.0](https://github.com/adrianht85/affine_quadric_lean/releases/tag/v0.1.0) was published at **2026-11-05T12:36:49Z**, with tag `v0.1.0` pointing to `e3efcf4e2a46da9b84e6928935d43eb6d9ec854a`. The automated Zenodo archive is [record 23979530](https://zenodo.org/records/23979530). The software version DOI is [10.5281/zenodo.23979530](https://doi.org/10.5281/zenodo.23979530); the software concept DOI is [10.5281/zenodo.23979529](https://doi.org/10.5281/zenodo.23979529). The software license is MIT.

The companion preprint was published on **2026-11-05**, in [record 23956688](https://zenodo.org/records/23956688), under **CC BY 4.0**. Its version DOI is [10.5281/zenodo.23956688](https://doi.org/10.5281/zenodo.23956688) and its concept DOI is [10.5281/zenodo.23956687](https://doi.org/10.5281/zenodo.23956687). Version and concept identifiers for the article are distinct from those for the software. The software supplements the preprint (`isSupplementTo`, `scheme: doi`, `resource_type: publication-preprint`).

The software's main citation metadata in `CITATION.cff` now identify version 0.1.0, with its version DOI and `date-released: 2026-11-05`. The title and MIT license remain those of the software. A concept DOI identifies a collection of versions; use the version DOI to cite this specific release.

The DOI for software 0.1.0 is not assigned as a top-level `doi` or `prereserve_doi` in `.zenodo.json`, and no fixed `publication_date` is set there. Its description names the published 0.1.0 identifiers as version-specific citation facts. Future software versions require their own version citation metadata and DOI; this DOI is not a reusable registration setting.

This documentation-only follow-up on `main` preserves the 59 protected files, all earlier execution evidence and the original `RELEASE_NOTES_0.1.0.md`. The release notes retain their release-time wording, which predates final DOI assignment and article publication. Their historical pending/reserved statements are not the current publication status. Neither the published tag nor the archived ZIP has been changed. No new software version, release, deposit, Lean build or axiom audit is produced by this closure.

Updating the repository's `.zenodo.json` does not edit the already published Zenodo record. Any separate proposal to correct that record's description is kept outside the public tree; no Zenodo edit is performed by this closure.

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
