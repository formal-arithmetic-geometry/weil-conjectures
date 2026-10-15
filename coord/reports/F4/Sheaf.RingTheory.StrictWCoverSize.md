## What changed

Repaired the returned delivery's duplicate theorem declarations. The generic cardinal bounds
`PrincipalWLocalization.finset_bound` and `PrincipalWLocalization.sigma_bound` are now exported
from `Sheaf.RingTheory.PrincipalWLocalizationSize`, and
`Sheaf.RingTheory.EtaleContractionSize` imports that module and reuses those declarations. The
étale module no longer proves local copies of either statement. Its cardinality theorem and the
principal, retained, and strict-cover estimates retain their original signatures and compile
without `sorry`.

The étale node's `proof_deps` now records the principal localization size node, which supplies the
shared cardinal-bound module used by the proof. No definitions or target statements changed.

## Proved and sorry left

Closed `PrincipalWLocalization.StrictWCover.cardinalMk_le`,
`PrincipalWLocalization.cardinalMk_le`, `CommRingCat.EtaleContraction.cardinalMk_le`, and
`PrincipalWLocalization.Retained.cardinalMk_le`. No `sorry` remains in any delivered module, and
no new split-off theorem was added.

## No longer needed

The duplicate private `finset_bound` and `sigma_bound` declarations in
`Sheaf.RingTheory.EtaleContractionSize` are removed. Their proofs are shared through the public
bounds in `PrincipalWLocalizationSize`. No DAG unit step or construction module is pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery duplicated two generic cardinal lemmas in both estimate modules. The landing
checker correctly rejected the étale module because its declarations had statements identical to
`PrincipalWLocalization.finset_bound` and `PrincipalWLocalization.sigma_bound` in the principal
localization module. Promoting the existing principal-module lemmas and importing them in the
étale proof resolves the duplication while preserving the proof route and all theorem statements.

## New nodes

The existing supporting nodes `lem-weil-pbc-principal-w-localization-size`,
`lem-weil-pbc-etale-contraction-size`, and `lem-weil-pbc-retained-localization-size` remain the
declarations implemented by the delivered modules; only the étale node's proof dependency metadata
was updated to record reuse of the principal localization size module. No new node was added.

## Earlier second reading (a previous round; superseded)

Pending the independent second reading. The repaired delivery compiles all four modules and the
dry-run checks now include the shared public cardinal bounds and the updated étale dependency.

## Second reading by F4

1. **Signatures and accidental changes.** Compared the delivered item module with the repository
version. The target theorem signature and all existing declarations are unchanged; the supporting
modules are new files, and the etale dependency metadata records the module it actually imports.

2. **Proof validity.** Compiled all four delivered modules with `lcompile.py --all`. The files
contain no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or `sorryAx`. The
proofs use only the permitted cardinal arithmetic, localization, filtered-colimit, and finite-
presentation results; no definition contains postponed data.

3. **Statements and supporting declarations.** Checked the three supporting node statements
against their Lean signatures and source descriptions, including zero-ring and empty-family cases.
The cardinal bounds are true and are used at the strength required by the strict-cover proof. The
two generic finite-set and sigma bounds are proof helpers exported from the principal-localization
module; they do not alter any target statement.

4. **Pruning and imports.** The item module now imports only the three size modules needed by its
proof in addition to its public definition and cardinal arithmetic imports. The etale module reuses
the principal module's cardinal helpers, so its former duplicate declarations and their proof work
are removed. No old proof dependency or unit route is bypassed.

5. **DAG agreement and route.** The item proof follows the retained-localization, etale-contraction,
and principal-localization bounds in the stated order. The delivered node copies preserve the
original statements and source metadata; each Lean declaration and dependency now matches the proof
and its imports.

Changed after this reading: added this review record only. The code and DAG changes described above
were already present in the repaired delivery and passed local compilation.
