## What changed

Restored and proved `Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison` from its
quarantined source. The theorem's signature is preserved. The proof constructs a
normalized Ext morphism using the exact inverse image of the Zariski-to-etale site
inclusion and the coefficient adjunction. This inverse image is constructed by left
Kan extension followed by sheafification, with its explicit adjunction; the private
packaging avoids repeatedly comparing a chosen adjoint with that construction.
A finite affine cover gives common acyclic embeddings; the existing dimension-shifting theorem proves bijectivity
and uniqueness. Transport through the fixed module comparison gives the stated
module-coefficient naturality and the actual-section formula in degree zero.

Added `Sheaf.AlgebraicGeometry.QcoherentComparisonDegreeZero`, proving the fixed
comparison's degree-zero formula for all module sheaves, without geometric or
quasi-coherence assumptions. It uses the source library's proved resolution and
Ext-cocycle normalization, not a newly chosen comparison.

Migrated the canonical comparison and four unclaimed consumers from the duplicate
Sheaf resolution module to the adopted source construction and its extension.
Only a private import changes in the four consumers; all declarations and proofs
remain verbatim. The duplicate Sheaf module is held by F2 and is not delivered or
changed. The repair service restored the Frobenius pullback consumer during this
session; its one duplicate private import is removed as a forced adaptation. No adopted source-library file changes. The fixed large comparison
retains its defining resolution-isomorphism component, with a proved component
formula and coefficient naturality. Ext universe transport uses Mathlib’s
`Ext.chgUniv`, proved to represent the same derived morphism as the previous
common-derived-category transport. The additive module cohomology object uses
the equivalent forgetful functor packaging. These definition changes preserve their mathematical meaning
and reopen target semantic review as required by AGENTS.md section 4.

The final source migration compiles without errors or warnings: the complete
item in 43.5 seconds, the degree-zero module in 36.3 seconds, and the canonical
comparison in 46.6 seconds. All six import-only consumer adaptations compile.
A separate audit proves equality of the new Ext-universe transport with the
previous common-derived-category transport. The item, degree-zero formula,
large-comparison naturality and universe-transport API each use only `propext`,
`Classical.choice` and `Quot.sound`; none depends on `sorryAx`. The delivery tool’s
appended whole-environment probes for the three large files exceeded 60 seconds
on the first dry run; it records that the merge repeats them. The independent
targeted axiom audit above compiled in 1.7 seconds.

The restored pullback-square consumer needs two import edits: removing the
now-conflicting duplicate and exposing moduleCohomologyFMap, which its existing
public statement uses. Its original has a pre-existing public-visibility error,
reported separately below. No statement or proof is changed. Unchanged diagnostic
copies of its cohomology-comparison consumer and the Frobenius comparison compile
against the migrated set; those copies are not delivered. The item's theorem
signature was compared byte-for-byte with the quarantine and is unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_unique_qcoherentNormalizedComparison`
(node `lem-weil-pbc-qcoherent-normalized-comparison-exists`).

Also proved
`AlgebraicGeometry.Scheme.Modules.moduleAbelianCohomologyLarge_zero`
(node `lem-weil-pbc-qcoherent-comparison-degree-zero`) and the evaluation API
`AlgebraicGeometry.Scheme.Modules.moduleAbelianCohomologyLarge_component`,
`AlgebraicGeometry.Scheme.Modules.moduleAbelianCohomologyLarge_naturality`, and
the canonical Ext-universe transport APIs recorded in the definition node.
There are zero explicit holes left in the item, zero holes in the new degree-zero
module, and zero holes added elsewhere. The import-only consumer adaptations retain
these five pre-existing holes without changing their statements or proofs:
`AlgebraicGeometry.Scheme.Modules.CoherentEtale.exists_normalized_map`,
`AlgebraicGeometry.Scheme.Modules.coherentEtaleComparison_pullback`,
`AlgebraicGeometry.Scheme.Modules.coherentPowerComparison`,
`AlgebraicGeometry.Scheme.Modules.qcoherentNormalizedComparison_pullback_square`, and
`AlgebraicGeometry.Scheme.Modules.coherentFrobenius_pullback`.
CoherentEtaleEffacingSequence has zero holes. No unfinished result was split off.
The proof uses the declared dependencies with their existing proof status.

## No longer needed

Removed these direct proof imports from the quarantined item:

- `WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift`
- `WeilConjectures.AlgebraicGeometry.EtaleAffineTensorCechVanishing`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen`
- `WeilConjectures.AlgebraicGeometry.EtaleFiniteAffineCechBasis`
- `WeilConjectures.AlgebraicGeometry.ModuleCechBetaAffineQuasiIso`
- `WeilConjectures.AlgebraicGeometry.ModuleCechComparison`
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization`
- `Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility`
- `Sheaf.CategoryTheory.DoubleComplexTotal`
- `WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion`
- `WeilConjectures.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings`
- `WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites`
- `WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal`
- `WeilConjectures.CategoryTheory.SiteCechMathlibComparison`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality`

The direct Cech-comparison route is replaced by exact inverse image and common
effacement. These old direct proof dependencies are no longer used by this node:

- `lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings`
- `lem-weil-pbc-separated-affine-open-intersection`
- `lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites`
- `lem-sc-etale-affine-qcoherent`
- `new-etale-finite-affine-cech-basis`
- `new-etale-affine-tensor-cech-vanishing`
- `lem-weil-pbc-site-cech-mathlib-comparison`
- `lem-weil-pbc-cech-vanishing-criterion`
- `lem-weil-pbc-etale-cohomology-over-open`
- `lem-weil-pbc-acyclic-cech-edge-compatibility`
- `def-sc-module-cech-comparison`
- `lem-sc-module-cech-beta-affine-quasi-iso`
- `def-sp-double-complex-total`
- `lem-weil-pbc-effaceable-delta-functor-universal`

The new degree-zero proof uses the defining common-resolution components and
the proved Ext-cocycle/terminal-generator formulas. It does not use
`new-module-cohomology-ext-resolution-normalization` or the separate
`new-module-cohomology-ext-sections-factorization` theorem. Pruning here concerns
this node’s direct proof route; global reachability also follows other consumers.
No Lean file or DAG node is withdrawn.
The proof and the migrated live consumers no longer import the duplicate Sheaf
resolution module; its current holder retains it unchanged. The corresponding
DAG node remains used, attached to the adopted source declarations. The blueprint
unit’s own statement and realized proof route are retained.

## Where the brief, the DAG or earlier work was wrong

The item’s recorded quarantine was caused by the source and Sheaf
resolution modules defining the same public constants. The source now also has
proved normalization lemmas and the identical supplementary cache/packaging API
in its extension module. Migrating the five unclaimed consumers to the source
owner allows these results to be used together; the duplicate module held by F2
stays untouched. The archived item is restored; absence from lean/ was not
treated as withdrawal.

The DAG's direct Cech construction is unnecessary. Exact inverse image already
gives the normalized morphism and its boundary identity. The affine-cover
argument is needed for common effacements, after which the existing comparison
morphism theorem supplies isomorphisms and uniqueness. The fixed degree-zero
formula is a separate resolution calculation; naturality alone does not prove it.
No target statement, unit route or mathematical hypothesis was changed.

## Forced adaptations

Single-file counterfactual checks of both unchanged originals against the migrated
compiled dependencies produce this exact collision (4.1 and 1.8 seconds):

```text
error: import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality failed,
environment already contains
'AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.moduleComparisonEquiv'
from WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
```

`Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback` is held by A2. The repair
service restored it at 2026-10-20T21:15:58Z, after the migration began.
The original imports `Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality`
while the migrated canonical module exports the adopted source owner. It fails
with `environment already contains ...ExtEdgeResolution.moduleComparisonEquiv`;
the original quarantine entry also records that collision. The adaptation removes
only the former private import (original line 12). The canonical public import
supplies the same names from the source owner. All existing signatures, visibility,
attributes and proofs remain verbatim. The adapted file compiles in the verification
set. No unrelated change is made to this held module.

`Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare` is held by F4 and
was restored by the same service at the same time. Its original similarly imports
the duplicate Sheaf resolution module, which conflicts with the source declarations
exported by the migrated canonical module. Removing that private import is forced.
The remaining compiler diagnostic is the pre-existing line-111 visibility error:
`Unknown identifier moduleCohomologyFMap`, with the compiler requesting a public
import. The adapted file promotes its existing import to `public import` because
its unchanged public statement uses that name. These are the only two changes
(original lines 18 and 27); no declaration, signature, attribute, proof or hypothesis
changes. The two import changes are necessary for the adapted consumer to compile;
the pre-existing visibility diagnostic is disclosed rather than attributed to the
new comparison definition. The adapted file compiles in 11.4 seconds.

## New nodes

`lem-weil-pbc-qcoherent-comparison-degree-zero`: a fully proved formula for the
fixed large module comparison on the degree-zero derived unit. It is strictly
the degree-zero normalization part of the argument and introduces no hole.
The statement includes the empty scheme and zero modules and requires no
quasi-coherence. The sources are Tags 03FD, 015E and 06XR. The existing source
cocycle, acyclic-resolution naturality and terminal-evaluation nodes remain used;
this lemma combines them
with degree-zero terminal evaluation and Ext universe transport, rather than
restating any of them.

Change records:
`coord/changes/qcoherent-section-comparison-component.md` and
`coord/changes/qcoherent-fixed-comparison-packaging.md`.

## Forced adaptations

### Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback
Only imports removed (Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality), e.g. to break an import cycle; nothing else changed. CODEX verifies that the removal is needed.

### Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare
Only imports removed (Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality), e.g. to break an import cycle; nothing else changed. CODEX verifies that the removal is needed.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
