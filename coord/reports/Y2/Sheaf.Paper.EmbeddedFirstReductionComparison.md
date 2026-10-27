## What changed

Replaced the sorry in `AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.firstReductionComparison`
by a localization argument on a K-flat representative. It uses ordinary balanced-tensor
comparison, preservation of K-flatness by integral scalar restriction, and invertibility
of the specified finite residue scalar map. The statement and its let-bound sheafification
instances are unchanged. No existing definition or signature was changed.

Added three narrowly scoped modules. `EmbeddedFiniteScalarIsIso` proves invertibility of
the actual constant-function map, using local bijectivity of its ring-presheaf map.
`EmbeddedIntegralRestrictionKFlat` transports the existing small-site scalar-flatness
theorem to the original site by the local equational criterion, applies flat scalar
restriction to section complexes, and transports back to native K-flatness.
`EmbeddedFirstReductionOrdinary` isolates the remaining ordinary tensor comparison.
Every new statement has a source, a full mathematical proof in its docstring, and a node.
The localization calculation is proved in a private lemma over abstract coefficient
objects, which avoids expensive unfolding of the concrete continuous coefficient
presentations. The complete parent compiled in 27.8 seconds; both proved helper
modules and the ordinary statement module also compiled.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.firstReductionComparison`
(node `lem-sfb-embedded-first-reduction-comparison`) by a complete proof from the three
more elementary statements. The added declarations `embeddedFiniteScalarIsIso` and
`embeddedIntegralRestrictionKFlat` are proved, with no holes in their modules.

Added one hole:
`AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.embeddedFirstReductionOrdinary`,
node `lem-sfb-embedded-first-reduction-ordinary`. This concerns a natural isomorphism
between ordinary module functors. It has no derived objects, resolutions, K-flatness,
right derived realization, or localization. The parent proof performs all those steps
in Lean. Thus the delivery is a decomposition (one upper hole closed, one strictly
simpler hole added), not a net hole reduction. The original item has zero holes left.
The existing imported `integralModelsEmbeddedScalarFlat` remains an assigned theorem
of its existing node; it is not a new hole of this delivery.

## No longer needed

The original file had no proof imports to remove. The parent additionally imports
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` privately for the existing
unbounded K-flat resolution theorem. It privately imports
`Sheaf.CategoryTheory.DerivedTensorRightExact` for the cochain-counit API and its
proved K-flat invertibility lemma; the corresponding node is now a proof dependency. The parent's direct dependencies
`det-prop-integral-criterion-constant-coefficients`,
`det-prop-sfb-qlbar-colimit-x-integral-limit`, and
`lem-weil-pbc-flat-common-quotient-reduction-tower` are replaced by the concrete
ordinary comparison and K-flat transport. In particular, no whole derived reduction
tower or normalized derived change-of-rings model is constructed here. The first two
still underlie the existing embedded scalar-flatness/residue-section results; no
claim of global withdrawal is made. The generic finite-discrete comparison is used
by `EmbeddedFiniteScalarIsIso` rather than imported directly by the parent.
`def-sfb-integral-model-generator-data` is retained for intrinsic realization.
No source-library declaration or module is withdrawn. The integral-models unit's
step (1), comparison of the first reductions, is preserved.

## Where the brief, the DAG or earlier work was wrong

The original proof plan combined ordinary quotient comparison with derived localization
and realization in one obligation. Its declared generic interfaces do not directly
identify all the embedded coefficient encodings. Separating the ordinary tensor step
makes the derived argument explicit and reusable without repeating the original
statement. No false statement, changed target, or definition repair was needed.

Edge cases were checked mathematically: the ordinary comparison sends zero modules
to zero modules; empty covering sieves cause no extra hypotheses; all K-flat and
localization arguments allow arbitrary integer-indexed complexes. Neither flat terms
nor boundedness are inferred from K-flatness.

## New nodes

`lem-sfb-embedded-finite-scalar-is-iso` attaches the proved specified scalar-map
isomorphism in `Sheaf.Paper.EmbeddedFiniteScalarIsIso`.

`lem-sfb-embedded-integral-restriction-kflat` attaches the proved K-flat transport
in `Sheaf.Paper.EmbeddedIntegralRestrictionKFlat`.

`lem-sfb-embedded-first-reduction-ordinary` attaches the sole remaining ordinary
balanced-tensor comparison in `Sheaf.Paper.EmbeddedFirstReductionOrdinary`.

The parent node's proof, dependencies and proof origin now follow the localization
argument. No change record is required: all existing signatures and definitions stay
unchanged, and no held module is adapted.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
