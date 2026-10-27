## What changed

Proved `WeilConjectures.zlReducedFrontierMixedGluing` by backward induction over the
finite frontier, using the existing localized Weil-heart sequence, immersion
filtration transport, prescribed clopen reconstruction, and the already proved
mixed-extension API. Adjunction uniqueness identifies the actual prescribed open
counit and normalized closed unit with the sequence supplied by localization.
All existing public signatures and public imports are preserved. Local
irreducibility settings prevent the elaborator from unfolding the large derived
pullback constructions while checking the compositor and its Weil-heart lift;
these settings change no construction or exported attribute.

Added `Sheaf.Paper.ZlWeilPullCompositorEquivariance`, isolating the compatibility of
`sfModelPullComposition` with `zlFrobeniusSquare`. Its documented proof transports the normalized
integral compositor and associativity to common coefficient stages and then pastes
three Frobenius squares. The categorical pasting calculation was checked in Lean,
but the integral-to-common-stage normalization remains the named theorem hole. The lift to Weil hearts is a proved private helper of the
item, using the source library's proved `IsoAlgebra.mapOfNatIsoCompIsoOfIso` and the
full heart subcategory. No arbitrary data is chosen from a mere existence statement.

Updated the item node's proof, proof dependencies and proof origin to this route.
The unit's reduction and frontier-gluing steps are retained. Empty schemes, empty
component families, a frontier of length zero, repeated filtration terms, arbitrary
real quotient weights and nonreduced ambient schemes are handled by the proof.

## Proved and sorry left

Closed upper hole: `WeilConjectures.zlReducedFrontierMixedGluing`
(`lem-zl-reduced-frontier-mixed-gluing`), the item's one original hole.
Added lower hole: `WeilConjectures.zlWeilPullCompositorEquivariance`
(`lem-zl-weil-pull-compositor-equivariance`), exactly one `sorry` in its new module.
The item module has zero holes. This is a decomposition: one upper hole closed,
one strictly separate lower hole added, net zero holes proved. Existing imported
theorem holes are unchanged and remain their own stage-3 items.

The main argument was checked in a scratch compilation in 18.4 seconds against
the new coherence statement. Its backward induction, exact sequence comparison,
filtration preservation and categorical lift are complete Lean proofs. The new
coherence theorem's categorical pasting calculation also compiled separately.
The unresolved portion is transport of the actual normalization through rational
coefficient stages. It has no mixedness, weights or frontier hypotheses, and is
not a repackaging of the item. Its source and complete proof plan are in its
docstring and node. Numerous normalization checks exposed hidden category-instance
bodies and auxiliary existence choices in the published interfaces; no category,
functor or public signature was changed to evade these comparisons.

## No longer needed

The generic `lem-zl-exact-functor-tower-filtration-splicing` /
`Sheaf.CategoryTheory.ExactFunctorTowerFiltrationSplicing` is not used: reverse
induction and `SfIsMixedOfWeightsAtMost.of_mono_cokernel` provide exactly the
bounded-mixedness conclusion needed here, without the stronger indexed
subobject/position output of that generic theorem. This does not withdraw its
module or claim it has no other users.

Removed proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual`
- `Sheaf.Paper.ConstructiblePullbackTExact`
- `Sheaf.Paper.MixedWeightsStability`
- `Sheaf.Paper.SfConstructibleHeart`
- `Sheaf.Paper.SfOpenClosedTriangleAllStages`
- `Sheaf.Paper.ZlFiniteAdicDirectImage`
- `Sheaf.Paper.ZlImmersionWeilLocalBehavior`
- `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`
- `WeilConjectures.WeilSheaf.FourierInversion.OtherSections`

Their lower-level Noetherian, finite-image, punctual, t-exactness, triangle and
local-behavior arguments are encapsulated by the three existing assembly lemmas;
no source-library declaration is removed. The original `prop-weil-operations`
attachment concerns another Weil category and cannot directly supply composition
for the actual common-stage heart; its proof import is replaced by the separately stated
normalized compositor compatibility. The underlying composition clause is retained,
not bypassed. Removed obsolete item-level tool-use entries for those encapsulated
arguments and the old operations attachment; retained the direct reduction input.

## Where the brief, the DAG or earlier work was wrong

The current DAG's four-part split is usable, but the generic tower theorem is much
stronger than the item's Lean output requires. A shorter existing extension-closure
route suffices. The planned composition input did not expose an isomorphism for
`zlWeilPull`: the adopted `prop-weil-operations` declarations use different categories.
The new compatibility theorem supplies this interface for the specified functors,
without changing their constructions or weakening any statement. The current live
item source was restored already; the old quarantine entry was not treated as a
withdrawal request, and no quarantined path was deleted.

## New nodes

`lem-zl-weil-pull-compositor-equivariance` records the composition/pasting clause
needed by actual common-stage Weil inverse images. Its statement is an equation
between the specified natural transformations. The categorical lifting helper
has a real complete proof from this equation. It is strictly separate from mixedness/gluing: it has no
filtration or frontier hypotheses or conclusions. Source: the latest
`lem-fix-weil-operations.proof.md`, pullback and composition/pasting paragraphs;
integral associativity is the existing `lem-pod-integral-pullback-composition`.
The node records LeanSearch, LeanFinder and Mathlib source searches. The source
library's categorical lifting result applies only after this equation is established.
No definition/signature change record or forced adaptation is needed.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
