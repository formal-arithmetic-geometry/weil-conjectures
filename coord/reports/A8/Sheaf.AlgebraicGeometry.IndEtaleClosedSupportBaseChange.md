## What changed

Replaced the single hole in `AlgebraicGeometry.Etale.indEtale_closedSupport_baseChange`
with a proof from three strictly smaller intermediate theorems. The two existing definitions,
the theorem signature and every public import of the item stay verbatim.

The proof computes the counit equation directly by `mateEquiv_counit`. It constructs a
morphism of the actual localization triangles with the prescribed supported first map,
identity middle map and invertible open comparison; shifted orthogonality supplies its
connecting square. Two-out-of-three and reflection by closed direct image give invertibility
of the mate. Reflection is proved on homology using ordinary full faithfulness.

Shift compatibility is proved for the specified resolution shift structures. Generic private
proofs from upstream `DerivedAdjunctionCommShift` and `RawModuleScalarCoefficientUnshifted`
are reused inside this module, since their published theorems specialize to different
coefficients. Their statements apply to every additive exact-left derived adjunction.
Finally, `mateEquiv_vcomp`, the mate whiskering law and `mateEquiv_unitors` turn the separate
ordinary closed exchange coherence into the required supported composition and identity laws.

Only the item, three new modules and their node records are changed. No consumer or shared
interface repair is needed. Remote compilation of all four modules passed without
warnings; the item took 25.7 seconds and the three new modules took 0.9, 1.4 and
5.2 seconds, all below the 60-second per-file limit. Each new module has one public theorem and one whole-proof hole,
with the source and a complete mathematical proof in its docstring. The statements cover
empty complements, arbitrary lower bounds and all allowed coefficient rings. The unit route
is unchanged.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Etale.indEtale_closedSupport_baseChange`
(node `lem-per-ind-etale-closed-support-base-change`), 1 of 1 original holes.
The item's proof and every private helper have no `sorry`.

Three holes added, each a proper step of the original argument:

- `AlgebraicGeometry.Etale.closedSupportPlus_localization`
  (`lem-per-closed-support-plus-localization`): actual D+ counit/unit localization triangles
  and closed-to-open shifted orthogonality; no base-change morphism occurs.
- `AlgebraicGeometry.Etale.indEtale_openLocalization_comparison`
  (`lem-per-ind-etale-open-localization-comparison`): ordinary open direct-image exchange,
  with its unit equation; no support right adjoint occurs.
- `AlgebraicGeometry.Etale.closedDirectImagePlus_coherence`
  (`lem-per-closed-direct-image-plus-coherence`): pasting/identity of termwise ordinary
  closed direct-image exchange, independent of support adjoints or ind-etale hypotheses.

This is a decomposition, not a net hole reduction: 1 closed, 3 added, net -2 before the
ledger computes the actual target import closure. The three steps are independently
compilable and none restates the main supported-base-change assertion.

## No longer needed

Removed proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Mathlib.CategoryTheory.Adjunction.Unique`
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `Sheaf.CategoryTheory.ExactDerivedAdjunction`
- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.SixFunctors.OpenClosed.Derived`
- `WeilConjectures.SixFunctors.BaseChange.Derived`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Sheaf.RingTheory.IndEtaleStability`
- `Mathlib.CategoryTheory.Shift.Adjunction`
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`

No public import or declaration is withdrawn. No whole module is claimed globally pruned:
most old prerequisites remain below the new localization and open-comparison nodes, and
can be needed by other consumers. Coefficient forgetting is unnecessary in the main proof,
which works directly with module-valued sheaves. The imported ordinary ind-etale theorem
may still use its coefficient-forgetting prerequisites. Ind-etale stability is unnecessary
for the composition equation because ordinary closed-exchange coherence holds for arbitrary
base changes; the required composite map is already specified in the theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. Existing ambient localization is on the
unbounded category and uses a chosen ambient right adjoint; it does not directly supply the
D+ triangle with the exact supported-kernel derivedPlus counit in this item's definition.
The first new theorem states precisely that normalization and restriction step.

The ordinary ind-etale direct-image prerequisite takes a chosen fibre product and a local
existence-of-affine-charts condition. The item takes an arbitrary Cartesian closed square
and section-ring hypotheses on every affine open. The second new theorem isolates that
transport, the complementary-open square and the unit equation, rather than pretending that
the existing prerequisite has the required signature.

The closed exchange in this item is termwise exact localization, whereas the published
ordinary derived exchange pasting theorem uses right-derived direct image. Their coincidence
and coherence require localization normalization. The third new theorem isolates this
ordinary functoriality calculation before taking support mates.

The retained ordinary qcqs prerequisite already leads to a DAG cycle in the shared
records: `lem-weil-pbc-derived-exchange-termwise` →
`lem-weil-pbc-derived-exchange-bounded-comparison` →
`lemma-weil-pbc-derived-exchange-replacement` → the termwise node. This cycle predates
this delivery; none of those nodes or their statements is changed here.

## New nodes

`lem-per-closed-support-plus-localization`, module
`Sheaf.AlgebraicGeometry.ClosedSupportPlusLocalization`, realizes original steps 2, 3 and 7.
It retains the ambient localization and derived-adjunction dependencies.

`lem-per-ind-etale-open-localization-comparison`, module
`Sheaf.AlgebraicGeometry.IndEtaleOpenLocalizationComparison`, realizes original steps 1, 6
and the open-unit part of step 8. It imports the already-stated ordinary qcqs ind-etale
base-change prerequisite.

`lem-per-closed-direct-image-plus-coherence`, module
`Sheaf.AlgebraicGeometry.ClosedDirectImagePlusCoherence`, realizes the ordinary-exchange
part of original step 10. The main proof supplies the second mate calculation.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
