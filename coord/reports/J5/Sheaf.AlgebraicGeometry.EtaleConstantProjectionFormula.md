## What changed

Proved `AlgebraicGeometry.Etale.isIso_constantDerivedProjectionMap_of_finite_torsion_cd`
in `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula`, with its original signature.
The proof transfers the torsion cohomological bound to module sheaves, applies the proved
source coproduct theorem, constructs the canonical projection mate's shifts and unit
comparison on common K-flat models, and applies derived-module free generation.
All argument helpers are private and completely proved in the assigned module.
The unit route remains the Stacks 0F12/09PB route; the unit has no numbered realized steps.

Repaired `Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap` to prevent the kernel from
expanding `leftDerivedTensorComparison` into its localization construction during concrete
specialization. `Functor.cachedDerivedTensorComparison` is a `@[no_expose]` interface whose
body is exactly that existing comparison. The proved equation
`Functor.cachedDerivedTensorComparison_eq` identifies it with the original construction.
`constantDerivedProjectionMap` uses that interface; its signature and canonical morphism
are unchanged. The existing construction node is updated to include this interface and
its equation. The record is
`coord/changes/constant-projection-comparison-interface-J5.md`.
No declaration in the adopted source library or target statement is changed.

The old attempt's Aux and Apply files were temporary compiler experiments. All their
retained work is consolidated into the assigned module; neither is delivered. No new
Lean module is introduced. Proof imports are private. The three retained public imports
have the same transitive public-import closure as the original ten public imports.

The complete assigned module compiled cleanly in one server invocation, including
axiom probes, in 45.9 seconds (without probes, 34.7 seconds). The map module compiled in
4.3 seconds. The unchanged direct consumers
`Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormulaBoundedBelow` (M5) and
`Sheaf.SixFunctors.FiniteMappingAdjunction` compiled cleanly against the repair in 13.6
and 25.4 seconds. Neither needs an adaptation or is included in this packet.

## Proved and sorry left

Closed 1 original hole:

- `AlgebraicGeometry.Etale.isIso_constantDerivedProjectionMap_of_finite_torsion_cd`
  (`lem-kun-0f12`).

Added 0 holes; split off 0 statements. Both delivered modules contain 0 remaining
`sorry`s. All private helpers and the new comparison equation are proved. This is a
proof, not a decomposition. `#print axioms` on the assigned theorem, the compact
comparison definition, and its equation reports exactly `propext`, `Classical.choice`,
and `Quot.sound`; in particular, the theorem has no transitive `sorryAx` dependency.
No data is chosen from an unproved existence theorem.

## No longer needed

Removed direct imports:

- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.Additive`
- `Mathlib.CategoryTheory.Sites.GlobalSections`
- `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`
- `Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex`
- `WeilConjectures.CategoryTheory.DerivedModuleDirectSums`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorDirectSums`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

Removed from the item's direct proof-dependency route:

- `def-weil-pbc-global-sections-functor`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-cohomology-filtered-colimit`
- `lem-pur-kinjective-degreewise-existence`
- `lem-kun-grothendieck-derived-coproducts`
- `lem-kun-finite-cd-acyclic-complex`
- `lem-pc-derived-module-direct-sums`
- `def-kun-constant-sheaf`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `lem-pc-sites-module-sheafification-interface`
- `lem-pc-kflat-resolution`
- `def-pc-kflat-complex`
- `def-pc-flat-sheaf-modules`
- `def-pc-tensor-complex-sheaves`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-kun-derived-tensor-direct-sums`

The source 0F11 coproduct theorem already contains the filtered-colimit, acyclic-complex,
and resolution work. The canonical abstract derived adjunction and comparison supply
exactness, shifts, and the unit directly. Monoidal closedness supplies tensor coproduct
preservation, and Mathlib's general colimit lemma propagates invertibility to a coproduct.
Thus the separate ringed-site comparison and coefficient-independent K-flat descent
modules are not direct proof inputs here. Some foundational results remain transitive
source dependencies; this delivery does not withdraw any source declarations or modules.

Removed obsolete top-level tool approvals, preserving the order of the remaining ones:

- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-cohomology-filtered-colimit`
- `lem-pur-kinjective-degreewise-existence`
- `lem-pc-derived-module-direct-sums`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `lem-pc-kflat-resolution`
- `lem-weil-pbc-site-derived-tensor-descent`

No module is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

The previous worker's 60-second timeout was reproducible. It occurred in kernel checking
of the concrete comparison: the kernel expanded the transparent
`leftDerivedTensorComparison` through derived bifunctors and localization data. Keeping
its identical body behind a compact interface, with a proved characterization equation,
resolves it. The proof also keeps the coefficient category abstract until the generation
step and selects the braiding inherited from the symmetric structure when applying the
rank-one module generator, agreeing with the map's existing normalization.

The planned mathematics is valid. The source 0F11 coproduct theorem already proves the
filtered-colimit, finite-cohomological-dimension, and acyclic-complex work. The source
shift and adjunction APIs supply the exactness and unit argument without a separate
ringed-site presentation. The DAG now describes this implemented route.
No statement was weakened or disputed. The argument covers the zero ring and empty
scheme: it only uses the positive annihilator and the given cohomological bound.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
