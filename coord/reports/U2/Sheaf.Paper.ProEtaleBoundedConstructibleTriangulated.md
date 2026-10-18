## What changed

Replaced the sole proof hole in
`AlgebraicGeometry.Scheme.proEtale_bounded_constructible_isTriangulated` without changing
its signature or any public import. The proof establishes the zero and isomorphism
closure conditions directly, packages canonical kernel/cokernel closure using their
universal-property isomorphisms, applies the existing proved
`CategoryTheory.cohomology_in_weak_serre_subcategory`, and identifies finite integer
homology support with the standard bounded derived property.

Private helpers prove that the specified constant coefficient map is an isomorphism,
by uniqueness of left adjoints and an explicit check of its constant-section
normalization. They specialize the existing exact module operations functor along that
map, and prove transport of local constancy and finite geometric stalks through
isomorphisms. This removes the need to construct tensor maps separately. The zero
argument uses one stratum, the identity covering and the zero module; stalk finiteness
follows from the colimit adjunction. No new definition chooses data from an unproved
existence statement. The empty scheme is covered by the same positive one-stratum
witness, and the zero coefficient ring is allowed throughout.

Added `Sheaf.Paper.ProEtaleConstructibleExactClosure` for the sheaf exactness part of
the original plan, and updated the original node's proof route. This new statement
contains no derived-category, cohomological boundedness or triangulation assertion.
The completed proof in the item performs all remaining categorical and boundedness
assembly. The original module-level openings are preserved; helper arguments use
fully qualified `Opposite.op` and proof-local zero instances.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.proEtale_bounded_constructible_isTriangulated`
(node `lem-weil-proetale-dbc-triangulated`). The item module has zero literal holes.

Added one hole:
`AlgebraicGeometry.Scheme.constructibleProEtale_exactClosure`
(node `lem-weil-proetale-constructible-exact-closure`). This is the only hole in the
delivery. It asserts preservation of global constructibility by kernels, cokernels and
short-exact middle terms. Its docstring supplies the common-stratification and
finite-type locally constant Serre argument. It still needs the small-model/constant-ring
transport of `finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions`, the
finite-model/finite-stalk comparison, and the inverse-image/refinement comparisons
listed in its node. The existing generic Serre theorem itself may be used while it
remains unproved, as the stage permits; the obstacle to applying it directly is its
different coefficient/site encoding, not its proof status.

This is a decomposition: one upper hole closed, one strictly sheaf-level hole added,
net zero literal holes. The zero/isomorphism and bounded-derived glue are proved.

Validation: `lcompile.py --all` and a final per-file check compiled the delivery without
errors or warnings (the sheaf statement in 5.2 seconds; the final item in 13.5 seconds).
A separate compile with `#print axioms` confirmed that the private coefficient-comparison,
zero-constructibility, isomorphism-constructibility and finite-support/boundedness lemmas
use only `propext`, `Classical.choice` and `Quot.sound`. The final theorem additionally has the expected
`sorryAx` dependency from the isolated exactness lemma. The diagnostic print commands
were removed.

## No longer needed

The following direct proof imports were removed:

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Mathlib.FieldTheory.IsAlgClosed.Basic`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`
- `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.Paper.ProEtaleFixedModuleLocalConstancy`
- `Sheaf.Paper.ProEtaleLocallyConstantSheaf`
- `Sheaf.RingTheory.WeaklyEtaleField`
- `WeilConjectures.ConstructibleSheaf.Refinement`

`ProEtaleOperationsCanonicalAdjunction`, `ProEtaleRingInverseImage` and
`ProEtaleFixedModuleLocalConstancy` supply interfaces that the completed categorical
proof does not use. Their direct imports have not been added to the new obligation. The finite-type local Serre theorem, stratification intersection,
weakly-etale point lifting, stalk comparisons and pullback comparisons are needed only
for the isolated sheaf exactness argument: they move to that node's proof plan and are
not claimed as pruned work. The elementary zero/stalk proof does not use the
constant-sheaf stalk theorem or weakly-etale localization. Several removed imports
remain transitively available through the unchanged public imports and are removals of
redundant direct imports, not whole-library pruning. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The direct route through the existing weak-Serre cohomology theorem is available and
proved. Its bounded clause uses `DerivedCategory.TStructure.t.bounded`, while the item
uses finite support of nonzero integer homology; these predicates are equivalent, not
definitionally equal. The equivalence is proved here using
`Set.finite_iff_bddBelow_bddAbove` and the derived `isGE_iff`/`isLE_iff` lemmas.

Several current dependency `lean` records name files absent from this read-only
checkout: `ProEtaleConstantRingMap`, `ProEtaleConstantRingOperations`,
`ProEtaleObjectInverseImageRestriction`, `ProEtaleInverseImageStalk`,
`ProEtaleModulePullbackComposition` and `ProEtalePullbackLocallyConstant` under
`Sheaf.AlgebraicGeometry`. The existing original ring-sheaf interfaces in
`ProEtaleInverseImage`, `ProEtaleOperations` and `ProEtaleLocallyConstantSheaf` are
available. Their object encodings differ from some newer recorded comparisons.
A remote compile probe of `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap` also failed
with "object file ... of module ... does not exist", confirming that this recorded
interface is unavailable in the compiled baseline. The temporary probe was removed.
The coefficient comparison itself is now proved as the private helper
`constantComparison_isIso` in the item, without the missing module: it uses the existing
constant-sheaf adjunction and sheafification interfaces. This argument can be reused for
the sheaf exactness step. I did not duplicate or alter any recorded module. The isolated
obligation retains the other original mathematical comparisons in its plan, so their
recorded interfaces can be reconciled when that argument is formalized.

The generic finite-type local Serre declaration is for a small category and a
`RingCat` constant ring sheaf. The item uses the actual pro-etale category, the
commutative-ring constant sheaf forgotten to rings, localized tensor pullbacks and
finite stalks. Applying that declaration requires the comparisons explicitly recorded
in the new node; treating these predicates as definitionally equal would be wrong.

No target or existing definition, public signature or public visibility was changed.
The unit `sk-def-sf-operations` has no realized steps imposing a different route.

## New nodes

`lem-weil-proetale-constructible-exact-closure` is the sheaf exactness portion of steps
2--7 of the original proof, with finite-ring algebra made explicit. It inherits chapter
`sec-smooth-purity` and unit `sk-def-sf-operations`, and serves the same blueprint
ancestor `def-weil-finite-torsion-constructibility`. The statement is strictly below the
item: it has no complexes or triangulation conclusion. The proof retains global finite
partitions rather than replacing them by affine-local constructibility. Its positive
number of strata survives common refinement by multiplication; empty strata, empty
schemes and zero rings require no extra assumptions. Searches found no Mathlib match;
the existing étale Serre theorem is on a different site and the discrete Noetherian
constructibility theorem uses affine-local partitions. No change records are needed.

A further scratch compile verified the following coefficient-encoding comparison in
6.3 seconds, using `Sheaf.Paper.ProEtaleConstructibleSheaf` and
`Mathlib.CategoryTheory.Sites.ConstantSheaf` (with `universe u` and
`open CategoryTheory` inside `namespace AlgebraicGeometry.Scheme`). It supplies a
ready construction for the constant-ring transport part of the remaining obligation.
The generic `constantCommuteCompose` API instead requests a
`PreservesSheafification (forget₂ CommRingCat RingCat)` instance whose synthesis timed
out. Explicit presheaf and sheaf arguments in the construction below avoid a second
unification timeout. The scratch module was removed from the delivery.

```lean
set_option backward.isDefEq.respectTransparency false in
noncomputable example (Y : Scheme.{u}) (A : Type u) [CommRing A] :
    (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A) ≅
      (constantSheaf (ProEt.topology Y) RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} A)) :=
by
  let J := ProEt.topology Y
  let B := RingCat.of (ULift.{u + 1, u} A)
  let P : Y.ProEtᵒᵖ ⥤ RingCat.{u + 1} := (Functor.const Y.ProEtᵒᵖ).obj B
  let D := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing Y A)
  let q : P ⟶ D.obj :=
    Functor.whiskerRight (toSheafify J ((Functor.const Y.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} A))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let f : (constantSheaf J RingCat.{u + 1}).obj B ⟶ D :=
    ((sheafificationAdjunction J RingCat.{u + 1}).homEquiv P D).symm q
  have fac : toSheafify J P ≫ f.hom = q :=
    ((sheafificationAdjunction J RingCat.{u + 1}).homEquiv P D).apply_symm_apply q
  have hq1 : Presheaf.IsLocallyInjective J q :=
    (proEtaleConstantRingUnit_locallyBijective Y A).1
  have hq2 : Presheaf.IsLocallySurjective J q :=
    (proEtaleConstantRingUnit_locallyBijective Y A).2
  have hf1 : Presheaf.IsLocallyInjective J f.hom := by
    apply (Presheaf.comp_isLocallyInjective_iff J (toSheafify J P) f.hom).mp
    rw [fac]
    exact hq1
  have hf2 : Presheaf.IsLocallySurjective J f.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J fac
  have : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).mp ⟨hf1, hf2⟩
  exact (asIso f).symm
```

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
