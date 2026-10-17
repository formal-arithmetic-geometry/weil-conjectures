/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Auxiliary results for the derived fibre at a geometric point

General facts used to compare the derived categories of two abelian categories through an
adjunction of exact functors.

## Main definitions and results

- `CategoryTheory.Functor.mapDerivedCategoryNatTrans`: a natural transformation `τ : F ⟶ G`
  of exact functors induces a natural transformation `D(F) ⟶ D(G)`.
- `CategoryTheory.Functor.isIso_mapDerivedCategoryNatTrans_app`: `D(τ)` is an isomorphism at
  `K` if `τ` is an isomorphism at all the cohomology objects of `K`.
- `CategoryTheory.Functor.preservesFiniteLimits_of_moduleCat`,
  `CategoryTheory.Functor.preservesFiniteColimits_of_moduleCat`: every additive functor out of
  the category of vector spaces over a field is exact, short exact sequences of vector spaces
  being split.
- `CategoryTheory.Adjunction.isIso_counit_app_of_bijective`: the counit of an adjunction
  `L ⊣ R` is an isomorphism at `X` if `R` is bijective on morphisms out of `X`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

namespace Functor

section NatTrans

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- A natural transformation `τ : F ⟶ G` of exact functors between abelian categories induces
a natural transformation `D(F) ⟶ D(G)` of the functors induced on the derived categories,
given on the image of a complex by the levelwise application of `τ`. -/
noncomputable def mapDerivedCategoryNatTrans (τ : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ))
      DerivedCategory.Q)

lemma mapDerivedCategoryNatTrans_app_Q (τ : F ⟶ G) (K : CochainComplex C ℤ) :
    (mapDerivedCategoryNatTrans τ).app (DerivedCategory.Q.obj K) =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) ≫
          G.mapDerivedCategoryFactors.inv.app K :=
  Localization.liftNatTrans_app _ _ _ _ _ _ _ _

/-- The natural transformation `D(τ)` is an isomorphism at an object `K` if `τ` is an
isomorphism at all the cohomology objects `Hⁿ(K)`. -/
lemma isIso_mapDerivedCategoryNatTrans_app (τ : F ⟶ G) (K : DerivedCategory C)
    (h : ∀ n : ℤ, IsIso (τ.app ((DerivedCategory.homologyFunctor C n).obj K))) :
    IsIso ((mapDerivedCategoryNatTrans τ).app K) := by
  obtain ⟨K', ⟨e⟩⟩ : ∃ K' : CochainComplex C ℤ, Nonempty (DerivedCategory.Q.obj K' ≅ K) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  rw [← NatTrans.isIso_app_iff_of_iso _ e, mapDerivedCategoryNatTrans_app_Q]
  suffices IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K')) by infer_instance
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso, quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff]
  have : IsIso (τ.app ((K'.sc n).homology)) :=
    (NatTrans.isIso_app_iff_of_iso τ ((DerivedCategory.homologyFunctor C n).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors C n).app K')).1 (h n)
  change IsIso (ShortComplex.homologyMap ((K'.sc n).mapNatTrans τ))
  rw [ShortComplex.homologyMap_mapNatTrans]
  infer_instance

end NatTrans

section Field

variable {K : Type*} [Field K] {D : Type*} [Category D] [Abelian D]
  (F : ModuleCat K ⥤ D) [F.Additive]

/-- An additive functor out of the category of vector spaces over a field preserves finite
limits: short exact sequences of vector spaces split. -/
lemma preservesFiniteLimits_of_moduleCat : PreservesFiniteLimits F := by
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  let s := (hS.splittingOfProjective).map F
  exact ⟨s.exact, s.shortExact.mono_f⟩

/-- An additive functor out of the category of vector spaces over a field preserves finite
colimits: short exact sequences of vector spaces split. -/
lemma preservesFiniteColimits_of_moduleCat : PreservesFiniteColimits F := by
  rw [Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi]
  intro S hS
  let s := (hS.splittingOfProjective).map F
  exact ⟨s.exact, s.shortExact.epi_g⟩

end Field

end Functor

namespace Adjunction

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}

/-- The counit of an adjunction `L ⊣ R` is an isomorphism at `X` if `R` induces bijections
`(X ⟶ Y) ≃ (R X ⟶ R Y)` for all `Y`. -/
lemma isIso_counit_app_of_bijective (adj : L ⊣ R) (X : D)
    (h : ∀ Y : D, Function.Bijective (R.map : (X ⟶ Y) → (R.obj X ⟶ R.obj Y))) :
    IsIso (adj.counit.app X) := by
  obtain ⟨g, hg⟩ := (h (L.obj (R.obj X))).2 (adj.unit.app (R.obj X))
  refine ⟨g, ?_, ?_⟩
  · apply (adj.homEquiv _ _).injective
    simp [Adjunction.homEquiv_unit, hg]
  · apply (h X).1
    simp [hg]

end Adjunction

end CategoryTheory
