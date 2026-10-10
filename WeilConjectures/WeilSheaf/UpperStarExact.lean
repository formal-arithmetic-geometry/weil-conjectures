/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Triangle

/-!
# Exactness of the pullback of Weil sheaves

The pullback `φ^*` of Weil sheaves along a morphism `φ : X ⟶ Y` of `k₀`-schemes is exact, being
induced by the exact pullback of pro-étale Weil sheaves; consequently the pullback of Weil
complexes commutes with the cohomology sheaves, `𝓗ⁿ(φ^*K) ≅ φ^*𝓗ⁿK`
(`AlgebraicGeometry.WeilComplex.upperStarCompHomologySheafIso`), and with the embedding of Weil
sheaves as complexes in degree zero (`AlgebraicGeometry.WeilSheaf.toComplexCompUpperStarIso`).

## Implementation notes

The isomorphisms are assembled from isomorphisms of functors, whiskered along the inclusions
of Weil sheaves and Weil complexes into the categories of pro-étale Weil sheaves and their
derived category. Stated objectwise, the comparison of `𝓗ⁿ(φ^*K)` with the corresponding object
of the derived category sends the kernel into a deterministic timeout.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

/-- The cohomology sheaves of Weil complexes are the cohomology objects in the derived
category of pro-étale Weil sheaves. -/
noncomputable def WeilComplex.homologySheafCompιIso (n : ℤ) :
    WeilComplex.homologySheaf (k₀ := k₀) (l := l) (X := X) n ⋙
        (WeilSheaf.objectProperty k₀ l X).ι ≅
      (WeilComplex.objectProperty k₀ l X).ι ⋙ DerivedCategory.homologyFunctor _ n := by
  unfold WeilComplex.homologySheaf
  exact ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _

/-- A Weil sheaf placed in degree zero is the corresponding object of the derived category of
pro-étale Weil sheaves. -/
noncomputable def WeilSheaf.toComplexCompιIso :
    WeilSheaf.toComplex (k₀ := k₀) (l := l) (X := X) ⋙ (WeilComplex.objectProperty k₀ l X).ι ≅
      (WeilSheaf.objectProperty k₀ l X).ι ⋙ DerivedCategory.singleFunctor _ 0 := by
  unfold WeilSheaf.toComplex
  exact ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _

variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- The pullback of Weil sheaves is the pullback of pro-étale Weil sheaves. -/
noncomputable def WeilSheaf.upperStarCompιIso :
    WeilSheaf.upperStar (k₀ := k₀) (l := l) φ ⋙ (WeilSheaf.objectProperty k₀ l X).ι ≅
      (WeilSheaf.objectProperty k₀ l Y).ι ⋙ ProEtaleWeilSheaf.upperStar k₀ l φ := by
  unfold WeilSheaf.upperStar
  exact ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _

/-- The pullback of Weil complexes is induced by the pullback of pro-étale Weil sheaves. -/
noncomputable def WeilComplex.upperStarCompιIso :
    WeilComplex.upperStar (k₀ := k₀) (l := l) φ ⋙ (WeilComplex.objectProperty k₀ l X).ι ≅
      (WeilComplex.objectProperty k₀ l Y).ι ⋙
        (ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategory := by
  unfold WeilComplex.upperStar
  exact ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _

/-- The cohomology sheaves of the pullback of a Weil complex are the pullbacks of its cohomology
sheaves: `𝓗ⁿ(φ^*K) ≅ φ^*𝓗ⁿK`, the pullback of pro-étale Weil sheaves being exact. -/
noncomputable def WeilComplex.upperStarCompHomologySheafIso (n : ℤ) :
    WeilComplex.upperStar φ ⋙ WeilComplex.homologySheaf n ≅
      WeilComplex.homologySheaf n ⋙ WeilSheaf.upperStar (k₀ := k₀) (l := l) φ :=
  ((WeilSheaf.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (homologySheafCompιIso n) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (upperStarCompιIso φ) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
        (Functor.mapDerivedCategoryHomologyFunctorIso
          (ProEtaleWeilSheaf.upperStar k₀ l φ) n).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (homologySheafCompιIso n).symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (WeilSheaf.upperStarCompιIso φ).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The pullback of a Weil sheaf placed in degree zero is the pullback of the Weil sheaf placed
in degree zero. -/
noncomputable def WeilSheaf.toComplexCompUpperStarIso :
    WeilSheaf.toComplex ⋙ WeilComplex.upperStar φ ≅
      WeilSheaf.upperStar (k₀ := k₀) (l := l) φ ⋙ WeilSheaf.toComplex :=
  ((WeilComplex.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (WeilComplex.upperStarCompιIso φ) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight toComplexCompιIso _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
        ((ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategorySingleFunctor 0) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (upperStarCompιIso φ).symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ toComplexCompιIso.symm ≪≫
      (Functor.associator _ _ _).symm)

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

instance : PreservesFiniteLimits (WeilSheaf.upperStar (k₀ := k₀) (l := l) φ) := by
  have : PreservesFiniteLimits (WeilSheaf.upperStar (k₀ := k₀) (l := l) φ ⋙
      (WeilSheaf.objectProperty k₀ l X).ι) :=
    preservesFiniteLimits_of_natIso (WeilSheaf.upperStarCompιIso φ).symm
  have : ReflectsFiniteLimits (WeilSheaf.objectProperty k₀ l X).ι := ⟨fun _ _ _ ↦ inferInstance⟩
  exact preservesFiniteLimits_of_reflects_of_preserves _ (WeilSheaf.objectProperty k₀ l X).ι

instance : PreservesFiniteColimits (WeilSheaf.upperStar (k₀ := k₀) (l := l) φ) := by
  have : PreservesFiniteColimits (WeilSheaf.upperStar (k₀ := k₀) (l := l) φ ⋙
      (WeilSheaf.objectProperty k₀ l X).ι) :=
    preservesFiniteColimits_of_natIso (WeilSheaf.upperStarCompιIso φ).symm
  have : ReflectsFiniteColimits (WeilSheaf.objectProperty k₀ l X).ι := {}
  exact preservesFiniteColimits_of_reflects_of_preserves _ (WeilSheaf.objectProperty k₀ l X).ι

end AlgebraicGeometry
