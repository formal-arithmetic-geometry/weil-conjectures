/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.GeometricFiber.ProperProjectionComponents

/-!
# The proper projection formula of forgetful functors on the ambient derived categories

For a proper morphism `g : Z ⟶ Y` of separated `k₀`-schemes of finite type, the derived condensed
realization carries the canonical proper projection map of Weil complexes to the projection
morphism of `Lḡ^* ⊣ Rḡ_*`
(`AlgebraicGeometry.WeilComplex.map_rightDerivedLowerStarNativeDerivedTensorIso_hom_app`). We
rewrite this compatibility through the factorization `N = forget ⋙ Φ` of the condensed
realization (`AlgebraicGeometry.WeilComplex.forget_map_projection_eq`), in the form in which the
comparisons of forgetting the Weil structure with the direct images, pullbacks and tensor products
appear on the ambient derived categories.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Commuting a left whiskering past an invertible right whiskering and two further right
whiskerings. -/
lemma whiskerRight_whiskerLeft_inv_whiskerRight {X₁ X₂ X₃ X₄ Y₁ Y₂ : C} (a : X₁ ≅ X₂)
    (b : Y₁ ⟶ Y₂) (d : X₁ ⟶ X₃) (e : X₃ ⟶ X₄) :
    a.hom ▷ Y₁ ≫ X₂ ◁ b ≫ a.inv ▷ Y₂ ≫ d ▷ Y₂ ≫ e ▷ Y₂ = d ▷ Y₁ ≫ e ▷ Y₁ ≫ X₄ ◁ b := by
  rw [whisker_exchange_assoc, ← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight,
    Category.id_comp, whisker_exchange_assoc, whisker_exchange]

end CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))] [IsProper g]

set_option quotPrecheck false

local notation "κ_" X => Functor.mapDerivedCategoryCompIso
  (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
  (adicSheafEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor

local notation "Φ_" X => (adicSheafEquivCondensedMod l
  (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.mapDerivedCategory

local notation "U_" X => (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory

local notation "Rg" => (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor

local notation "Rḡ" => (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
  (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).rightDerivedFunctor

local notation "Lḡ" => (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
  (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).leftDerivedFunctor

local notation "gW" => (ProEtaleWeilSheaf.upperStar k₀ l g).mapDerivedCategory

local notation "β₀" => (mateEquiv (ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l g)
  (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
    (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
  (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l g).hom).natTrans

local notation "α₀" => ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l g

local notation "τ_" X => ProEtaleWeilSheaf.condensedRealizationTensor k₀ l X

local notation "⊗W_" X => ProEtaleWeilSheaf.nativeDerivedTensor k₀ l X

set_option maxHeartbeats 8000000 in
-- the derived categories of condensed modules are slow to elaborate
set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
/-- **The proper projection formula of forgetful functors, on the ambient derived categories.**
The image under `D(Φ) ∘ D(forget)` of the canonical proper projection map of Weil complexes,
followed by the inverse of the derived base change map of the condensed realization, by the
tensor comparison and by the pullback comparison, is the tensor comparison followed by the
inverse of the derived base change map and the projection morphism of `Lḡ^* ⊣ Rḡ_*`, all up to
the identifications `D(forget ⋙ Φ) ≅ D(forget) ⋙ D(Φ)`. -/
theorem forget_map_projection_eq (A : WeilComplex k₀ l Z) (T : WeilComplex k₀ l Y) :
    (Φ_ Y).map ((U_ Y).map ((((ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l
          g).rightAdjointProjectionMap (ProEtaleWeilSheaf.nativeCurriedPullTensor k₀ l g)).app
          A.obj).app T.obj)) ≫
      ((κ_ Y).inv.app ((Rg).obj ((⊗W_ Z).obj (A.obj, (gW).obj T.obj))) ≫
        (β₀).app ((⊗W_ Z).obj (A.obj, (gW).obj T.obj)) ≫
        (Rḡ).map ((κ_ Z).hom.app ((⊗W_ Z).obj (A.obj, (gW).obj T.obj)))) ≫
      (Rḡ).map ((κ_ Z).inv.app ((⊗W_ Z).obj (A.obj, (gW).obj T.obj)) ≫
        (τ_ Z).hom.app (A.obj, (gW).obj T.obj) ≫
        (κ_ Z).hom.app A.obj ▷ (ProEtaleWeilSheaf.derivedCondensedRealization k₀ l Z).obj
          ((gW).obj T.obj) ≫
        (Φ_ Z).obj ((U_ Z).obj A.obj) ◁ (κ_ Z).hom.app ((gW).obj T.obj)) ≫
      (Rḡ).map ((Φ_ Z).obj ((U_ Z).obj A.obj) ◁
        ((κ_ Z).inv.app ((gW).obj T.obj) ≫ (α₀).inv.app T.obj ≫ (Lḡ).map ((κ_ Y).hom.app T.obj))) =
    ((κ_ Y).inv.app ((⊗W_ Y).obj ((Rg).obj A.obj, T.obj)) ≫
        (τ_ Y).hom.app ((Rg).obj A.obj, T.obj) ≫
        (κ_ Y).hom.app ((Rg).obj A.obj) ▷ (ProEtaleWeilSheaf.derivedCondensedRealization k₀ l Y).obj
          T.obj ≫
        (Φ_ Y).obj ((U_ Y).obj ((Rg).obj A.obj)) ◁ (κ_ Y).hom.app T.obj) ≫
      ((κ_ Y).inv.app ((Rg).obj A.obj) ≫ (β₀).app A.obj ≫ (Rḡ).map ((κ_ Z).hom.app A.obj)) ▷
        (Φ_ Y).obj ((U_ Y).obj T.obj) ≫
      (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g
          (comp_over g (Spec (CommRingCat.of k₀))))).projectionMorphism
        ((Φ_ Z).obj ((U_ Z).obj A.obj)) ((Φ_ Y).obj ((U_ Y).obj T.obj)) := by
  have hPF := map_rightDerivedLowerStarNativeDerivedTensorIso_hom_app g A T
  simp only [rightDerivedLowerStarNativeDerivedTensorIso_hom_app, curriedTensor_obj_map,
    curriedTensor_map_app, ProEtaleWeilSheaf.condensedRealizationCurriedTensor,
    Functor.curryCompIsoOfIso', NatIso.ofComponents_hom_app, Iso.app_hom,
    Functor.curry_obj_obj_obj, rightAdjointProjectionMap_leftDerivedUpperStarTensor_app_app] at hPF
  have h1 := (κ_ Y).inv.naturality ((((ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l
    g).rightAdjointProjectionMap (ProEtaleWeilSheaf.nativeCurriedPullTensor k₀ l g)).app
    A.obj).app T.obj)
  dsimp at h1
  have c1 : (Rḡ).map ((κ_ Z).hom.app ((⊗W_ Z).obj (A.obj, (gW).obj T.obj))) ≫
      (Rḡ).map ((κ_ Z).inv.app ((⊗W_ Z).obj (A.obj, (gW).obj T.obj))) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have c2 : (Rḡ).map ((Φ_ Z).obj ((U_ Z).obj A.obj) ◁ (κ_ Z).hom.app ((gW).obj T.obj)) ≫
      (Rḡ).map ((Φ_ Z).obj ((U_ Z).obj A.obj) ◁ (κ_ Z).inv.app ((gW).obj T.obj)) = 𝟙 _ := by
    rw [← Functor.map_comp, ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id_app,
      MonoidalCategory.whiskerLeft_id, CategoryTheory.Functor.map_id]
  have c3 : (Rḡ).map ((κ_ Z).hom.app A.obj ▷
        (ProEtaleWeilSheaf.derivedCondensedRealization k₀ l Z).obj ((gW).obj T.obj)) ≫
      (Rḡ).map ((Φ_ Z).obj ((U_ Z).obj A.obj) ◁ (α₀).inv.app T.obj) =
      (Rḡ).map ((ProEtaleWeilSheaf.derivedCondensedRealization k₀ l Z).obj A.obj ◁
        (α₀).inv.app T.obj) ≫
      (Rḡ).map ((κ_ Z).hom.app A.obj ▷
        (Lḡ).obj ((ProEtaleWeilSheaf.derivedCondensedRealization k₀ l Y).obj T.obj)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (whisker_exchange _ _).symm
  have c4 := Adjunction.projectionMorphism_natural_left
    (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
    ((κ_ Z).hom.app A.obj) ((ProEtaleWeilSheaf.derivedCondensedRealization k₀ l Y).obj T.obj)
  have c5 := Adjunction.projectionMorphism_natural_right
    (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
    ((Φ_ Z).obj ((U_ Z).obj A.obj)) ((κ_ Y).hom.app T.obj)
  have c6 : (κ_ Y).hom.app ((Rg).obj A.obj) ▷
        (ProEtaleWeilSheaf.derivedCondensedRealization k₀ l Y).obj T.obj ≫
      (Φ_ Y).obj ((U_ Y).obj ((Rg).obj A.obj)) ◁ (κ_ Y).hom.app T.obj ≫
      (κ_ Y).inv.app ((Rg).obj A.obj) ▷ (Φ_ Y).obj ((U_ Y).obj T.obj) ≫
      (β₀).app A.obj ▷ (Φ_ Y).obj ((U_ Y).obj T.obj) ≫
      (Rḡ).map ((κ_ Z).hom.app A.obj) ▷ (Φ_ Y).obj ((U_ Y).obj T.obj) =
      (β₀).app A.obj ▷ (ProEtaleWeilSheaf.derivedCondensedRealization k₀ l Y).obj T.obj ≫
      (Rḡ).map ((κ_ Z).hom.app A.obj) ▷
        (ProEtaleWeilSheaf.derivedCondensedRealization k₀ l Y).obj T.obj ≫
      (Rḡ).obj ((Φ_ Z).obj ((U_ Z).obj A.obj)) ◁ (κ_ Y).hom.app T.obj := by
    exact MonoidalCategory.whiskerRight_whiskerLeft_inv_whiskerRight ((κ_ Y).app ((Rg).obj A.obj))
      ((κ_ Y).hom.app T.obj) ((β₀).app A.obj) ((Rḡ).map ((κ_ Z).hom.app A.obj))
  simp only [Functor.map_comp, Category.assoc] at hPF
  simp only [Functor.map_comp, Category.assoc, MonoidalCategory.whiskerLeft_comp,
    comp_whiskerRight]
  dsimp only [Functor.comp_obj] at h1 hPF c1 c2 c3 c4 c5 c6 ⊢
  rw [reassoc_of% h1]
  rw [reassoc_of% c1, reassoc_of% c2, reassoc_of% c3, reassoc_of% hPF, ← reassoc_of% c4, ← c5,
    reassoc_of% c6]

end AlgebraicGeometry.WeilComplex
