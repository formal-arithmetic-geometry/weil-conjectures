/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FlatCohomologyDerivedTensor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # The coefficient map for a free line

Source: Step 9 of `lem-pod-condensed-point-sections-transport`: reduce a trivial
line to the unit, where the cycle map is the right unitor. No boundedness or
flatness assumption on the first complex is needed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u w
open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem coefficient_map_unit_isIso
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DerivedCategory (ModuleCat.{u} R)) (q : ℤ) :
    IsIso (Etale.canonicalCoefficientMap R K (ModuleCat.of R R) q) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) q
  let e := DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} R)
  let t := H.map (K ◁ e.hom ≫ (ρ_ K).hom)
  have ha (a : R) :
      Etale.coefficientAction R K (ModuleCat.of R R) q a ≫ t = a • 𝟙 (H.obj K) := by
    have hs : ModuleCat.ofHom (LinearMap.toSpanSingleton R R a) =
        a • 𝟙 (ModuleCat.of R R) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      simp [LinearMap.toSpanSingleton_apply, mul_comm]
    dsimp [Etale.coefficientAction, t]
    rw [hs]
    have hi : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (𝟙 (ModuleCat.of R R)) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
    simp only [Functor.map_smul, hi]
    simp only [MonoidalLinear.whiskerLeft_smul, Functor.map_smul,
      Linear.smul_comp, Linear.comp_smul]
    congr 1
    change H.map ((ρ_ K).inv ≫ K ◁ (e.inv ≫ 𝟙 _)) ≫
      H.map (K ◁ e.hom ≫ (ρ_ K).hom) = 𝟙 _
    simp only [Category.comp_id, ← H.map_comp]
    rw [Category.assoc, ← whiskerLeft_comp_assoc, Iso.inv_hom_id,
      whiskerLeft_id, Category.id_comp, Iso.inv_hom_id, H.map_id]
  have hb : Etale.canonicalCoefficientMap R K (ModuleCat.of R R) q ≫ t =
      (ρ_ (H.obj K)).hom := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x a
    change t.hom ((Etale.canonicalCoefficientMap R K (ModuleCat.of R R) q).hom
        (x ⊗ₜ[R] a)) = _
    rw [Etale.canonicalCoefficientMap_unit_normalization]
    have h := congrArg (fun f ↦ f.hom x) (ha a)
    change _ = a • x
    change t.hom ((Etale.coefficientAction R K (ModuleCat.of R R) q a).hom x) = a • x
      at h
    exact h
  have : IsIso (Etale.canonicalCoefficientMap R K (ModuleCat.of R R) q ≫ t) := by
    rw [hb]
    infer_instance
  exact IsIso.of_isIso_comp_right _ t

/-- The cycle-level coefficient comparison is invertible for a module isomorphic
to the scalar line, for every unbounded complex and every integer degree.
Source: blueprint `sk-thm-frobenius`, elimination of the twist, and Step 9 of the
point-section transport argument.
Proof: for the scalar module the pure tensor formula, followed by the derived
right unitor, is the ordinary right unitor on cohomology. Both unitors are
invertible. Naturality in the coefficient module transports this result along
the specified line isomorphism.
(blueprint: lem-pod-point-line-coefficient-map) -/
theorem line_coefficient_map_isIso
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DerivedCategory (ModuleCat.{u} R)) (M : ModuleCat.{u} R)
    (hM : M ≅ ModuleCat.of R R) (q : ℤ) :
    IsIso (Etale.canonicalCoefficientMap R K M q) := by
  have := coefficient_map_unit_isIso R K q
  have hn := Etale.canonicalCoefficientMap_natural_M R K M (ModuleCat.of R R) q hM.hom
  let t := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map
    (((curriedTensor (DerivedCategory (ModuleCat.{u} R))).obj K).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map hM.hom))
  have : IsIso (Etale.canonicalCoefficientMap R K M q ≫ t) := by
    dsimp only [t]
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ t

end AlgebraicGeometry.ProEtale.CondensedRing
