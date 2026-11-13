/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulCechComparisonConstruction
import WeilConjectures.AlgebraicGeometry.KoszulOpenHomChainEvaluation

/-! # The degree-zero restriction square for the Koszul comparison

## References

* Stacks Project, Tags 08DD and 08D1.
-/

@[expose] public section

universe uMain wMain vMain
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option maxHeartbeats 800000 in
-- Transport across nested derived functors requires extra elaboration heartbeats.
/-- The stage Hom and restricted structure-Hom identifications intertwine the canonical
Koszul comparison with restriction and augmentation (Stacks, Tags 08DD, 08D1). -/
theorem koszulOpenHom_comparison_square
    (A : Type uMain) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    [HasDerivedCategory.{vMain} (ModuleCat.{uMain} A)]
    (F : CochainComplex
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    (i : DerivedCategory.Q.obj F ≅ E.obj) :
    let R := ((SheafOfModules.overFunctor.{uMain}
      (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uMain}
          ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
        (D := SheafOfModules.{uMain}
          (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory
    let H := DerivedCategory.homologyFunctor (ModuleCat.{uMain} A) 0
    let D := koszulCechHomDiagram A r f
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
    let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
    let c := koszulCechDerivedComparison A r f F ≫ G.map i.hom
    ∃ (a : ∀ e : ℕ, (koszulOpenObject A r f e ⟶ E.obj) ≃
          H.obj (DerivedCategory.Q.obj (D.obj e)))
      (b : (R.obj (koszulOpenStructure A) ⟶ R.obj E.obj) ≃ H.obj (G.obj E.obj)),
      ∀ (e : ℕ) (φ : koszulOpenObject A r f e ⟶ E.obj)
        (ψ : R.obj (koszulOpenStructure A) ⟶ R.obj E.obj),
        R.map (koszulOpenUnit A r f e) ≫ ψ = R.map φ →
        b ψ = H.map c (H.map (DerivedCategory.Q.map (colimit.ι D e)) (a e φ)) := by
  classical
  dsimp only
  let R := ((SheafOfModules.overFunctor.{uMain}
    (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)) ⋙
    Equivalence.functor
      (C := SheafOfModules.{uMain}
        ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
      (D := SheafOfModules.{uMain}
        (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory
  let H := DerivedCategory.homologyFunctor (ModuleCat.{uMain} A) 0
  let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
  obtain ⟨a₀, ha₀, hrep⟩ := koszulOpenHom_chain_representatives A r f F hF
  obtain ⟨b, hb, hchain⟩ := koszulOpenHom_chain_evaluation A r f
  let a (e : ℕ) := (Iso.homCongr (Iso.refl (koszulOpenObject A r f e)) i.symm).trans
    (a₀ e)
  refine ⟨a, b E.obj, ?_⟩
  intro e φ ψ h
  obtain ⟨t, ht⟩ := hrep e (φ ≫ i.inv)
  have ha : a e φ = koszulOpenHomStageClass A r f F e t := by
    simp only [a, Equiv.trans_apply, Iso.homCongr, Iso.refl_inv, Iso.symm_hom,
      Category.id_comp, Equiv.coe_fn_mk]
    rw [← ht, ha₀]
  let ψ₀ := ψ ≫ R.map i.inv
  have hψ₀ : R.map (koszulOpenUnit A r f e) ≫ ψ₀ =
      R.map (DerivedCategory.Q.map t) := by
    dsimp only [ψ₀]
    rw [← Category.assoc, h, ← R.map_comp, ← ht]
  have hψ : ψ₀ ≫ R.map i.hom = ψ := by
    dsimp only [ψ₀]
    rw [Category.assoc, ← R.map_comp, Iso.inv_hom_id, R.map_id, Category.comp_id]
  rw [← hψ, hb, hchain F hF e t ψ₀ hψ₀, ha, H.map_comp]
  rfl

end AlgebraicGeometry
