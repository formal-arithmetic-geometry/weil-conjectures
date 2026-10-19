/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Sheaf.AlgebraicGeometry.HigherDirectImageOverCoherence
import Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity
import WeilConjectures.AlgebraicGeometry.SmallEtaleAffineColimitDetection

public import Sheaf.AlgebraicGeometry.BaseChangeSourceImageCoherence

/-! # Descent of base-change source images

Source: Stacks Project Tag 09Z1 and the limit step of Tag 0F07.
(blueprint: lem-sbc-source-image-limit-descent)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X S T : Scheme.{u}} [IsAffine S]
variable (p : X ⟶ S) (g : T ⟶ S) (q : ℤ)
variable (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)


open BaseChangeSourceImageLimitDescent
variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over T)
variable [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
variable [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]

set_option backward.isDefEq.respectTransparency true in
/-- The image under base change of a source element at the limit comes from a stage.

Source: Stacks Tag 09Z1, applied to the source side in Tag 0F07 condition (2).
(blueprint: lem-sbc-source-image-limit-descent)

Proof: The maps from the qcqs stages to the affine scheme S are qcqs. The limit is qcqs
and its projections are affine. Apply higher-direct-image continuity to the sheaves
pulled back from F on the stages, and then apply the exact inverse image along p and the
geometric stalk functor at x. These two left adjoints preserve colimits; inverse image
is exact and hence commutes with degree-q homology. Thus every element of the source
stalk at the limit is the restriction of a source element at some stage. In negative
degrees both source stalks vanish, so choose any stage and its zero element. Apply the
base-change map to a representative of the given element. Compatibility of base change
with restriction, followed by naturality for the inverse-image composition isomorphism,
identifies its restriction with the base-change image at the limit. This proves the
asserted equality; no injectivity or nonzero hypothesis is needed.
-/
theorem baseChange_source_image_limit_descent (c : Cone D)
    (hc : IsLimit ((Over.forget T).mapCone c))
    (η : baseChangeSourceStalk Λ p g q F x c.pt) :
    ∃ (i : I) (ηi : baseChangeSourceStalk Λ p g q F x (D.obj i)),
      (baseChangeTargetStalkMap Λ p g q F x (c.π.app i)).hom
        ((baseChangeStalkMap Λ p g q F x (D.obj i)).hom ηi) =
          (baseChangeStalkMap Λ p g q F x c.pt).hom η := by
  classical
  let E := D ⋙ Over.forget T
  let cE := (Over.forget T).mapCone c
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (E.map f) :=
    fun f ↦ inferInstanceAs (IsAffineHom (D.map f).left)
  have : ∀ i : I, CompactSpace (E.obj i) :=
    fun i ↦ inferInstanceAs (CompactSpace (D.obj i).left)
  have : CompactSpace c.pt.left := Scheme.compactSpace_of_isLimit E cE hc
  let i₀ : I := Classical.choice (IsCofiltered.nonempty (C := I))
  have : IsAffineHom (c.π.app i₀).left := isAffineHom_π_app E cE hc i₀
  have : QuasiSeparatedSpace c.pt.left :=
    quasiSeparatedSpace_of_quasiSeparated (c.π.app i₀).left
  have : ∀ i : I, QuasiCompact ((D.obj i).hom ≫ g) := fun i ↦ inferInstance
  have : ∀ i : I, QuasiSeparated ((D.obj i).hom ≫ g) := fun i ↦ inferInstance
  have : QuasiCompact (c.pt.hom ≫ g) := inferInstance
  have : QuasiSeparated (c.pt.hom ≫ g) := inferInstance
  let t := fun {U V : Over T} (φ : U ⟶ V) ↦ higherDirectImageOverMap Λ g F q φ
  obtain ⟨hid, hcomp⟩ := higher_image_over_transition_coherence Λ g F q
  let K : Iᵒᵖ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    { obj := fun i ↦ higherDirectImage Λ ((D.obj i.unop).hom ≫ g) q
        ((((D.obj i.unop).hom)^*[ModuleCat.{u + 1} Λ]).obj F)
      map := fun f ↦ t (D.map f.unop)
      map_id := fun i ↦ by
        change t (D.map (𝟙 i.unop)) = 𝟙 _
        rw [D.map_id]
        exact hid _
      map_comp := fun f h ↦ by
        change t (D.map (h.unop ≫ f.unop)) = t (D.map f.unop) ≫ t (D.map h.unop)
        rw [D.map_comp]
        exact hcomp _ _ }
  let B : Cocone K :=
    { pt := higherDirectImage Λ (c.pt.hom ≫ g) q
        (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj F)
      ι :=
        { app := fun i ↦ t (c.π.app i.unop)
          naturality := fun i j f ↦ by
            change t (D.map f.unop) ≫ t (c.π.app j.unop) = t (c.π.app i.unop) ≫ 𝟙 _
            rw [← hcomp, c.w, Category.comp_id] } }
  have hB : Nonempty (IsColimit B) :=
    nonempty_isColimit_of_affine_etale Λ S K B (fun V ↦
      nonempty_isColimit_higher_image_affine Λ g F q D c hc K
        (fun _ ↦ Iso.refl _) (fun _ ↦ by
          simp only [K, t, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
          rfl)
        B (Iso.refl _) (fun _ ↦ by
          simp only [B, t, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
          exact (Category.comp_id _).symm) V)
  let L := (p)^*[ModuleCat.{u + 1} Λ] ⋙
    (X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have hC : IsColimit (L.mapCocone B) := isColimitOfPreserves L hB.some
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u}
      (forget (ModuleCat.{u + 1} Λ))
  let fiber := (X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)
  let ec := fiber.mapIso (sourceIso Λ p g q F c.pt)
  obtain ⟨i, y, hy⟩ := Concrete.isColimit_exists_rep (K ⋙ L) hC (ec.hom.hom η)
  let ei := fiber.mapIso (sourceIso Λ p g q F (D.obj i.unop))
  refine ⟨i.unop, ei.inv.hom y, ?_⟩
  have hs : (fiber.map ((sourceIso Λ p g q F (D.obj i.unop)).hom ≫
      ((p)^*[ModuleCat.{u + 1} Λ]).map (t (c.π.app i.unop)) ≫
      (sourceIso Λ p g q F c.pt).inv)).hom (ei.inv.hom y) = η := by
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    change (fiber.map (sourceIso Λ p g q F c.pt).inv).hom
      ((L.map (t (c.π.app i.unop))).hom (ei.hom.hom (ei.inv.hom y))) = η
    have hei : ei.hom.hom (ei.inv.hom y) = y := by
      rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
    rw [hei]
    change (L.map (t (c.π.app i.unop))).hom y = ec.hom.hom η at hy
    rw [hy]
    change ec.inv.hom (ec.hom.hom η) = η
    rw [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply]
  have hw := congrArg (fun f ↦ f.hom (ei.inv.hom y))
    (source_square Λ p g q F x (c.π.app i.unop))
  dsimp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hw
  change _ = (baseChangeStalkMap Λ p g q F x c.pt).hom
    ((fiber.map ((sourceIso Λ p g q F (D.obj i.unop)).hom ≫
      ((p)^*[ModuleCat.{u + 1} Λ]).map (t (c.π.app i.unop)) ≫
      (sourceIso Λ p g q F c.pt).inv)).hom (ei.inv.hom y)) at hw
  rw [hs] at hw
  exact hw

end AlgebraicGeometry.Etale
