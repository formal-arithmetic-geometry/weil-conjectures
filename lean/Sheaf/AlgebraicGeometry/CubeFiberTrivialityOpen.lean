/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

import Sheaf.AlgebraicGeometry.PicardProductOpen
import Sheaf.AlgebraicGeometry.ProperFlatGlobalSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Extension of a trivial fibre in a product with two trivial slices

Source: Stacks Project, Tag 0BF3, applied after base change to Z.
(blueprint: lem-sc-cube-fiber-triviality-open).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

private lemma pullback_iso_unit_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (L : C.Modules)
    (e : Nonempty ((Scheme.Modules.pullback g).obj L ≅ SheafOfModules.unit _)) :
    Nonempty ((Scheme.Modules.pullback (f ≫ g)).obj L ≅ SheafOfModules.unit _) := by
  exact ⟨(Scheme.Modules.pullbackComp f g).symm.app L ≪≫
    (Scheme.Modules.pullback f).mapIso e.some ≪≫ Scheme.Modules.pullbackObjUnitIso f⟩

private noncomputable def tensorPullbackIsoPullback {A B : Scheme.{u}} (g : A ⟶ B) :
    Scheme.Modules.tensorPullback g ≅ Scheme.Modules.pullback g :=
  (Scheme.Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction g)

/-- For a line bundle with two trivial section slices, triviality on an arbitrary
residue-field fibre extends over a neighbourhood of that point.

Source: Stacks Project, Tag 0BF3 (blueprint: lem-sc-cube-fiber-triviality-open).

Proof: View the total space as (X × Z) ×_Z (Y × Z), using the canonical product
isomorphism. Both projections to Z are flat, proper and of finite presentation, by base
change from the field. Their universal structure-sheaf pushforward follows from Tag 0E0L
(or from GlobalSectionsBijective for the proper geometrically integral factors). The
points x and y give sections of these two projections. Transfer L to this pullback and
identify its two section restrictions with the stated slices, and its fibre at t with the
fibre of the last projection. The source module pullback and tensorPullback used in
picard_product_open are canonically isomorphic: both are left adjoint to module
pushforward. Apply Scheme.picard_product_open (Tag 0BF3). Its open base change is
canonically the open subscheme given by the preimage of U. Transport the resulting
trivialization through these isomorphisms. No rationality of t or connectedness of Z is
used. -/
theorem exists_mem_nonempty_pullback_iso_unit_of_cube_fiber
    {K : Type u} [Field K] (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom]
    (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (L : ((X ⊗ Y) ⊗ Z).left.Modules) [L.IsInvertible]
    (hx : Nonempty (Scheme.Modules.overPullback
      (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) L ≅ SheafOfModules.unit _))
    (hy : Nonempty (Scheme.Modules.overPullback
      (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) L ≅ SheafOfModules.unit _))
    (t : Z.left)
    (ht : Nonempty ((Scheme.Modules.pullback
      ((snd (X ⊗ Y) Z).left.fiberι t)).obj L ≅ SheafOfModules.unit _)) :
    ∃ U : Z.left.Opens, t ∈ U ∧
      Nonempty ((Scheme.Modules.pullback ((snd (X ⊗ Y) Z).left ⁻¹ᵁ U).ι).obj L ≅
        SheafOfModules.unit _) := by
  let f := (snd X Z).left
  let g := (snd Y Z).left
  have : IsProper f := inferInstanceAs (IsProper (pullback.snd X.hom Z.hom))
  have : Flat f := inferInstanceAs (Flat (pullback.snd X.hom Z.hom))
  have : LocallyOfFinitePresentation f :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X.hom Z.hom))
  have : GeometricallyIntegral f :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd X.hom Z.hom))
  have : IsProper g := inferInstanceAs (IsProper (pullback.snd Y.hom Z.hom))
  have : Flat g := inferInstanceAs (Flat (pullback.snd Y.hom Z.hom))
  have : LocallyOfFinitePresentation g :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd Y.hom Z.hom))
  have : GeometricallyIntegral g :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd Y.hom Z.hom))
  let σ := (lift (toUnit Z ≫ x) (𝟙 Z)).left
  let τ := (lift (toUnit Z ≫ y) (𝟙 Z)).left
  have hσ : σ ≫ f = 𝟙 Z.left := by
    rw [← Over.comp_left]
    simp
  have hτ : τ ≫ g = 𝟙 Z.left := by
    rw [← Over.comp_left]
    simp
  let e : ((X ⊗ Y) ⊗ Z).left ≅ pullback f g :=
    (Over.forget Z.left).mapIso (prodComparisonIso (Over.pullback Z.hom) X Y)
  let L' := (Scheme.Modules.pullback e.inv).obj L
  have hfO := isIso_structureSheafMap_of_proper_flat_geometricallyReduced_connected_fibers f
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
  have hgO := isIso_structureSheafMap_of_proper_flat_geometricallyReduced_connected_fibers g
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
  let a : (X ⊗ Z).left ⟶ pullback f g := pullback.lift (𝟙 (X ⊗ Z).left) (f ≫ τ) (by simp [hτ])
  let b : (Y ⊗ Z).left ⟶ pullback f g := pullback.lift (g ≫ σ) (𝟙 (Y ⊗ Z).left) (by simp [hσ])
  have heX : e.inv ≫ (fst (X ⊗ Y) Z).left ≫ (fst X Y).left =
      pullback.fst f g ≫ (fst X Z).left :=
    Over.prodComparisonIso_pullback_inv_left_fst_fst Z.hom X Y
  have heY : e.inv ≫ (fst (X ⊗ Y) Z).left ≫ (snd X Y).left =
      pullback.snd f g ≫ (fst Y Z).left :=
    Over.prodComparisonIso_pullback_inv_left_fst_snd' Z.hom X.hom Y.hom
  have heZ : e.inv ≫ (snd (X ⊗ Y) Z).left = pullback.snd f g ≫ g :=
    Over.prodComparisonIso_pullback_inv_left_snd' Z.hom X.hom Y.hom
  have ha : a ≫ e.inv =
      (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)).left := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simpa [a, ← Category.assoc] using congrArg (fun k ↦ a ≫ k) heX
      · simp only [Category.assoc]
        change a ≫ e.inv ≫ (fst (X ⊗ Y) Z).left ≫ (snd X Y).left =
          ((lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) ≫
            fst (X ⊗ Y) Z ≫ snd X Y).left
        rw [heY]
        simp only [a, pullback.lift_snd_assoc]
        change ((snd X Z) ≫ lift (toUnit Z ≫ y) (𝟙 Z) ≫ fst Y Z).left = _
        simp
    · simpa [a, hτ, f, Category.assoc] using congrArg (fun k ↦ a ≫ k) heZ
  have hb : b ≫ e.inv =
      (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)).left := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc]
        change b ≫ e.inv ≫ (fst (X ⊗ Y) Z).left ≫ (fst X Y).left =
          ((lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) ≫
            fst (X ⊗ Y) Z ≫ fst X Y).left
        rw [heX]
        simp only [b, pullback.lift_fst_assoc]
        change ((snd Y Z) ≫ lift (toUnit Z ≫ x) (𝟙 Z) ≫ fst X Z).left = _
        simp
      · simpa [b, ← Category.assoc] using congrArg (fun k ↦ b ≫ k) heY
    · simpa [b, g, ← Category.assoc] using congrArg (fun k ↦ b ≫ k) heZ
  have h₁ : Nonempty ((Scheme.Modules.tensorPullback a).obj L' ≅
      SheafOfModules.unit _) := by
    refine ⟨(tensorPullbackIsoPullback a).app L' ≪≫
      (Scheme.Modules.pullbackComp a e.inv).app L ≪≫
      (Scheme.Modules.pullbackCongr ha).app L ≪≫ hy.some⟩
  have h₂ : Nonempty ((Scheme.Modules.tensorPullback b).obj L' ≅
      SheafOfModules.unit _) := by
    refine ⟨(tensorPullbackIsoPullback b).app L' ≪≫
      (Scheme.Modules.pullbackComp b e.inv).app L ≪≫
      (Scheme.Modules.pullbackCongr hb).app L ≪≫ hx.some⟩
  let p := (snd (X ⊗ Y) Z).left
  let p' := pullback.fst f g ≫ f
  have hep : e.inv ≫ p = p' := by
    exact heZ.trans (pullback.condition.symm)
  let j := pullback.map p' (Z.left.fromSpecResidueField t) p
    (Z.left.fromSpecResidueField t) e.inv (𝟙 _) (𝟙 _) (by simpa using hep.symm) (by simp)
  have hj : j ≫ p.fiberι t = p'.fiberι t ≫ e.inv := by
    simp [j, Scheme.Hom.fiberι]
  have hs : Nonempty ((Scheme.Modules.tensorPullback (p'.fiberι t)).obj L' ≅
      SheafOfModules.unit _) := by
    obtain ⟨d⟩ := pullback_iso_unit_comp j (p.fiberι t) L ht
    exact ⟨(tensorPullbackIsoPullback _).app L' ≪≫
      (Scheme.Modules.pullbackComp _ e.inv).app L ≪≫
      (Scheme.Modules.pullbackCongr hj.symm).app L ≪≫ d⟩
  obtain ⟨U, htU, hU⟩ := Scheme.picard_product_open f g σ τ hσ hτ t L'
    hfO.2 hgO.2 h₁ h₂ hs
  let V := p ⁻¹ᵁ U
  have he'p : e.hom ≫ p' = p := by rw [← hep, Iso.hom_inv_id_assoc]
  let k : V.toScheme ⟶ pullback p' U.ι :=
    pullback.lift (V.ι ≫ e.hom) (p ∣_ U) (by
      rw [Category.assoc, he'p, morphismRestrict_ι])
  have hk : (k ≫ pullback.fst p' U.ι) ≫ e.inv = V.ι := by
    simp [k]
  obtain ⟨d⟩ := pullback_iso_unit_comp k (pullback.fst p' U.ι) L'
    ⟨(tensorPullbackIsoPullback _).symm.app L' ≪≫ hU.some⟩
  exact ⟨U, htU, ⟨(Scheme.Modules.pullbackCongr hk.symm).app L ≪≫
    (Scheme.Modules.pullbackComp _ e.inv).symm.app L ≪≫ d⟩⟩

end AlgebraicGeometry
