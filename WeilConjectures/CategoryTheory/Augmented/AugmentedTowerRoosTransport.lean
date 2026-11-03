/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralTensorPullbackData

import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Transport of strict augmented towers through the Roos construction

Source: Stacks Tag 08TC and the scalar-restriction paragraph of
`det-lem-int-tensor-pullback.proof.md`.
(blueprint: lem-sfb-augmented-tower-roos-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b c d
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
open CochainComplex CochainComplex.HomComplex WeilConjectures
section ProductRoos
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  {B : Type c} [Category.{d} B] [Abelian B] [HasCountableProducts B]
private def coconeCoordinates {K L : CochainComplex A ℤ} (φ : K ⟶ L) (i : ℤ) :
    (mappingCocone φ).X i ≅ K.X i ⊞ L.X (i - 1) where
  hom := biprod.lift ((mappingCocone.fst φ).f i)
    ((mappingCocone.snd φ).v i (i - 1) (by omega))
  inv := biprod.desc ((mappingCocone.inl φ).v i i (by omega))
    ((mappingCocone.inr φ).1.v (i - 1) i (by omega))
  hom_inv_id := by simpa using mappingCocone.id_X φ i (i - 1) (by omega)
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

private theorem productRoosIsIso (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) : IsIso (scalarRoosMap F C) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let pc : G.obj (∏ᶜ fun n : ℕ ↦ C.obj (op n)) ⟶
      ∏ᶜ fun n : ℕ ↦ G.obj (C.obj (op n)) :=
    piComparison G (fun n : ℕ ↦ C.obj (op n))
  have hpc : IsIso pc := by dsimp only [pc]; infer_instance
  obtain ⟨hf, hs⟩ := scalarRoosCoordinates F C
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have hpcf (i : ℤ) : IsIso (pc.f i) := inferInstance
  have hi (i : ℤ) : IsIso ((scalarRoosMap F C).f i) := by
    let eY := coconeCoordinates (scalarRoosBoundary C) i
    let eX := coconeCoordinates (scalarRoosBoundary (C ⋙ G)) i
    have he : F.map eY.hom ≫
        (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom =
        biprod.lift (F.map ((mappingCocone.fst (scalarRoosBoundary C)).f i))
          (F.map ((mappingCocone.snd (scalarRoosBoundary C)).v
            i (i - 1) (by omega))) :=
      biprod.map_lift_mapBiprod F _ _ _ _
    have hm : (scalarRoosMap F C).f i ≫ eX.hom =
        F.map eY.hom ≫ (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
            ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom ≫
          biprod.map (pc.f i) (pc.f (i - 1)) := by
      rw [← Category.assoc, he]
      apply biprod.hom_ext
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
        exact congrArg (fun f ↦ f.f i) hf
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc]
        exact hs i
    have : IsIso ((scalarRoosMap F C).f i ≫ eX.hom) := by
      rw [hm]
      change IsIso (((F.mapIso eY) ≪≫
        F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1)) ≪≫
        biprod.mapIso (asIso (pc.f i)) (asIso (pc.f (i - 1)))).hom)
      infer_instance
    exact IsIso.of_isIso_comp_right _ eX.hom
  exact HomologicalComplex.Hom.isIso_of_components _

/-- An additive functor preserving countable products transports an isomorphism
of augmented strict towers to an isomorphism of their augmented Roos complexes.
Only the specified source comparison and the component augmentation squares enter.

Source: Stacks Tag 08TC; blueprint `det-lem-int-tensor-pullback.proof.md`,
comparison paragraph, restriction commutes with R lim.
(blueprint: lem-sfb-augmented-tower-roos-transport).

Proof: write G for the functor on complexes induced by F. The canonical comparison
G(product T_n) to product G(T_n) is invertible, since products of complexes are
computed degreewise and F preserves countable products. Follow it by the product
of the components of e. Naturality of e and the defining equations of the product
comparison show, after every product projection, that this isomorphism conjugates
G(1 minus shift) to 1 minus shift for U. Additivity of F identifies its image of
the mapping cocone with the mapping cocone of the image map: its degree i is the
biproduct of the product terms in degrees i and i-1, with the usual shifted-cone
signs. The diagonal map on these two terms therefore gives a chain isomorphism r.
For its composite with the image of the strict augmentation, the first coordinate
is the product of G(gamma_n) followed by e_n, which by h is the product of a delta_n.
The second coordinate is zero because both the original augmentation and its image
have zero homotopy coordinate. The same are the two coordinates of a followed by
the target augmentation. The two cocone coordinates jointly determine a map in
each degree, proving the asserted equality. No boundedness, completeness, exactness
beyond additivity, or nonzero-object assumption is used. -/
theorem augmentedTowerRoosTransport
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type c} [Category.{d} B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ)
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (U : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (γ : (Functor.const ℕᵒᵖ).obj P ⟶ T)
    (δ : (Functor.const ℕᵒᵖ).obj Q ⟶ U)
    (a : (F.mapHomologicalComplex (.up ℤ)).obj P ≅ Q)
    (e : T ⋙ F.mapHomologicalComplex (.up ℤ) ≅ U)
    (h : ∀ n : ℕ, (F.mapHomologicalComplex (.up ℤ)).map (γ.app (op n)) ≫
        e.hom.app (op n) = a.hom ≫ δ.app (op n)) :
    ∃ r : (F.mapHomologicalComplex (.up ℤ)).obj
          (WeilConjectures.integralOperationsRoos T) ≅
        WeilConjectures.integralOperationsRoos U,
      (F.mapHomologicalComplex (.up ℤ)).map
          (AlgebraicGeometry.ProEtale.IntegralTensorPullback.augmentation P T γ) ≫ r.hom =
        a.hom ≫ AlgebraicGeometry.ProEtale.IntegralTensorPullback.augmentation Q U δ := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let := productRoosIsIso F T
  let r := asIso (WeilConjectures.scalarRoosMap F T) ≪≫
    WeilConjectures.integralOperationsRoosFunctor.mapIso e
  refine ⟨r, ?_⟩
  let α := AlgebraicGeometry.ProEtale.IntegralTensorPullback.augmentation P T γ
  let β := AlgebraicGeometry.ProEtale.IntegralTensorPullback.augmentation Q U δ
  have hα : α ≫ CochainComplex.mappingCocone.fst
      (WeilConjectures.scalarRoosBoundary T) = Pi.lift (fun n ↦ γ.app (op n)) := by
    simp only [α, AlgebraicGeometry.ProEtale.IntegralTensorPullback.augmentation,
      WeilConjectures.scalarRoosBoundary, CochainComplex.mappingCocone.lift_fst]
  have hβ : β ≫ CochainComplex.mappingCocone.fst
      (WeilConjectures.scalarRoosBoundary U) = Pi.lift (fun n ↦ δ.app (op n)) := by
    simp only [β, AlgebraicGeometry.ProEtale.IntegralTensorPullback.augmentation,
      WeilConjectures.scalarRoosBoundary, CochainComplex.mappingCocone.lift_fst]
  have hf : G.map α ≫ r.hom ≫
      CochainComplex.mappingCocone.fst (WeilConjectures.scalarRoosBoundary U) =
      a.hom ≫ β ≫
        CochainComplex.mappingCocone.fst (WeilConjectures.scalarRoosBoundary U) := by
    dsimp only [r, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
      WeilConjectures.integralOperationsRoosFunctor]
    simp only [Category.assoc]
    rw [(WeilConjectures.scalarRoosTowerCoordinates e.hom).1]
    rw [← Category.assoc (WeilConjectures.scalarRoosMap F T),
      (WeilConjectures.scalarRoosCoordinates F T).1]
    change G.map α ≫ (G.map _ ≫ _) ≫ _ = _
    rw [← Category.assoc (G.map α), ← G.map_comp_assoc]
    rw [hα, hβ]
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Limits.Pi.map_π]
    change G.map (Pi.lift (fun n ↦ γ.app (op n))) ≫
      (piComparison G (fun n ↦ T.obj (op n))) ≫
        Pi.π (fun n ↦ G.obj (T.obj (op n))) n ≫ e.hom.app (op n) = _
    rw [piComparison_comp_π_assoc, ← G.map_comp_assoc, Pi.lift_π, Pi.lift_π]
    exact h n
  have hs (i : ℤ) : (G.map α ≫ r.hom).f i ≫
      (CochainComplex.mappingCocone.snd (WeilConjectures.scalarRoosBoundary U)).v
        i (i - 1) (by omega) =
      (a.hom ≫ β).f i ≫
        (CochainComplex.mappingCocone.snd (WeilConjectures.scalarRoosBoundary U)).v
          i (i - 1) (by omega) := by
    dsimp only [r, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
      WeilConjectures.integralOperationsRoosFunctor]
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [(WeilConjectures.scalarRoosTowerCoordinates e.hom).2 i (i - 1) (by omega),
      ← Category.assoc ((WeilConjectures.scalarRoosMap F T).f i),
      (WeilConjectures.scalarRoosCoordinates F T).2 i]
    simp only [G, Functor.mapHomologicalComplex_map_f, ← Category.assoc,
      ← F.map_comp]
    dsimp only [α, β,
      AlgebraicGeometry.ProEtale.IntegralTensorPullback.augmentation]
    simp only [Category.assoc, CochainComplex.mappingCocone.lift_f_snd_v,
      CochainComplex.HomComplex.Cochain.zero_v, Functor.map_zero,
      zero_comp, comp_zero]
  apply HomologicalComplex.hom_ext
  intro i
  have hfi : (G.map α ≫ r.hom).f i ≫
      (CochainComplex.mappingCocone.fst (WeilConjectures.scalarRoosBoundary U)).f i =
      (a.hom ≫ β).f i ≫
        (CochainComplex.mappingCocone.fst (WeilConjectures.scalarRoosBoundary U)).f i := by
    simpa only [HomologicalComplex.comp_f, Category.assoc] using
      congrArg (fun z ↦ z.f i) hf
  have hid := CochainComplex.mappingCocone.id_X
    (WeilConjectures.scalarRoosBoundary U) i (i - 1) (by omega)
  have hleft := congrArg (fun z ↦ (G.map α ≫ r.hom).f i ≫ z) hid
  have hright := congrArg (fun z ↦ (a.hom ≫ β).f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc] at hleft hright
  rw [hfi, hs i] at hleft
  exact (Category.comp_id _).symm.trans
    ((hleft.symm.trans hright).trans (Category.comp_id _))

end ProductRoos
attribute [local implicit_reducible] WeilConjectures.integralOperationsRoos
  WeilConjectures.integralOperationsRoosFunctor CochainComplex.mappingCocone
  Functor.mapHomologicalComplex

set_option maxHeartbeats 2000000 in
-- The canonical comparisons involve several chosen product and cocone models.

end CategoryTheory
