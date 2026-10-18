/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.CategoryTheory.RingedSectionLocalization
public import Sheaf.CategoryTheory.RingedSiteLocalization
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Sequential presentation of coefficient localization

Source: Stacks Project, algebraization.tex, Tag 0997.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R] (f : R)

private def mult : ModuleCat.of R R ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom (LinearMap.mul R R f)

private abbrev seq : ℕ ⥤ ModuleCat.{u} R :=
  Functor.ofSequence (X := fun _ : ℕ => ModuleCat.of R R) (fun _ => mult R f)

private def leg (n : ℕ) : ModuleCat.of R R ⟶ ModuleCat.of R (Localization.Away f) :=
  ModuleCat.ofHom ((LinearMap.id : R →ₗ[R] R).smulRight
    ((IsLocalization.Away.invSelf f : Localization.Away f) ^ n))

private def coc : Cocone (seq R f) where
  pt := ModuleCat.of R (Localization.Away f)
  ι := NatTrans.ofSequence (leg R f) (by
    intro n
    simp only [seq, Functor.ofSequence_map_homOfLE_succ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    dsimp [seq, Functor.ofSequence] at x ⊢
    change (f * x) • (IsLocalization.Away.invSelf f : Localization.Away f) ^ (n + 1) =
      x • (IsLocalization.Away.invSelf f : Localization.Away f) ^ n
    simp only [Algebra.smul_def, map_mul, pow_succ]
    calc
      _ = algebraMap R (Localization.Away f) x *
          (IsLocalization.Away.invSelf f : Localization.Away f) ^ n *
          (algebraMap R (Localization.Away f) f * IsLocalization.Away.invSelf f) := by ring
      _ = _ := by rw [IsLocalization.Away.mul_invSelf, mul_one])

private theorem seq_map (n k : ℕ) (x : R) :
    (seq R f).map (homOfLE (Nat.le_add_right n k)) x = f ^ k * x := by
  induction k with
  | zero => simp [seq]
  | succ k hk =>
    rw [show homOfLE (Nat.le_add_right n (k + 1)) =
      homOfLE (Nat.le_add_right n k) ≫ homOfLE (Nat.le_add_right (n + k) 1) by rfl]
    rw [Functor.map_comp]
    simp only [seq, Functor.ofSequence_map_homOfLE_succ, ModuleCat.comp_apply]
    rw [show (Functor.ofSequence (X := fun _ : ℕ => ModuleCat.of R R)
      (fun _ => mult R f)).map (homOfLE (Nat.le_add_right n k)) x = f ^ k * x from hk]
    change f * (f ^ k * x) = f ^ (k + 1) * x
    rw [pow_succ]
    ring

private def coc_isColimit : IsColimit (coc R f) := by
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  have : ReflectsColimitsOfShape ℕ (forget (ModuleCat.{u} R)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget (ModuleCat.{u} R))
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    change Localization.Away f at x
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f x
    refine ⟨n, a, ?_⟩
    change x = a • (IsLocalization.Away.invSelf f : Localization.Away f) ^ n
    rw [Algebra.smul_def, ← ha, mul_assoc, ← mul_pow,
      IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  · intro n x y hxy
    dsimp [seq, Functor.ofSequence] at x y hxy ⊢
    change x • (IsLocalization.Away.invSelf f : Localization.Away f) ^ n =
      y • (IsLocalization.Away.invSelf f : Localization.Away f) ^ n at hxy
    have hxy' : algebraMap R (Localization.Away f) x = algebraMap R (Localization.Away f) y :=
      by
        have h := congrArg (fun z : Localization.Away f => z * algebraMap R _ f ^ n) hxy
        simpa only [Algebra.smul_def, mul_assoc, ← mul_pow,
          mul_comm (IsLocalization.Away.invSelf f) (algebraMap R _ f),
          IsLocalization.Away.mul_invSelf, one_pow, mul_one] using h
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalization.eq_iff_exists (Submonoid.powers f) (Localization.Away f)).mp hxy'
    refine ⟨n + k, homOfLE (Nat.le_add_right n k), ?_⟩
    change (seq R f).map (homOfLE (Nat.le_add_right n k)) x =
      (seq R f).map (homOfLE (Nat.le_add_right n k)) y
    simpa only [seq_map] using hk


open Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u}) (s : (O.obj ⋙ forget CommRingCat.{u}).sections)

private abbrev sectionValue (X : Cᵒᵖ) : O.obj.obj X := s.val X

private noncomputable instance fracAlgebra (X : Cᵒᵖ) :
    Algebra (O.obj.obj X) (ringedSectionLocalizationCarrier O s X) :=
  inferInstanceAs (Algebra (O.obj.obj X)
    (Localization.Away (M := O.obj.obj X) (sectionValue O s X : O.obj.obj X)))

private noncomputable instance fracIsLocalization (X : Cᵒᵖ) :
    IsLocalization.Away (R := O.obj.obj X) (sectionValue O s X : O.obj.obj X)
      (ringedSectionLocalizationCarrier O s X) :=
  inferInstanceAs (IsLocalization.Away (R := O.obj.obj X) (sectionValue O s X : O.obj.obj X)
    (Localization.Away (M := O.obj.obj X) (sectionValue O s X : O.obj.obj X)))

private noncomputable instance fracModule (X : Cᵒᵖ) :
    Module (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).obj.obj X)
      (ringedSectionLocalizationCarrier O s X) :=
  inferInstanceAs (Module (O.obj.obj X) (ringedSectionLocalizationCarrier O s X))

private theorem map_inv {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    ringedSectionLocalizationMap O s a
      (IsLocalization.Away.invSelf (R := O.obj.obj X) (sectionValue O s X : O.obj.obj X)) =
      (IsLocalization.Away.invSelf (R := O.obj.obj Y) (sectionValue O s Y : O.obj.obj Y) :
        ringedSectionLocalizationCarrier O s Y) := by
  have halg (x : O.obj.obj X) :
      ringedSectionLocalizationMap O s a (algebraMap _ _ x) =
        algebraMap (O.obj.obj Y) (ringedSectionLocalizationCarrier O s Y) (O.obj.map a x) := by
    exact IsLocalization.Away.lift_eq _ _ _
  apply IsUnit.mul_right_cancel (IsLocalization.Away.algebraMap_isUnit (R := O.obj.obj Y)
    (sectionValue O s Y : O.obj.obj Y))
  rw [mul_comm (IsLocalization.Away.invSelf (R := O.obj.obj Y) (sectionValue O s Y : O.obj.obj
    Y)), IsLocalization.Away.mul_invSelf]
  calc
    _ = ringedSectionLocalizationMap O s a
        (IsLocalization.Away.invSelf (R := O.obj.obj X) (sectionValue O s X : O.obj.obj X) *
          algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrier O s X) (sectionValue O s
            X)) := by
      have hs : O.obj.map a (sectionValue O s X) = sectionValue O s Y := s.property a
      rw [map_mul, halg, hs]
    _ = 1 := by rw [mul_comm, IsLocalization.Away.mul_invSelf, map_one]

private def fracLeg (n : ℕ) :
    PresheafOfModules.unit.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).obj ⟶
      ringedSectionLocalizationPresheaf O s where
  app X := ModuleCat.ofHom (Y := (ringedSectionLocalizationPresheaf O s).obj X)
    ((LinearMap.id : O.obj.obj X →ₗ[O.obj.obj X] O.obj.obj X).smulRight
    ((IsLocalization.Away.invSelf (R := O.obj.obj X) (sectionValue O s X : O.obj.obj X) :
      ringedSectionLocalizationCarrier O s X) ^ n))
  naturality {X Y} a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change O.obj.map a (show O.obj.obj X from x) • (IsLocalization.Away.invSelf (R := O.obj.obj
      Y) (sectionValue O s Y : O.obj.obj Y) :
      ringedSectionLocalizationCarrier O s Y) ^ n =
        ringedSectionLocalizationMap O s a
          ((show O.obj.obj X from x) • (IsLocalization.Away.invSelf (R := O.obj.obj X)
            (sectionValue O s X : O.obj.obj X) :
            ringedSectionLocalizationCarrier O s X) ^ n)
    rw [ringedSectionLocalizationMap_smul, map_pow, map_inv]


private def sheafMult :
    SheafOfModules.unit.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ⟶
      SheafOfModules.unit.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) :=
  (SheafOfModules.unit _).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk (fun X => sectionValue O s X)
      (fun {_X _Y} a => s.property a))

private def sheafSeq : ℕ ⥤ SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) :=
  Functor.ofSequence (X := fun _ : ℕ => SheafOfModules.unit.{u} _)
    (fun _ => sheafMult O s)

private def fracCoc : Cocone (sheafSeq O s ⋙
    SheafOfModules.forget.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) where
  pt := ringedSectionLocalizationPresheaf O s
  ι := NatTrans.ofSequence (fracLeg O s) (by
    intro n
    simp only [Functor.comp_map, sheafSeq, Functor.ofSequence_map_homOfLE_succ]
    ext X : 2
    apply LinearMap.ext
    intro x
    change ((show O.obj.obj X from x) * (sectionValue O s X : O.obj.obj X)) •
      (IsLocalization.Away.invSelf (R := O.obj.obj X) (sectionValue O s X) :
        ringedSectionLocalizationCarrier O s X) ^ (n + 1) =
        (show O.obj.obj X from x) •
          (IsLocalization.Away.invSelf (R := O.obj.obj X) (sectionValue O s X) :
            ringedSectionLocalizationCarrier O s X) ^ n
    simp only [Algebra.smul_def, map_mul, pow_succ]
    calc
      _ = algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrier O s X) x *
        (IsLocalization.Away.invSelf (R := O.obj.obj X) (sectionValue O s X) :
          ringedSectionLocalizationCarrier O s X) ^ n *
        (algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrier O s X)
          (sectionValue O s X) *
          IsLocalization.Away.invSelf (R := O.obj.obj X) (sectionValue O s X)) := by ring
      _ = _ := by rw [IsLocalization.Away.mul_invSelf, mul_one])


private def evalIso (X : Cᵒᵖ) :
    (sheafSeq O s ⋙
      SheafOfModules.forget.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) ⋙
        PresheafOfModules.evaluation.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).obj X ≅
      seq (O.obj.obj X) (sectionValue O s X) := by
  let t : ((sheafSeq O s ⋙
      SheafOfModules.forget.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) ⋙
        PresheafOfModules.evaluation.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).obj X) ⟶
      seq (O.obj.obj X) (sectionValue O s X) :=
    NatTrans.ofSequence (fun _ => 𝟙 _) (by
      intro n
      with_unfolding_all
        simp only [Functor.comp_map, sheafSeq, seq,
          Functor.ofSequence_map_homOfLE_succ, Category.id_comp, Category.comp_id]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change (show O.obj.obj X from x) * sectionValue O s X =
          sectionValue O s X * (show O.obj.obj X from x)
        exact mul_comm _ _)
  exact NatIso.ofComponents (fun _ => Iso.refl _) (fun a => t.naturality a)

private def fracCoc_isColimit : IsColimit (fracCoc O s) := by
  apply PresheafOfModules.evaluationJointlyReflectsColimits
  intro X
  let e := evalIso O s X
  refine IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv e (coc (O.obj.obj X) (sectionValue O s X))).symm
      (coc_isColimit (O.obj.obj X) (sectionValue O s X))) ?_
  refine Cocone.ext (Iso.refl _) ?_
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private theorem sheaf_localization_iso :
    Nonempty (colimit (sheafSeq O s) ≅ ringedSectionLocalization O s) := by
  let R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O
  let S := PresheafOfModules.sheafification (𝟙 R.obj)
  let e : sheafSeq O s ≅ (sheafSeq O s ⋙ SheafOfModules.forget R) ⋙ S :=
    Functor.isoWhiskerLeft (sheafSeq O s)
      (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm
  exact ⟨HasColimit.isoOfNatIso e ≪≫ colimit.isoColimitCocone
    ⟨S.mapCocone (fracCoc O s), isColimitOfPreserves S (fracCoc_isColimit O s)⟩⟩


end CategoryTheory

namespace CategoryTheory

/-- Sheafifying sectionwise fractions agrees with the sequential module colimit.

Source: Stacks Project, algebraization.tex, Tag 0997, lemma-hom-from-Af.
(blueprint: lem-weil-pbc-section-localization-sequence).
Proof: on an object V of the slice over U, send the class of a at stage n to a/f_V^n.
This respects the relation a at stage n equals f_V*a at stage n+1. Every fraction is in
the image. Equality of a/f_V^n and b/f_V^m means that after multiplication by a further
power of f_V the cross products agree, which is exactly equality at a later stage in the
sequential colimit. These linear identifications commute with restriction: restricting a
fraction restricts numerator and denominator. Hence the presheaf colimit is the fraction
presheaf. Module sheafification is a left adjoint and preserves the colimit; its value on
the unit sheaf is canonically the unit sheaf. The induced isomorphism is the assertion.
This argument also covers f=0, nilpotent f, and the zero ring.
-/
theorem sectionLocalization_sequence_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U)) :
    Nonempty
      (ringedSiteSectionLocalization ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        U f ≅ ringedSectionLocalization (R.over U) (ringedSliceSection R U f)) := by
  exact sheaf_localization_iso (R.over U) (ringedSliceSection R U f)

end CategoryTheory
