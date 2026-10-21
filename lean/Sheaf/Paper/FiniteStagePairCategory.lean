/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NQ, NG and NS
-/
module

public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.PbcFiniteCompletedCoefficientMap
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.CategoryTheory.StageSystem.Basic

import Sheaf.Paper.PbcScalarExtension
import all Sheaf.Paper.CompletedAdicCoefficientDatum
import all Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.Torsion.Field
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction

/-!
# Scalar extension of completed integral coefficients and its raw rationalization

Source: blueprint, proper base change, order 1307
(blueprint: def-weil-pbc-finite-stage-pair-category).

The coefficient map is fixed by every finite quotient. Its derived tensor functor
is the recorded K-flat construction. Rationalization is uniquely fixed by its
composite with the integral localization, including its object function.

For objects `(E,K)` and `(F,L)`, an upstream `PairCategory.Rep` contains a finite
coefficient field `M`, inclusions `E ≤ M` and `F ≤ M`, and a morphism between
the two specified scalar extensions in `pbcStageCategory M`. Its transport is
`pbcScalarAssociator.inv ≫ pbcScalarExtension.map u ≫ pbcScalarAssociator.hom`.
The upstream quotient identifies exactly those representatives whose transports
agree at a further finite coefficient field; none of these data is a parameter
of `PbcFiniteStagePairCategory`.

## Main definitions

* `pbcStageCategory`: the recorded raw rational finite coefficient stage.
* `pbcScalarSystem`: its concrete normalized tensor extension system.
* `PbcFiniteStagePairCategory`: the common-stage quotient with its Hom group laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] ULift.module
-- Avoid the generic flatness search for vector spaces over the coefficient field.
attribute [local instance 2000] DivisionSemiring.to_moduleIsTorsionFree
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.StageSystem

universe w v z
variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type z} [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)]
  (S : StageSystem C)

/-- Addition on classes is fixed by addition of representatives at any common stage.
Source: blueprint finite-stage pair category
(blueprint: def-weil-pbc-finite-stage-pair-category). -/
def PairPreadditiveNormalized (P : Preadditive S.PairCategory) : Prop := by
  letI := P
  exact ∀ (X Y : S.PairCategory) (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n)
    (f g : X.toStage hX ⟶ Y.toStage hY),
    PairCategory.mkHom n hX hY (f + g) =
      PairCategory.mkHom n hX hY f + PairCategory.mkHom n hX hY g ∧
    PairCategory.mkHom n hX hY (0 : X.toStage hX ⟶ Y.toStage hY) = 0

section AdditiveConstruction

variable [∀ i j (h : i ≤ j), (S.T h).Additive]

omit [IsDirectedOrder I] in
private lemma pair_tr_add {i j n p : I} {hi : i ≤ n} {hj : j ≤ n}
    (h : n ≤ p) {x : C i} {y : C j}
    (f g : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    S.tr h (f + g) = S.tr h f + S.tr h g := by
  simp [tr, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

omit [IsDirectedOrder I] in
private lemma pair_tr_zero {i j n p : I} {hi : i ≤ n} {hj : j ≤ n}
    (h : n ≤ p) {x : C i} {y : C j} :
    S.tr h (0 : (S.T hi).obj x ⟶ (S.T hj).obj y) = 0 := by
  simp [tr]

omit [IsDirectedOrder I] in
private lemma pair_tr_neg {i j n p : I} {hi : i ≤ n} {hj : j ≤ n}
    (h : n ≤ p) {x : C i} {y : C j}
    (f : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    S.tr h (-f) = -S.tr h f := by
  simp [tr]

open PairCategory in
private def pairAddRep {X Y : S.PairCategory} (r s : Rep X Y) : Rep X Y :=
  ⟨commonStage r.k s.k, r.hX.trans (le_commonStage_left _ _),
    r.hY.trans (le_commonStage_left _ _),
    S.tr (le_commonStage_left _ _) r.u + S.tr (le_commonStage_right _ _) s.u⟩

open PairCategory in
private lemma pairAddRep_rel {X Y : S.PairCategory} {r r' s s' : Rep X Y}
    (hr : Rep.Rel r r') (hs : Rep.Rel s s') :
    Rep.Rel (pairAddRep S r s) (pairAddRep S r' s') := by
  obtain ⟨p, h₁, h₂, e⟩ := hr
  obtain ⟨q, h₃, h₄, e'⟩ := hs
  obtain ⟨a, ha₁, ha₂⟩ := exists_ge_ge p q
  obtain ⟨b, hb₁, hb₂⟩ := exists_ge_ge (commonStage r.k s.k) (commonStage r'.k s'.k)
  obtain ⟨m, hm₁, hm₂⟩ := exists_ge_ge a b
  refine ⟨m, hb₁.trans hm₂, hb₂.trans hm₂, ?_⟩
  change S.tr _ (S.tr _ r.u + S.tr _ s.u) = S.tr _ (S.tr _ r'.u + S.tr _ s'.u)
  rw [pair_tr_add, pair_tr_add, tr_tr, tr_tr, tr_tr, tr_tr]
  exact congrArg₂ (· + ·)
    (Rep.rel_of_eq h₁ h₂ e (ha₁.trans hm₁))
    (Rep.rel_of_eq h₃ h₄ e' (ha₂.trans hm₁))

private def pairHomAdd {X Y : S.PairCategory} (f g : X ⟶ Y) : X ⟶ Y :=
  Quotient.map₂ (pairAddRep S) (fun _ _ hr _ _ hs ↦ pairAddRep_rel S hr hs) f g

open PairCategory in
private lemma pairHomAdd_mk {X Y : S.PairCategory} {n : I}
    {hX : X.stage ≤ n} {hY : Y.stage ≤ n} (f g : X.toStage hX ⟶ Y.toStage hY) :
    pairHomAdd S (mkHom n hX hY f) (mkHom n hX hY g) = mkHom n hX hY (f + g) := by
  change mkHom _ _ _ _ = _
  rw [mkHom_eq_mkHom_iff']
  refine ⟨commonStage n n, le_rfl, le_commonStage_left _ _, ?_⟩
  simp only [pair_tr_add, tr_tr]

private def pairHomNeg {X Y : S.PairCategory} (f : X ⟶ Y) : X ⟶ Y :=
  Quotient.map (fun r ↦ ⟨r.k, r.hX, r.hY, -r.u⟩)
    (by
      rintro r s ⟨p, hr, hs, e⟩
      exact ⟨p, hr, hs, by simpa only [pair_tr_neg] using congrArg Neg.neg e⟩) f

open PairCategory in
private lemma pairHomNeg_mk {X Y : S.PairCategory} {n : I}
    {hX : X.stage ≤ n} {hY : Y.stage ≤ n} (f : X.toStage hX ⟶ Y.toStage hY) :
    pairHomNeg S (mkHom n hX hY f) = mkHom n hX hY (-f) := rfl

open PairCategory in
private def pairHomZero (X Y : S.PairCategory) : X ⟶ Y :=
  mkHom (commonStage X.stage Y.stage) (le_commonStage_left _ _)
    (le_commonStage_right _ _) 0

open PairCategory in
private lemma pairHomZero_mk {X Y : S.PairCategory} (n : I)
    (hX : X.stage ≤ n) (hY : Y.stage ≤ n) :
    pairHomZero S X Y = mkHom n hX hY 0 := by
  rw [pairHomZero, mkHom_eq_mkHom_iff']
  obtain ⟨p, hp, hn⟩ := exists_ge_ge (commonStage X.stage Y.stage) n
  exact ⟨p, hp, hn, by simp only [pair_tr_zero]⟩

open PairCategory in
private abbrev pairHomGroup (X Y : S.PairCategory) : AddCommGroup (X ⟶ Y) := by
  letI : Add (X ⟶ Y) := ⟨pairHomAdd S⟩
  letI : Zero (X ⟶ Y) := ⟨pairHomZero S X Y⟩
  letI : Neg (X ⟶ Y) := ⟨pairHomNeg S⟩
  exact {
    add := pairHomAdd S
    zero := pairHomZero S X Y
    neg := pairHomNeg S
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc f g h := by
      change pairHomAdd S (pairHomAdd S f g) h = pairHomAdd S f (pairHomAdd S g h)
      induction f using hom_induction with
      | h n hX hY f =>
        induction g using hom_induction with
        | h n' hX' hY' g =>
          induction h using hom_induction with
          | h n'' hX'' hY'' h =>
            obtain ⟨a, ha, ha'⟩ := exists_ge_ge n n'
            obtain ⟨p, hp, hp'⟩ := exists_ge_ge a n''
            rw [← mkHom_tr (ha.trans hp) f, ← mkHom_tr (ha'.trans hp) g,
              ← mkHom_tr hp' h]
            simp only [pairHomAdd_mk, add_assoc]
    zero_add f := by
      change pairHomAdd S (pairHomZero S X Y) f = f
      induction f using hom_induction with
      | h n hX hY f => rw [pairHomZero_mk S n hX hY, pairHomAdd_mk, zero_add]
    add_zero f := by
      change pairHomAdd S f (pairHomZero S X Y) = f
      induction f using hom_induction with
      | h n hX hY f => rw [pairHomZero_mk S n hX hY, pairHomAdd_mk, add_zero]
    neg_add_cancel f := by
      change pairHomAdd S (pairHomNeg S f) f = pairHomZero S X Y
      induction f using hom_induction with
      | h n hX hY f =>
        rw [pairHomNeg_mk, pairHomAdd_mk, neg_add_cancel, pairHomZero_mk S n hX hY]
    add_comm f g := by
      change pairHomAdd S f g = pairHomAdd S g f
      obtain ⟨n, _, hX, hY, _, _, f, g, rfl, rfl⟩ :=
        exists_common_stage f g X.stage
      rw [pairHomAdd_mk, pairHomAdd_mk, add_comm] }

open PairCategory in
private abbrev pairPreadditiveStructure : Preadditive S.PairCategory where
  homGroup := pairHomGroup S
  add_comp X Y Z f g h := by
    induction f using hom_induction with
    | h n hX hY f =>
      induction g using hom_induction with
      | h n' hX' hY' g =>
        induction h using hom_induction with
        | h n'' hY'' hZ h =>
          obtain ⟨a, ha, ha'⟩ := exists_ge_ge n n'
          obtain ⟨p, hp, hp'⟩ := exists_ge_ge a n''
          rw [← mkHom_tr (ha.trans hp) f, ← mkHom_tr (ha'.trans hp) g,
            ← mkHom_tr hp' h]
          change pairHomAdd S _ _ ≫ _ = pairHomAdd S (_ ≫ _) (_ ≫ _)
          rw [pairHomAdd_mk, mkHom_comp_mkHom, mkHom_comp_mkHom,
            mkHom_comp_mkHom, pairHomAdd_mk, Preadditive.add_comp]
  comp_add X Y Z f g h := by
    induction f using hom_induction with
    | h n hX hY f =>
      induction g using hom_induction with
      | h n' hY' hZ g =>
        induction h using hom_induction with
        | h n'' hY'' hZ' h =>
          obtain ⟨a, ha, ha'⟩ := exists_ge_ge n n'
          obtain ⟨p, hp, hp'⟩ := exists_ge_ge a n''
          rw [← mkHom_tr (ha.trans hp) f, ← mkHom_tr (ha'.trans hp) g,
            ← mkHom_tr hp' h]
          change _ ≫ pairHomAdd S _ _ = pairHomAdd S (_ ≫ _) (_ ≫ _)
          rw [pairHomAdd_mk, mkHom_comp_mkHom, mkHom_comp_mkHom,
            mkHom_comp_mkHom, pairHomAdd_mk, Preadditive.comp_add]

end AdditiveConstruction

/-- The common-stage formulas determine a unique preadditive structure.
Source: blueprint finite-stage pair category
(blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: transport is conjugation of an additive functor by associators, so it is
additive. For two representatives pass to their finite common upper stage and
add there. A second choice agrees after transport to a common further stage.
Negation and zero descend in the same way. All abelian-group identities and
bilinearity of composition hold after passing to one common stage. Every
morphism has a representative, so these equations also prove uniqueness. -/
theorem pairPreadditive_exists [∀ i j (h : i ≤ j), (S.T h).Additive] :
    ∃! P : Preadditive S.PairCategory, S.PairPreadditiveNormalized P := by
  refine ⟨pairPreadditiveStructure S, ?_, ?_⟩
  · intro X Y n hX hY f g
    exact ⟨(pairHomAdd_mk S f g).symm, (pairHomZero_mk S n hX hY).symm⟩
  · intro P hP
    apply Preadditive.ext
    funext X Y
    apply AddCommGroup.ext
    funext f g
    obtain ⟨n, _, hX, hY, _, _, f, g, rfl, rfl⟩ :=
      PairCategory.exists_common_stage f g X.stage
    exact ((hP X Y n hX hY f g).1).symm.trans (pairHomAdd_mk S f g).symm

/-- The preadditive structure determined by the common-stage group laws.
Source: blueprint finite-stage pair category
(blueprint: def-weil-pbc-finite-stage-pair-category). -/
instance pairPreadditive [∀ i j (h : i ≤ j), (S.T h).Additive] :
    Preadditive S.PairCategory := (S.pairPreadditive_exists).exists.choose

end CategoryTheory.StageSystem

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section DerivedUnit
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {A : C ⥤ C} {B : D ⥤ D} {F : C ⥤ D}
  [A.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

private noncomputable abbrev pairDerivedUnit (e : A ≅ 𝟭 C) : A.mapDerivedCategory ≅ 𝟭 _ :=
  mapDerivedCategoryNatIso e ≪≫ mapDerivedCategoryIdIso C

private lemma pairDerivedComp_id_comp (e : A ≅ 𝟭 C) (a : A ⋙ F ≅ F)
    (h : a = isoWhiskerRight e F ≪≫ leftUnitor F) :
    (mapDerivedCategoryCompIso A F).symm ≪≫ mapDerivedCategoryNatIso a =
      isoWhiskerRight (pairDerivedUnit e) F.mapDerivedCategory ≪≫
      leftUnitor F.mapDerivedCategory := by
  rw [h]
  have he : (mapDerivedCategoryNatIso (leftUnitor F)).hom = 𝟙 _ :=
    mapDerivedCategoryNatIso_refl
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hn := congr_app (mapDerivedCategoryNatIso_isoWhiskerRight e F) K
  have hu := congr_app (mapDerivedCategoryCompIso_id_comp F) K
  simp only [NatTrans.comp_app, whiskerRight_app, NatTrans.id_app] at hn hu
  simp only [pairDerivedUnit, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, map_comp, leftUnitor_hom_app,
    mapDerivedCategoryNatIso_trans, he, Category.comp_id, Category.assoc]
  rw [← cancel_epi ((mapDerivedCategoryCompIso A F).hom.app K),
    Iso.hom_inv_id_app_assoc, ← reassoc_of% hn, reassoc_of% hu, Category.comp_id]
  exact (Category.comp_id _).symm

private lemma pairDerivedComp_comp_id (e : B ≅ 𝟭 D) (a : F ⋙ B ≅ F)
    (h : a = isoWhiskerLeft F e ≪≫ rightUnitor F) :
    (mapDerivedCategoryCompIso F B).symm ≪≫ mapDerivedCategoryNatIso a =
      isoWhiskerLeft F.mapDerivedCategory (pairDerivedUnit e) ≪≫
      rightUnitor F.mapDerivedCategory := by
  rw [h]
  have he : (mapDerivedCategoryNatIso (rightUnitor F)).hom = 𝟙 _ :=
    mapDerivedCategoryNatIso_refl
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hn := congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft F e) K
  have hu := congr_app (mapDerivedCategoryCompIso_comp_id F) K
  simp only [NatTrans.comp_app, whiskerLeft_app, NatTrans.id_app] at hn hu
  simp only [pairDerivedUnit, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, rightUnitor_hom_app,
    mapDerivedCategoryNatIso_trans, he, Category.comp_id, Category.assoc]
  rw [← cancel_epi ((mapDerivedCategoryCompIso F B).hom.app K),
    Iso.hom_inv_id_app_assoc, ← reassoc_of% hn, reassoc_of% hu, Category.comp_id]
  exact (Category.comp_id _).symm
end DerivedUnit
end CategoryTheory.Functor

section RawLocalization

universe r₁ v₁ u₁ v₂ u₂
open scoped TensorProduct
variable {R : Type r₁} [CommRing R] {C : Type u₁} [Category.{v₁} C]
  [Preadditive C] [Linear R C] (p : R)
  {D : Type u₂} [Category.{v₂} D]

private lemma pairRaw_clear {X Y : ScalarLocalization R C p} (f : X ⟶ Y) :
    ∃ (s : Submonoid.powers p) (g : X.obj ⟶ Y.obj),
      f ≫ (ScalarLocalization.localization R C p).map ((s : R) • 𝟙 Y.obj) =
        (ScalarLocalization.localization R C p).map g := by
  obtain ⟨⟨g, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers p)
    (TensorProduct.mk R (Localization.Away p) (X.obj ⟶ Y.obj) 1) f
  refine ⟨s, g, ?_⟩
  change ScalarLocalization.composition R C p _ _ _ (1 ⊗ₜ[R] ((s : R) • 𝟙 Y.obj)) f = _
  have he : (1 : Localization.Away p) ⊗ₜ[R] ((s : R) • 𝟙 Y.obj) =
      (s : R) • (𝟙 Y : Y ⟶ Y) := by
    change 1 ⊗ₜ[R] ((s : R) • 𝟙 Y.obj) = (s : R) • (1 ⊗ₜ[R] 𝟙 Y.obj)
    exact TensorProduct.tmul_smul _ _ _
  change f ≫ (1 ⊗ₜ[R] ((s : R) • 𝟙 Y.obj)) = _
  rw [he, Linear.comp_smul, Category.comp_id]
  exact hs

private lemma pairRaw_denominator (Y : C) (s : Submonoid.powers p) :
    IsIso ((ScalarLocalization.localization R C p).map ((s : R) • 𝟙 Y)) := by
  obtain ⟨a, ha⟩ := IsLocalization.map_units (Localization.Away p) s
  let e : ScalarLocalization.mk (R := R) (p := p) Y ≅ ScalarLocalization.mk Y :=
    { hom := (a : Localization.Away p) ⊗ₜ[R] 𝟙 Y
      inv := (↑(a⁻¹) : Localization.Away p) ⊗ₜ[R] 𝟙 Y
      hom_inv_id := by
        change ScalarLocalization.composition R C p _ _ _ _ _ = 1 ⊗ₜ[R] 𝟙 Y
        simp [ScalarLocalization.composition_tmul]
      inv_hom_id := by
        change ScalarLocalization.composition R C p _ _ _ _ _ = 1 ⊗ₜ[R] 𝟙 Y
        simp [ScalarLocalization.composition_tmul] }
  have he : (ScalarLocalization.localization R C p).map ((s : R) • 𝟙 Y) = e.hom := by
    change 1 ⊗ₜ[R] ((s : R) • 𝟙 Y) = (a : Localization.Away p) ⊗ₜ[R] 𝟙 Y
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, ha]
  rw [he]
  exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

private def pairRaw_natTrans {F G : ScalarLocalization R C p ⥤ D}
    (e : ScalarLocalization.localization R C p ⋙ F ⟶
      ScalarLocalization.localization R C p ⋙ G) : F ⟶ G where
  app X := e.app X.obj
  naturality {X Y} f := by
    rcases X with ⟨X⟩
    rcases Y with ⟨Y⟩
    obtain ⟨s, g, hg⟩ := pairRaw_clear p f
    have := pairRaw_denominator p Y s
    have hn := e.naturality ((s : R) • 𝟙 Y)
    change F.map ((ScalarLocalization.localization R C p).map ((s : R) • 𝟙 Y)) ≫
      e.app Y = e.app Y ≫ G.map ((ScalarLocalization.localization R C p).map
        ((s : R) • 𝟙 Y)) at hn
    apply (cancel_mono (G.map ((ScalarLocalization.localization R C p).map
      ((s : R) • 𝟙 Y)))).1
    rw [Category.assoc, ← hn, ← Category.assoc, ← F.map_comp, hg,
      Category.assoc, ← G.map_comp, hg]
    exact e.naturality g

private def pairRaw_natIso {F G : ScalarLocalization R C p ⥤ D}
    (e : ScalarLocalization.localization R C p ⋙ F ≅
      ScalarLocalization.localization R C p ⋙ G) : F ≅ G where
  hom := pairRaw_natTrans p e.hom
  inv := pairRaw_natTrans p e.inv
  hom_inv_id := by ext X; exact e.hom_inv_id_app X.obj
  inv_hom_id := by ext X; exact e.inv_hom_id_app X.obj

private lemma pairRaw_functor_ext {F G : ScalarLocalization R C p ⥤ D}
    (h : ScalarLocalization.localization R C p ⋙ F =
      ScalarLocalization.localization R C p ⋙ G) : F = G := by
  refine Functor.ext_of_iso (pairRaw_natIso p (eqToIso h))
    (fun X ↦ Functor.congr_obj h X.obj) ?_
  intro X
  change (eqToHom h : _ ⟶ _).app X.obj = _
  rw [eqToHom_app]

end RawLocalization

private lemma pairLift_eq {A B : Type*} [Category A] [Category B]
    (P : ObjectProperty B) {F G : A ⥤ B} (h : F = G)
    (hf : ∀ X, P (F.obj X)) (hg : ∀ X, P (G.obj X)) :
    P.lift F hf = P.lift G hg := by
  subst G
  rfl

universe wD u₁ v₁
private theorem pairDerived_unit
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{wD} A]
    (F : A ⥤ A) [F.Additive] (LF : DerivedCategory A ⥤ DerivedCategory A)
    (ε : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ))]
    (e : F ≅ 𝟭 A) :
    ∃! d : LF ≅ 𝟭 _, ∀ P : CochainComplex A ℤ,
      d.hom.app (DerivedCategory.Q.obj P) =
        LF.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
        ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso A).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
  let t : F.mapHomotopyCategory (.up ℤ) ≅ 𝟭 (HomotopyCategory A (.up ℤ)) :=
    { hom := NatTrans.mapHomotopyCategory e.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory e.inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] } ≪≫
      Functor.mapHomotopyCategoryIdIso A (.up ℤ)
  let τ := Functor.isoWhiskerRight t DerivedCategory.Qh ≪≫
    Functor.leftUnitor DerivedCategory.Qh
  let a := Functor.rightUnitor (DerivedCategory.Qh : HomotopyCategory A (.up ℤ) ⥤ _)
  let := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso A (.up ℤ)) (𝟭 (DerivedCategory A)) a
  let d := Functor.leftDerivedNatIso LF (𝟭 _) ε a.hom
    (HomotopyCategory.quasiIso A (.up ℤ)) τ
  have hd (H : HomotopyCategory A (.up ℤ)) :
      d.hom.app (DerivedCategory.Qh.obj H) = ε.app H ≫
        DerivedCategory.Qh.map (t.hom.app H) := by
    have h := Functor.leftDerivedNatTrans_app LF (𝟭 _) ε a.hom
      (HomotopyCategory.quasiIso A (.up ℤ)) τ.hom H
    change d.hom.app (DerivedCategory.Qh.obj H) ≫ 𝟙 _ =
      ε.app H ≫ (DerivedCategory.Qh.map (t.hom.app H) ≫ 𝟙 _) at h
    simpa only [Category.comp_id] using h
  have hp (P : CochainComplex A ℤ) :
      d.hom.app (DerivedCategory.Q.obj P) =
        LF.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
        ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso A).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
    have hn := d.hom.naturality ((DerivedCategory.quotientCompQhIso A).inv.app P)
    dsimp only [Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn
    have hf : (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P = 𝟙 _ := rfl
    have ht : t.hom.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) =
        (HomotopyCategory.quotient A (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
      simp only [t, Iso.trans_hom, NatTrans.comp_app,
        Functor.mapHomotopyCategoryIdIso_hom_app_eq_id]
      erw [Category.comp_id]
      rfl
    calc
      _ = LF.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
          d.hom.app ((HomotopyCategory.quotient A (.up ℤ) ⋙ DerivedCategory.Qh).obj P) ≫
          (DerivedCategory.quotientCompQhIso A).hom.app P := by
        dsimp only [Functor.comp_obj]
        rw [reassoc_of% hn]
        simp only [Iso.inv_hom_id_app, Category.comp_id]
      _ = _ := by
        dsimp only [Functor.comp_obj]
        erw [hd, ht, hf, DerivedCategory.Qh.map_id]
        simp only [Category.id_comp, Category.assoc]
        erw [DerivedCategory.quotientCompQhIso_hom_naturality]
  refine ⟨d, hp, ?_⟩
  intro d' hd'
  apply Iso.ext
  exact Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) (fun P ↦ (hd' P).trans (hp P).symm)

private theorem pairTransport_cocycle
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃]
    [Category B₀] [Category B₁] [Category B₂] [Category B₃]
    (Q₀ : A₀ ⥤ B₀) (Q₁ : A₁ ⥤ B₁) (Q₂ : A₂ ⥤ B₂) (Q₃ : A₃ ⥤ B₃)
    (I₀₁ : A₀ ⥤ A₁) (I₁₂ : A₁ ⥤ A₂) (I₂₃ : A₂ ⥤ A₃)
    (I₀₂ : A₀ ⥤ A₂) (I₁₃ : A₁ ⥤ A₃) (I₀₃ : A₀ ⥤ A₃)
    (T₀₁ : B₀ ⥤ B₁) (T₁₂ : B₁ ⥤ B₂) (T₂₃ : B₂ ⥤ B₃)
    (T₀₂ : B₀ ⥤ B₂) (T₁₃ : B₁ ⥤ B₃) (T₀₃ : B₀ ⥤ B₃)
    (a₀₁₂ : I₀₁ ⋙ I₁₂ ≅ I₀₂) (a₁₂₃ : I₁₂ ⋙ I₂₃ ≅ I₁₃)
    (a₀₁₃ : I₀₁ ⋙ I₁₃ ≅ I₀₃) (a₀₂₃ : I₀₂ ⋙ I₂₃ ≅ I₀₃)
    (b₀₁₂ : T₀₁ ⋙ T₁₂ ≅ T₀₂) (b₁₂₃ : T₁₂ ⋙ T₂₃ ≅ T₁₃)
    (b₀₁₃ : T₀₁ ⋙ T₁₃ ≅ T₀₃) (b₀₂₃ : T₀₂ ⋙ T₂₃ ≅ T₀₃)
    (c₀₁ : Q₀ ⋙ T₀₁ ≅ I₀₁ ⋙ Q₁) (c₁₂ : Q₁ ⋙ T₁₂ ≅ I₁₂ ⋙ Q₂)
    (c₂₃ : Q₂ ⋙ T₂₃ ≅ I₂₃ ⋙ Q₃) (c₀₂ : Q₀ ⋙ T₀₂ ≅ I₀₂ ⋙ Q₂)
    (c₁₃ : Q₁ ⋙ T₁₃ ≅ I₁₃ ⋙ Q₃) (c₀₃ : Q₀ ⋙ T₀₃ ≅ I₀₃ ⋙ Q₃)
    (h₀₁₂ : ∀ X, b₀₁₂.hom.app (Q₀.obj X) = T₁₂.map (c₀₁.hom.app X) ≫
      c₁₂.hom.app (I₀₁.obj X) ≫ Q₂.map (a₀₁₂.hom.app X) ≫ c₀₂.inv.app X)
    (h₁₂₃ : ∀ X, b₁₂₃.hom.app (Q₁.obj X) = T₂₃.map (c₁₂.hom.app X) ≫
      c₂₃.hom.app (I₁₂.obj X) ≫ Q₃.map (a₁₂₃.hom.app X) ≫ c₁₃.inv.app X)
    (h₀₁₃ : ∀ X, b₀₁₃.hom.app (Q₀.obj X) = T₁₃.map (c₀₁.hom.app X) ≫
      c₁₃.hom.app (I₀₁.obj X) ≫ Q₃.map (a₀₁₃.hom.app X) ≫ c₀₃.inv.app X)
    (h₀₂₃ : ∀ X, b₀₂₃.hom.app (Q₀.obj X) = T₂₃.map (c₀₂.hom.app X) ≫
      c₂₃.hom.app (I₀₂.obj X) ≫ Q₃.map (a₀₂₃.hom.app X) ≫ c₀₃.inv.app X)
    (hi : ∀ X, I₂₃.map (a₀₁₂.hom.app X) ≫ a₀₂₃.hom.app X =
      a₁₂₃.hom.app (I₀₁.obj X) ≫ a₀₁₃.hom.app X) (X : A₀) :
    T₂₃.map (b₀₁₂.hom.app (Q₀.obj X)) ≫ b₀₂₃.hom.app (Q₀.obj X) =
      b₁₂₃.hom.app (T₀₁.obj (Q₀.obj X)) ≫ b₀₁₃.hom.app (Q₀.obj X) := by
  rw [← cancel_mono (c₀₃.hom.app X)]
  rw [h₀₁₂, h₀₂₃, h₀₁₃]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
  rw [← T₂₃.map_comp_assoc (c₀₂.inv.app X) (c₀₂.hom.app X),
    Iso.inv_hom_id_app, T₂₃.map_id, Category.id_comp]
  rw [← reassoc_of% (b₁₂₃.hom.naturality (c₀₁.hom.app X)), h₁₂₃]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% (c₂₃.hom.naturality (a₀₁₂.hom.app X))]
  erw [Category.comp_id, Category.comp_id]
  rw [← Q₃.map_comp, hi, Q₃.map_comp]

private lemma pairTransport_left_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Q : A ⥤ B) (R : C ⥤ D) (I : A ⥤ A) (J : A ⥤ C)
    (S : B ⥤ B) (hs : S = 𝟭 B) (T : B ⥤ D) (u : I ≅ 𝟭 A)
    (c₀ : Q ⋙ S ≅ I ⋙ Q) (c : Q ⋙ T ≅ J ⋙ R)
    (hc : HEq c₀ (Functor.rightUnitor Q ≪≫ (Functor.leftUnitor Q).symm ≪≫
      Functor.isoWhiskerRight u.symm Q))
    (a : I ⋙ J ≅ J) (ha : ∀ X, a.hom.app X = J.map (u.hom.app X))
    (b : S ⋙ T ≅ T)
    (hb : ∀ X, b.hom.app (Q.obj X) = T.map (c₀.hom.app X) ≫
      c.hom.app (I.obj X) ≫ R.map (a.hom.app X) ≫ c.inv.app X)
    (hQ : ∀ Y, ∃ X, Q.obj X = Y) : HEq b (Functor.leftUnitor T) := by
  subst S
  have hc' := eq_of_heq hc
  apply heq_of_eq
  apply Iso.ext
  apply NatTrans.ext
  funext Y
  obtain ⟨X, rfl⟩ := hQ Y
  rw [hb, ha, hc']
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.rightUnitor_hom_app,
    Iso.symm_hom, Functor.leftUnitor_inv_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp, Functor.leftUnitor_hom_app]
  erw [Category.id_comp]
  rw [reassoc_of% (c.hom.naturality (u.inv.app X))]
  erw [← R.map_comp_assoc, ← J.map_comp, Iso.inv_hom_id_app, J.map_id, R.map_id,
    Category.id_comp, Iso.hom_inv_id_app]
  rfl

private lemma pairTransport_right_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Q : A ⥤ B) (R : C ⥤ D) (I : C ⥤ C) (J : A ⥤ C)
    (S : D ⥤ D) (hs : S = 𝟭 D) (T : B ⥤ D) (u : I ≅ 𝟭 C)
    (c₀ : R ⋙ S ≅ I ⋙ R) (c : Q ⋙ T ≅ J ⋙ R)
    (hc : HEq c₀ (Functor.rightUnitor R ≪≫ (Functor.leftUnitor R).symm ≪≫
      Functor.isoWhiskerRight u.symm R))
    (a : J ⋙ I ≅ J) (ha : ∀ X, a.hom.app X = u.hom.app (J.obj X))
    (b : T ⋙ S ≅ T)
    (hb : ∀ X, b.hom.app (Q.obj X) = S.map (c.hom.app X) ≫
      c₀.hom.app (J.obj X) ≫ R.map (a.hom.app X) ≫ c.inv.app X)
    (hQ : ∀ Y, ∃ X, Q.obj X = Y) : HEq b (Functor.rightUnitor T) := by
  subst S
  have hc' := eq_of_heq hc
  apply heq_of_eq
  apply Iso.ext
  apply NatTrans.ext
  funext Y
  obtain ⟨X, rfl⟩ := hQ Y
  rw [hb, ha, hc']
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.rightUnitor_hom_app,
    Iso.symm_hom, Functor.leftUnitor_inv_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp, Functor.id_map]
  erw [Category.id_comp]
  erw [← R.map_comp_assoc, Iso.inv_hom_id_app, R.map_id, Category.id_comp,
    Iso.hom_inv_id_app]
  rfl

private def pairTransportIso
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (Q₀ : A₀ ⥤ B₀) (Q₁ : A₁ ⥤ B₁) (Q₂ : A₂ ⥤ B₂)
    (I₀₁ : A₀ ⥤ A₁) (I₁₂ : A₁ ⥤ A₂) (I₀₂ : A₀ ⥤ A₂)
    (T₀₁ : B₀ ⥤ B₁) (T₁₂ : B₁ ⥤ B₂) (T₀₂ : B₀ ⥤ B₂)
    (c₀₁ : Q₀ ⋙ T₀₁ ≅ I₀₁ ⋙ Q₁) (c₁₂ : Q₁ ⋙ T₁₂ ≅ I₁₂ ⋙ Q₂)
    (c₀₂ : Q₀ ⋙ T₀₂ ≅ I₀₂ ⋙ Q₂) (a : I₀₁ ⋙ I₁₂ ≅ I₀₂) :
    Q₀ ⋙ (T₀₁ ⋙ T₁₂) ≅ Q₀ ⋙ T₀₂ :=
  (Functor.associator Q₀ T₀₁ T₁₂).symm ≪≫
    Functor.isoWhiskerRight c₀₁ T₁₂ ≪≫ Functor.associator I₀₁ Q₁ T₁₂ ≪≫
    Functor.isoWhiskerLeft I₀₁ c₁₂ ≪≫ (Functor.associator I₀₁ I₁₂ Q₂).symm ≪≫
    Functor.isoWhiskerRight a Q₂ ≪≫ c₀₂.symm

private lemma pairTransportIso_hom
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (Q₀ : A₀ ⥤ B₀) (Q₁ : A₁ ⥤ B₁) (Q₂ : A₂ ⥤ B₂)
    (I₀₁ : A₀ ⥤ A₁) (I₁₂ : A₁ ⥤ A₂) (I₀₂ : A₀ ⥤ A₂)
    (T₀₁ : B₀ ⥤ B₁) (T₁₂ : B₁ ⥤ B₂) (T₀₂ : B₀ ⥤ B₂)
    (c₀₁ : Q₀ ⋙ T₀₁ ≅ I₀₁ ⋙ Q₁) (c₁₂ : Q₁ ⋙ T₁₂ ≅ I₁₂ ⋙ Q₂)
    (c₀₂ : Q₀ ⋙ T₀₂ ≅ I₀₂ ⋙ Q₂) (a : I₀₁ ⋙ I₁₂ ≅ I₀₂) (X : A₀) :
    (pairTransportIso Q₀ Q₁ Q₂ I₀₁ I₁₂ I₀₂ T₀₁ T₁₂ T₀₂ c₀₁ c₁₂ c₀₂ a).hom.app X =
      T₁₂.map (c₀₁.hom.app X) ≫ c₁₂.hom.app (I₀₁.obj X) ≫
        Q₂.map (a.hom.app X) ≫ c₀₂.inv.app X := by
  simp only [pairTransportIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, Category.id_comp]

private lemma pairDerivedId_app
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{wD} A]
    (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryIdIso A).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 A).mapDerivedCategoryFactors.hom.app K := by
  have hf := congr_app (congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh A))
    ((HomotopyCategory.quotient A (.up ℤ)).obj K)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.mapDerivedCategoryFactorsh_hom_app,
    Functor.mapHomotopyCategoryIdIso_hom_app] at hf
  have h₁ : ((𝟭 A).mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  have h₂ : (Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app K = 𝟙 _ := rfl
  erw [h₁, h₂] at hf
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.comp_id] at hf
  have he : (DerivedCategory.quotientCompQhIso A).inv.app
      (((𝟭 A).mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  erw [he] at hf
  erw [Category.id_comp, Category.comp_id] at hf
  erw [Category.comp_id] at hf
  exact hf

private lemma pairDerived_unit_mate
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{wD} A]
    (L R : A ⥤ A) [L.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (adj : L ⊣ R) (ri : R ≅ 𝟭 A) (e : L ≅ 𝟭 A)
    (he : ∀ M, adj.unit.app M ≫ ri.hom.app (L.obj M) ≫ e.hom.app M = 𝟙 M)
    (LD : DerivedCategory A ⥤ DerivedCategory A) (d : LD ⊣ R.mapDerivedCategory)
    (P : CochainComplex A ℤ → Prop)
    (hres : ∀ X : CochainComplex A ℤ, ∃ (K : CochainComplex A ℤ) (s : K ⟶ X),
      P K ∧ QuasiIso s)
    (c : ∀ K : CochainComplex A ℤ, LD.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj K))
    (hd : ∀ K, P K → d.unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (c K) ≫
      R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app K))
    (u : LD ≅ 𝟭 (DerivedCategory A))
    (hu : ∀ K, u.hom.app (DerivedCategory.Q.obj K) = c K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K)) :
    u = d.leftAdjointIdIso
      (Functor.mapDerivedCategoryNatIso ri ≪≫ Functor.mapDerivedCategoryIdIso A) := by
  let rd := Functor.mapDerivedCategoryNatIso ri ≪≫ Functor.mapDerivedCategoryIdIso A
  let v := d.leftAdjointIdIso rd
  have hr (K : CochainComplex A ℤ) :
      rd.hom.app (DerivedCategory.Q.obj K) = R.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ri.hom (.up ℤ)).app K) := by
    change (Functor.mapDerivedCategoryNatIso ri).hom.app (DerivedCategory.Q.obj K) ≫
      (Functor.mapDerivedCategoryIdIso A).hom.app (DerivedCategory.Q.obj K) = _
    rw [pairDerivedId_app]
    exact Functor.mapDerivedCategoryNatIso_fac ri K
  have hk (K : CochainComplex A ℤ) (hK : P K) :
      u.hom.app (DerivedCategory.Q.obj K) = v.hom.app (DerivedCategory.Q.obj K) := by
    apply (d.homEquiv _ _).injective
    have hv : rd.inv.app (DerivedCategory.Q.obj K) =
        d.unit.app (DerivedCategory.Q.obj K) ≫
          R.mapDerivedCategory.map (v.hom.app (DerivedCategory.Q.obj K)) := by
      simpa only [v, Adjunction.conjugateEquiv_leftAdjointIdIso_hom,
        Adjunction.id_unit, NatTrans.id_app, Functor.id_obj, Category.id_comp] using
        unit_conjugateEquiv Adjunction.id d v.hom (DerivedCategory.Q.obj K)
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← hv]
    rw [← cancel_mono (rd.hom.app (DerivedCategory.Q.obj K)), Iso.inv_hom_id_app]
    have ho : (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex ri.hom (.up ℤ)).app
          ((L.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K = 𝟙 K := by
      ext n
      exact he (K.X n)
    erw [hu, Functor.map_comp]
    simp only [Category.assoc]
    erw [(rd.hom.naturality
        (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K))),
      hr]
    simp only [Category.assoc]
    erw [reassoc_of% (hd K hK)]
    simp only [Functor.id_map]
    erw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, ho,
      DerivedCategory.Q.map_id]
    rfl
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
  intro X
  obtain ⟨K, s, hK, hs⟩ := hres X
  have : QuasiIso s := hs
  rw [← cancel_epi (LD.map (DerivedCategory.Q.map s)),
    u.hom.naturality, v.hom.naturality, hk K hK]

namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData
open scoped TensorProduct ChangeOfRings

@[irreducible] private def pbcPair_restrictUnit (T : Scheme.{u})
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ R) (ha : a = 𝟙 R) : pbcRestrict a ≅ 𝟭 (pbcModules T R) :=
  eqToIso (congrArg (fun b : R ⟶ R ↦ pbcRestrict b) ha) ≪≫
    NatIso.ofComponents (fun M ↦
      (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun U ↦
          ModuleCat.restrictScalarsId'App _ rfl (M.val.obj U))
          (fun {U V} f ↦ by ext x; rfl))) (fun f ↦ by ext U x; rfl)

private lemma pbcPair_restrictUnit_sections (T : Scheme.{u})
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ R) (ha : a = 𝟙 R)
    (M : pbcModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcPair_restrictUnit T a ha).hom.app M).val.app U x = x := by
  subst a
  unfold pbcPair_restrictUnit
  rfl

private lemma pbcPair_unit_mate (T : Scheme.{u})
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ R)
    (ri : pbcRestrict a ≅ 𝟭 (pbcModules T R))
    (hri : ∀ (M : pbcModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (ri.hom.app M).val.app U x = x)
    (e : pbcExtend a ≅ 𝟭 (pbcModules T R))
    (he : ∀ (M : pbcModules T R) (U : T.ProEtᵒᵖ) (r : R.obj.obj U) (x : M.val.obj U),
      (e.hom.app M).val.app U (pbcTensorSection a M U r x) = r • x)
    (u : pbcDerivedExtend a ≅ 𝟭 (DerivedCategory (pbcModules T R)))
    (hu : ∀ P : CochainComplex (pbcModules T R) ℤ,
      u.hom.app (DerivedCategory.Q.obj P) = pbcComplexCounit a P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P)) :
    u = (pbcDerivedScalarAdjunction a).leftAdjointIdIso
      (Functor.mapDerivedCategoryNatIso ri ≪≫ Functor.mapDerivedCategoryIdIso _) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  apply pairDerived_unit_mate (pbcExtend a) (pbcRestrict a) (pbcScalarAdjunction a) ri e
    ?_ (pbcDerivedExtend a) (pbcDerivedScalarAdjunction a)
    (CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology T) (R := R))
    (ScalarReductionDerivedProof.kFlatResolutions.{u + 1, u, u + 1}
      (J := ProEt.topology T) (O := R)) (pbcComplexCounit a)
    (pbcDerivedScalarAdjunction_exists a).exists.choose_spec u hu
  intro M
  ext U x
  change (e.hom.app M).val.app U
      ((ri.hom.app ((pbcExtend a).obj M)).val.app U
        (((pbcScalarAdjunction a).unit.app M).val.app U x)) = x
  erw [hri, (pbcScalarAdjunction_exists a).exists.choose_spec,
    he M U 1 x, one_smul]


private lemma pbcPair_restrict_left_unit (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ R) (ha : a = 𝟙 R) (b : R ⟶ S) (hab : a ≫ b = b) :
    pbcDerivedRestrictComp a b b hab =
      Functor.isoWhiskerLeft (pbcDerivedRestrict b)
        (Functor.mapDerivedCategoryNatIso (pbcPair_restrictUnit T a ha) ≪≫
          Functor.mapDerivedCategoryIdIso _) ≪≫ Functor.rightUnitor (pbcDerivedRestrict b) := by
  have ho : pbcRestrictComp a b b hab =
      Functor.isoWhiskerLeft (pbcRestrict b) (pbcPair_restrictUnit T a ha) ≪≫
        Functor.rightUnitor (pbcRestrict b) := by
    apply Iso.ext
    ext M U x
    change ((pbcRestrictComp a b b hab).hom.app M).val.app U x =
      ((pbcPair_restrictUnit T a ha).hom.app ((pbcRestrict b).obj M)).val.app U x
    exact ((pbcRestrictComp_exists a b b hab).exists.choose_spec M U x).trans
      (pbcPair_restrictUnit_sections T a ha ((pbcRestrict b).obj M) U x).symm
  exact CategoryTheory.Functor.pairDerivedComp_comp_id (pbcPair_restrictUnit T a ha)
    (pbcRestrictComp a b b hab) ho

private lemma pbcPair_restrict_right_unit (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : S ⟶ S) (ha : a = 𝟙 S) (b : R ⟶ S) (hba : b ≫ a = b) :
    pbcDerivedRestrictComp b a b hba =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso (pbcPair_restrictUnit T a ha) ≪≫
          Functor.mapDerivedCategoryIdIso _) (pbcDerivedRestrict b) ≪≫
        Functor.leftUnitor (pbcDerivedRestrict b) := by
  have ho : pbcRestrictComp b a b hba =
      Functor.isoWhiskerRight (pbcPair_restrictUnit T a ha) (pbcRestrict b) ≪≫
        Functor.leftUnitor (pbcRestrict b) := by
    apply Iso.ext
    ext M U x
    change ((pbcRestrictComp b a b hba).hom.app M).val.app U x =
      ((pbcPair_restrictUnit T a ha).hom.app M).val.app U x
    exact ((pbcRestrictComp_exists b a b hba).exists.choose_spec M U x).trans
      (pbcPair_restrictUnit_sections T a ha M U x).symm
  exact CategoryTheory.Functor.pairDerivedComp_id_comp (pbcPair_restrictUnit T a ha)
    (pbcRestrictComp b a b hba) ho


private lemma pbcPair_rational_fac_raw
    (l : ℕ) [Fact l.Prime] (A B : Type u) [Field A] [Field B]
    [Algebra (Padic l) A] [Algebra (Padic l) B]
    [FiniteDimensional (Padic l) A] [FiniteDimensional (Padic l) B]
    (i : A →ₐ[Padic l] B) (T : Scheme.{u}) [IsNoetherian T]
    (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
    (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) :
    pbcRationalization T (pbcIntegralDatum l A) (pbcUniformizer l A) ⋙
        pbcRationalScalarExtension l A B i T hdim hl =
      pbcEmbeddingIntegralTensor l A B i T hdim hl ⋙
        pbcRationalization T (pbcIntegralDatum l B) (pbcUniformizer l B) := by
  refine CategoryTheory.Functor.ext
    (F := pbcRationalization T (pbcIntegralDatum l A) (pbcUniformizer l A) ⋙
      pbcRationalScalarExtension l A B i T hdim hl)
    (G := pbcEmbeddingIntegralTensor l A B i T hdim hl ⋙
      pbcRationalization T (pbcIntegralDatum l B) (pbcUniformizer l B))
    (fun _ ↦ rfl) ?_
  intro K L f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have hh := (pbcRationalScalarHom_exists l A B i T hdim hl K L).exists.choose_spec 1 f
  change pbcRationalScalarHom l A B i T hdim hl K L
      ((1 * 1) ⊗ₜ[PbcIntegralRing l A] f) =
    ((pbcRationalCoefficientEquiv l B).symm (i (pbcRationalCoefficientEquiv l A 1)) * 1)
      ⊗ₜ[PbcIntegralRing l B] (pbcEmbeddingIntegralTensor l A B i T hdim hl).map f at hh
  change pbcRationalScalarHom l A B i T hdim hl K L
    (1 ⊗ₜ[PbcIntegralRing l A] f) =
      1 ⊗ₜ[PbcIntegralRing l B] (pbcEmbeddingIntegralTensor l A B i T hdim hl).map f
  simpa only [map_one, mul_one] using hh

private lemma pbcPair_ordinaryUnit (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    ∃! e : pbcExtend (𝟙 R) ≅ 𝟭 (pbcModules T R),
      ∀ (M : pbcModules T R) (U : T.ProEtᵒᵖ) (r : R.obj.obj U) (x : M.val.obj U),
        (e.hom.app M).val.app U (pbcTensorSection (𝟙 R) M U r x) = r • x := by
  let ri : pbcRestrict (𝟙 R) ≅ 𝟭 (pbcModules T R) :=
    NatIso.ofComponents (fun M ↦
      (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun U ↦
          ModuleCat.restrictScalarsId'App _ rfl (M.val.obj U))
          (fun {U V} f ↦ by ext x; rfl))) (fun f ↦ by ext U x; rfl)
  let a := (pbcScalarAdjunction (𝟙 R)).ofNatIsoRight ri
  let e := a.leftAdjointUniq Adjunction.id
  have he (M : pbcModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
      (e.hom.app M).val.app U (pbcTensorSection (𝟙 R) M U 1 x) = x := by
    have hh := Adjunction.unit_leftAdjointUniq_hom_app a Adjunction.id M
    have ht := congrArg (fun f ↦ f.val.app U x) hh
    change (e.hom.app M).val.app U
      (((pbcScalarAdjunction (𝟙 R)).unit.app M).val.app U x) = x at ht
    have hu := (pbcScalarAdjunction_exists (𝟙 R)).exists.choose_spec M U x
    exact (congrArg ((e.hom.app M).val.app U) hu.symm).trans ht
  clear_value e
  clear a ri
  have hs (M : pbcModules T R) (U : T.ProEtᵒᵖ) (r : R.obj.obj U)
      (x : M.val.obj U) :
      pbcTensorSection (𝟙 R) M U r x = r • pbcTensorSection (𝟙 R) M U 1 x := by
    have h := completedTensor_smul T (𝟙 R) M U r 1 x
    simpa only [mul_one, pbcTensorSection] using h
  refine ⟨e, ?_, ?_⟩
  · intro M U r x
    rw [hs, map_smul, he]
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ((pbcScalarAdjunction (𝟙 R)).homEquiv M M).injective
    ext U x
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    change (e'.hom.app M).val.app U
      (((pbcScalarAdjunction (𝟙 R)).unit.app M).val.app U x) =
      (e.hom.app M).val.app U
        (((pbcScalarAdjunction (𝟙 R)).unit.app M).val.app U x)
    have hu := (pbcScalarAdjunction_exists (𝟙 R)).exists.choose_spec M U x
    calc
      _ = (e'.hom.app M).val.app U (pbcTensorSection (𝟙 R) M U 1 x) :=
        congrArg ((e'.hom.app M).val.app U) hu
      _ = x := by simpa only [one_smul] using he' M U 1 x
      _ = (e.hom.app M).val.app U (pbcTensorSection (𝟙 R) M U 1 x) := (he M U x).symm
      _ = _ := congrArg ((e.hom.app M).val.app U) hu.symm

private lemma pbcPair_ambient_assoc
    (T : Scheme.{u}) {R S B D : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : B ⟶ D)
    (ab : R ⟶ B) (bc : S ⟶ D) (abc : R ⟶ D)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (ha_bc : a ≫ bc = abc) (hab_c : ab ≫ c = abc)
    (X : DerivedCategory (pbcModules T R)) :
    (pbcDerivedExtend c).map
        ((Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
          (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction ab)
          (pbcDerivedRestrictComp a b ab hab)).hom.app X) ≫
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction ab)
        (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction abc)
        (pbcDerivedRestrictComp ab c abc hab_c)).hom.app X =
    (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction b)
        (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction bc)
        (pbcDerivedRestrictComp b c bc hbc)).hom.app ((pbcDerivedExtend a).obj X) ≫
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
        (pbcDerivedScalarAdjunction bc) (pbcDerivedScalarAdjunction abc)
        (pbcDerivedRestrictComp a bc abc ha_bc)).hom.app X := by
  have hr : Functor.isoWhiskerLeft (pbcRestrict c) (pbcRestrictComp a b ab hab) ≪≫
        pbcRestrictComp ab c abc hab_c =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pbcRestrictComp b c bc hbc) (pbcRestrict a) ≪≫
        pbcRestrictComp a bc abc ha_bc := by
    apply Iso.ext
    ext M U x
    change ((pbcRestrictComp ab c abc hab_c).hom.app M).val.app U
        (((pbcRestrictComp a b ab hab).hom.app ((pbcRestrict c).obj M)).val.app U x) =
      ((pbcRestrictComp a bc abc ha_bc).hom.app M).val.app U
        (((pbcRestrictComp b c bc hbc).hom.app M).val.app U x)
    erw [(pbcRestrictComp_exists a b ab hab).exists.choose_spec,
      (pbcRestrictComp_exists ab c abc hab_c).exists.choose_spec,
      (pbcRestrictComp_exists b c bc hbc).exists.choose_spec,
      (pbcRestrictComp_exists a bc abc ha_bc).exists.choose_spec]
  have hrD := SheafOfModules.SuccessiveDerivedQuotient.exactComp_assoc
    (pbcRestrict a) (pbcRestrict b) (pbcRestrict c)
    (pbcRestrict ab) (pbcRestrict bc) (pbcRestrict abc)
    (pbcRestrictComp a b ab hab) (pbcRestrictComp b c bc hbc)
    (pbcRestrictComp a bc abc ha_bc) (pbcRestrictComp ab c abc hab_c) hr
  have h := Adjunction.leftAdjointCompIso_assoc
    (pbcDerivedScalarAdjunction a) (pbcDerivedScalarAdjunction b)
    (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction ab)
    (pbcDerivedScalarAdjunction bc) (pbcDerivedScalarAdjunction abc)
    (pbcDerivedRestrictComp a b ab hab) (pbcDerivedRestrictComp b c bc hbc)
    (pbcDerivedRestrictComp a bc abc ha_bc) (pbcDerivedRestrictComp ab c abc hab_c) hrD
  have hh := congrArg (fun e ↦ e.hom.app X) h
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp] at hh
  exact hh.symm

variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
variable {E F G : Padic.FiniteCoefficientFields l Ω}

variable (T : Scheme.{u})

/-- The existing bounded constructible complete integral stage, with its coefficient fixed.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcIntegralStage (E : Padic.FiniteCoefficientFields l Ω) :=
  PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)

/-- The ambient derived coefficient stage used by the integral full inclusion.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcAmbientStage (E : Padic.FiniteCoefficientFields l Ω) :=
  PbcCompletedDerived T (pbcStageDatum.{u} l Ω E)

/-- The existing full inclusion of the integral stage into its ambient derived category.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcStageInclusion (E : Padic.FiniteCoefficientFields l Ω) :
    pbcIntegralStage l Ω T E ⥤ pbcAmbientStage l Ω T E :=
  ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E))

/-- The recorded raw rationalization at the canonical small model of E.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcStageCategory (E : Padic.FiniteCoefficientFields l Ω) :=
  PbcRationalCategory T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)

/-- The recorded integral localization functor at this coefficient stage.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcStageLocalization (E : Padic.FiniteCoefficientFields l Ω) :=
  pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)

omit [IsAlgClosure (Padic l) Ω] in
private lemma pbcPair_levelComparison_hom (E : Padic.FiniteCoefficientFields l Ω)
    (n : ℕ) :
    (pbcLevelConstantComparison T (pbcStageDatum.{u} l Ω E) n).hom =
      AdicCoefficients.constantComparison T
        (PbcIntegralRing l (pbcFiniteField.{u} l Ω E) ⧸
          (pbcStageDatum.{u} l Ω E).ideal ^ (n + 1)) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings T (pbcStageDatum.{u} l Ω E)).obj
    (op n)).property
  change toSheafify _ _ ≫ (pbcLevelConstantComparison T _ n).hom.hom =
    toSheafify _ _ ≫ sheafifyMap _ _
  rw [← toSheafify_naturality]
  ext U b
  exact (pbcLevelConstantComparison_exists T (pbcStageDatum.{u} l Ω E) n).exists.choose_spec U b

private lemma pbcPair_completedMap (h : E ≤ F) :
    pbcCompletedScalarMap l Ω T h =
      pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) T := by
  apply (pbcCompletedScalarMap_exists l Ω T h).unique
  · exact (pbcCompletedScalarMap_exists l Ω T h).exists.choose_spec
  · intro n
    change (pbcScalarCoefficientMap_exists l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T).exists.choose ≫ _ = _
    rw [(pbcScalarCoefficientMap_exists l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T).exists.choose_spec n]
    congr 1
    unfold pbcFiniteScalarMap
    apply (cancel_epi (pbcLevelConstantComparison T (pbcStageDatum.{u} l Ω E) n).hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [pbcPair_levelComparison_hom, pbcPair_levelComparison_hom]
    change (presheafToSheaf _ CommRingCat).map _ ≫
        (presheafToSheaf _ CommRingCat).map _ =
      (presheafToSheaf _ CommRingCat).map _ ≫
        (presheafToSheaf _ CommRingCat).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1

/-- Finite coefficient extension preserves the three defining integral conditions.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: the target integer ring is finite free over the source integer ring.
Compute derived extension on K-flat representatives. Finite freeness commutes
with the reduction tower and its derived limit and preserves completion.
Tensor the common bounded local models and the compatible etale origins.
Their normalization equations follow from ordinary tensor balancing at every
finite quotient; neither the bounds nor the finite stratification changes. -/
theorem pbcAmbientScalarExtension_preserves (h : E ≤ F)
    [IsNoetherian T] (_hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : pbcIntegralStage l Ω T E) :
    PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F)
      ((pbcAmbientScalarExtension l Ω T h).obj K.obj) := by
  change PbcIsBoundedConstructibleComplete T _
    ((pbcDerivedExtend (pbcCompletedScalarMap l Ω T h)).obj K.obj)
  rw [pbcPair_completedMap]
  exact pbcEmbeddingAmbientTensor_preserves l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T _hdim _hl K

variable [IsNoetherian T] (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
  (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- Restriction of the specified ambient tensor extension to the integral subcategories.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcIntegralScalarExtension (h : E ≤ F) :
    pbcIntegralStage l Ω T E ⥤
      pbcIntegralStage l Ω T F :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F))
    ((pbcStageInclusion l Ω T E) ⋙
      pbcAmbientScalarExtension l Ω T h)
    (pbcAmbientScalarExtension_preserves l Ω T h hdim hl)

private lemma pbcPair_integral (h : E ≤ F) :
    pbcIntegralScalarExtension l Ω T hdim hl h =
      pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T hdim hl := by
  have hf : pbcStageInclusion l Ω T E ⋙ pbcAmbientScalarExtension l Ω T h =
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) ⋙
        pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T := by
    unfold pbcAmbientScalarExtension pbcEmbeddingAmbientTensor
    rw [pbcPair_completedMap]
  exact pairLift_eq _ hf _ _

private lemma pbcPair_rational_fac (h : E ≤ F) :
    pbcStageLocalization l Ω T E ⋙
        pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T hdim hl =
      pbcIntegralScalarExtension l Ω T hdim hl h ⋙ pbcStageLocalization l Ω T F := by
  rw [pbcPair_integral]
  exact pbcPair_rational_fac_raw l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T hdim hl

/-- Integral tensor extension has a unique factorization through raw localization.
The equality fixes objects as well as integral morphisms; inverses of uniformizer
multiples then fix every fraction. No arbitrary functor is chosen.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: the image of the source uniformizer is a unit times a positive power of
the target uniformizer, so it becomes invertible in the target localization.
Send a fraction f/pi^n to the integral tensor image of f divided by the image of
pi^n. The tensor relations, bilinearity and balancing prove well-definedness
and functoriality. Every localized morphism is such a fraction, proving uniqueness. -/
theorem pbcRationalScalarExtension_exists (h : E ≤ F) :
    ∃! B : pbcStageCategory l Ω T E ⥤
        pbcStageCategory l Ω T F,
      pbcStageLocalization l Ω T E ⋙ B =
        pbcIntegralScalarExtension l Ω T hdim hl h ⋙
          pbcStageLocalization l Ω T F := by
  refine ⟨pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T hdim hl,
    pbcPair_rational_fac l Ω T hdim hl h, ?_⟩
  intro B hB
  exact pairRaw_functor_ext _ (hB.trans (pbcPair_rational_fac l Ω T hdim hl h).symm)

/-- Raw rationalized tensor extension. Equal coefficient fields use identity literally.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcScalarExtension (h : E ≤ F) :
    pbcStageCategory l Ω T E ⥤
      pbcStageCategory l Ω T F :=
  by
    classical
    exact if e : E = F then e ▸ 𝟭 _ else
      (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose


attribute [local irreducible] pbcScalarExtension

set_option linter.unusedSectionVars false in
/-- Coefficient maps compose exactly, including repeated fields.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: both composites have the same quotient projections, because the field
inclusions compose. Use uniqueness of the completed limit map. -/
theorem pbcCompletedScalarMap_comp (h : E ≤ F) (k : F ≤ G) :
    pbcCompletedScalarMap l Ω T h ≫ pbcCompletedScalarMap l Ω T k =
      pbcCompletedScalarMap l Ω T (h.trans k) := by
  have hi : (pbcIntegerInclusion l Ω k).comp (pbcIntegerInclusion l Ω h) =
      pbcIntegerInclusion l Ω (h.trans k) := by
    apply RingHom.ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    have hinc : pbcFiniteFieldInclusion l Ω k
        (pbcFiniteFieldInclusion l Ω h x.down.val) =
        pbcFiniteFieldInclusion l Ω (h.trans k) x.down.val := by
      change (Shrink.algEquiv (Padic l) G.val).symm
          (IntermediateField.inclusion k
            ((Shrink.algEquiv (Padic l) F.val)
              ((Shrink.algEquiv (Padic l) F.val).symm
                (IntermediateField.inclusion h
                  ((Shrink.algEquiv (Padic l) E.val) x.down.val))))) = _
      rw [AlgEquiv.apply_symm_apply]
      rfl
    simpa [pbcIntegerInclusion, WeilConjectures.integralScalarIntegerInclusion] using hinc
  have hq (n : ℕ) :
      (pbcQuotientInclusion l Ω k n).comp (pbcQuotientInclusion l Ω h n) =
        pbcQuotientInclusion l Ω (h.trans k) n := by
    apply RingHom.ext
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    change Ideal.Quotient.mk _ (pbcIntegerInclusion l Ω k (pbcIntegerInclusion l Ω h x)) =
      Ideal.Quotient.mk _ (pbcIntegerInclusion l Ω (h.trans k) x)
    exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun hi x)
  have hf (n : ℕ) : pbcFiniteScalarMap l Ω T h n ≫ pbcFiniteScalarMap l Ω T k n =
      pbcFiniteScalarMap l Ω T (h.trans k) n := by
    dsimp only [pbcFiniteScalarMap]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc]
    congr 2
    exact congrArg ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map)
      (congrArg CommRingCat.ofHom (hq n))
  apply (pbcCompletedScalarMap_exists l Ω T (h.trans k)).unique
  · intro n
    dsimp only [pbcCompletedScalarMap]
    rw [Category.assoc,
      (pbcCompletedScalarMap_exists l Ω T k).exists.choose_spec n,
      ← Category.assoc,
      (pbcCompletedScalarMap_exists l Ω T h).exists.choose_spec n,
      Category.assoc, hf n]
  · exact (pbcCompletedScalarMap_exists l Ω T (h.trans k)).exists.choose_spec

omit [IsNoetherian T] in
private lemma pbcPair_completedId (E : Padic.FiniteCoefficientFields l Ω) :
    pbcCompletedScalarMap l Ω T (le_refl E) =
      𝟙 (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)) := by
  rw [pbcPair_completedMap]
  have hi : pbcFiniteFieldInclusion.{u} l Ω (le_refl E) =
      AlgHom.id (Padic l) (pbcFiniteField.{u} l Ω E) := by
    ext x
    simp [pbcFiniteFieldInclusion]
  rw [hi]
  exact pbcScalarCoefficientMap_id l (pbcFiniteField.{u} l Ω E) T

set_option linter.unusedSectionVars false in
/-- The tensor unit comparison is fixed on sheafified pure tensors.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: inclusion E→E is identity, also on completions. The balanced map
r tensor x ↦ r*x and x ↦ 1 tensor x are inverse sectionwise, commute with
restriction, and descend through sheafification. Pure tensors generate locally,
so the indicated formula determines the natural isomorphism uniquely. -/
theorem pbcOrdinaryScalarUnit_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! e : pbcExtend (pbcCompletedScalarMap l Ω T (le_refl E)) ≅
        𝟭 (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))),
      ∀ (M : pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)))
        (U : T.ProEtᵒᵖ) (r : (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)).obj.obj U)
        (x : M.val.obj U),
        (e.hom.app M).val.app U
          (pbcTensorSection (pbcCompletedScalarMap l Ω T (le_refl E)) M U r x) = r • x := by
  rw [pbcPair_completedId]
  exact pbcPair_ordinaryUnit T _

/-- The section-normalized ordinary tensor unit.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcOrdinaryScalarUnit (E : Padic.FiniteCoefficientFields l Ω) :
    pbcExtend (pbcCompletedScalarMap l Ω T (le_refl E)) ≅
        𝟭 (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) :=
  (pbcOrdinaryScalarUnit_exists l Ω T E).exists.choose

/-- The derived tensor unit is uniquely fixed by its universal counit on complexes.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: tensor extension along identity is exact. Its universal left-derived
counit is invertible; descend the section-normalized ordinary tensor unit.
Localization of complexes is essentially surjective and full on natural
transformations, so this normalization determines the comparison uniquely. -/
theorem pbcAmbientScalarUnit_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! e : pbcAmbientScalarExtension l Ω T (le_refl E) ≅
        𝟭 (pbcAmbientStage l Ω T E),
      ∀ P : CochainComplex (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) =
          pbcComplexCounit (pbcCompletedScalarMap l Ω T (le_refl E)) P ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex
                (pbcOrdinaryScalarUnit l Ω T E).hom (.up ℤ)).app P) := by
  let φ := pbcCompletedScalarMap l Ω T (le_refl E)
  let := pbcDerivedExtension_universal φ
  simpa only [pbcAmbientScalarExtension, pbcComplexCounit, Category.assoc] using
    pairDerived_unit (pbcExtend φ) (pbcDerivedExtend φ) (pbcExtensionCounit φ)
      (pbcOrdinaryScalarUnit l Ω T E)

/-- The canonical derived tensor unit, rather than an arbitrary unit isomorphism.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcAmbientScalarUnit (E : Padic.FiniteCoefficientFields l Ω) :
    pbcAmbientScalarExtension l Ω T (le_refl E) ≅
        𝟭 (pbcAmbientStage l Ω T E) :=
  (pbcAmbientScalarUnit_exists l Ω T E).exists.choose

/-- The integral tensor unit is the restriction of the canonical ambient one.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: the integral subcategories are full. Lift each component of the ambient
unit and its inverse. Faithfulness gives naturality, inverse equations and
uniqueness. -/
theorem pbcIntegralScalarUnit_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! e : pbcIntegralScalarExtension l Ω T hdim hl (le_refl E) ≅
        𝟭 (pbcIntegralStage l Ω T E),
      Functor.whiskerRight e.hom
          (pbcStageInclusion l Ω T E) =
        Functor.whiskerLeft
          (pbcStageInclusion l Ω T E)
          (pbcAmbientScalarUnit l Ω T E).hom := by
  let e : pbcIntegralScalarExtension l Ω T hdim hl (le_refl E) ≅
      𝟭 (pbcIntegralStage l Ω T E) :=
    NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _ ((pbcAmbientScalarUnit l Ω T E).app K.obj))
      (fun f ↦ by
        apply ObjectProperty.hom_ext
        exact (pbcAmbientScalarUnit l Ω T E).hom.naturality f.hom)
  refine ⟨e, rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext _
  exact congrArg (fun η ↦ η.app K) he'

/-- Integral unit with its ambient normalization.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcIntegralScalarUnit (E : Padic.FiniteCoefficientFields l Ω) :
    pbcIntegralScalarExtension l Ω T hdim hl (le_refl E) ≅
        𝟭 (pbcIntegralStage l Ω T E) :=
  (pbcIntegralScalarUnit_exists l Ω T hdim hl E).exists.choose

/-- The integral/rational comparison is fixed by the tensor unit at equal fields
and the unique localization factorization at distinct fields.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: at equal fields use the section-normalized tensor unit. Otherwise use the
equality in the unique factorization through scalar localization. These cases
are exhaustive. Heterogeneous equality retains the exact functor indices under
the literal identity normalization. Either formula specifies every component
and hence gives uniqueness. -/
theorem pbcScalarIntegralComparison_exists (h : E ≤ F) :
    ∃! c : pbcStageLocalization l Ω T E ⋙
        pbcScalarExtension l Ω T hdim hl h ≅
      pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcStageLocalization l Ω T F,
      (E = F → HEq c
        ((Functor.rightUnitor
          (pbcStageLocalization l Ω T E)) ≪≫
        (Functor.leftUnitor
          (pbcStageLocalization l Ω T E)).symm ≪≫
        Functor.isoWhiskerRight (pbcIntegralScalarUnit l Ω T hdim hl E).symm
          (pbcStageLocalization l Ω T E))) ∧
      (E ≠ F → HEq c
        (eqToIso (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose_spec)) := by
  classical
  by_cases hEF : E = F
  · subst F
    have hs : pbcScalarExtension l Ω T hdim hl h = 𝟭 _ := by
      simp [pbcScalarExtension]
    rw [hs]
    let e := (Functor.rightUnitor (pbcStageLocalization l Ω T E)) ≪≫
      (Functor.leftUnitor (pbcStageLocalization l Ω T E)).symm ≪≫
      Functor.isoWhiskerRight (pbcIntegralScalarUnit l Ω T hdim hl E).symm
        (pbcStageLocalization l Ω T E)
    refine ⟨e, ⟨fun _ ↦ HEq.rfl, fun hne ↦ (hne rfl).elim⟩, ?_⟩
    intro e' he'
    exact eq_of_heq (he'.1 rfl)
  · have hs : pbcScalarExtension l Ω T hdim hl h =
        (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose := by
      simp [pbcScalarExtension, hEF]
    rw [hs]
    refine ⟨eqToIso
      (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose_spec,
      ⟨fun heq ↦ (hEF heq).elim, fun _ ↦ HEq.rfl⟩, ?_⟩
    intro e' he'
    exact eq_of_heq (he'.2 hEF)

/-- The uniquely normalized comparison with integral scalar extension.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcScalarIntegralComparison (h : E ≤ F) :
    pbcStageLocalization l Ω T E ⋙
        pbcScalarExtension l Ω T hdim hl h ≅
      pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcStageLocalization l Ω T F :=
  (pbcScalarIntegralComparison_exists l Ω T hdim hl h).exists.choose

/-- The ambient tensor associator is the mate of composition of actual scalar
restrictions, normalized by their identity on sections.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcAmbientScalarAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcAmbientScalarExtension l Ω T h ⋙ pbcAmbientScalarExtension l Ω T k ≅
      pbcAmbientScalarExtension l Ω T (h.trans k) :=
  Adjunction.leftAdjointCompIso
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T h))
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T k))
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T (h.trans k)))
    (pbcDerivedRestrictComp (pbcCompletedScalarMap l Ω T h)
      (pbcCompletedScalarMap l Ω T k) (pbcCompletedScalarMap l Ω T (h.trans k))
      (pbcCompletedScalarMap_comp l Ω T h k))

/-- Restriction of the canonical ambient associator to the full integral subcategories.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: lift its components and inverse components using fullness. Naturality and
inverse equations follow after the faithful inclusion; the same inclusion gives
uniqueness. -/
theorem pbcIntegralScalarAssociator_exists (h : E ≤ F) (k : F ≤ G) :
    ∃! e : pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcIntegralScalarExtension l Ω T hdim hl k ≅
        pbcIntegralScalarExtension l Ω T hdim hl (h.trans k),
      Functor.whiskerRight e.hom
          (pbcStageInclusion l Ω T G) =
        Functor.whiskerLeft
          (pbcStageInclusion l Ω T E)
          (pbcAmbientScalarAssociator l Ω T h k).hom := by
  let e : pbcIntegralScalarExtension l Ω T hdim hl h ⋙
      pbcIntegralScalarExtension l Ω T hdim hl k ≅
      pbcIntegralScalarExtension l Ω T hdim hl (h.trans k) :=
    NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _ ((pbcAmbientScalarAssociator l Ω T h k).app K.obj))
      (fun f ↦ by
        apply ObjectProperty.hom_ext
        exact (pbcAmbientScalarAssociator l Ω T h k).hom.naturality f.hom)
  refine ⟨e, rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext _
  exact congrArg (fun η ↦ η.app K) he'

/-- The integral associator with the ambient tensor normalization.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcIntegralScalarAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcIntegralScalarExtension l Ω T hdim hl k ≅
        pbcIntegralScalarExtension l Ω T hdim hl (h.trans k) :=
  (pbcIntegralScalarAssociator_exists l Ω T hdim hl h k).exists.choose

attribute [local irreducible] pbcIntegralScalarAssociator pbcScalarIntegralComparison

/-- The rational associator is uniquely determined on the unchanged integral objects.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: apply target rationalization to the integral associator, conjugating by
the integral comparisons. Naturality holds on integral morphisms and hence on
their fractions. Rationalization is surjective on objects, giving uniqueness. -/
theorem pbcScalarAssociator_exists (h : E ≤ F) (k : F ≤ G) :
    ∃! e : pbcScalarExtension l Ω T hdim hl h ⋙
        pbcScalarExtension l Ω T hdim hl k ≅
        pbcScalarExtension l Ω T hdim hl (h.trans k),
      ∀ K : pbcIntegralStage l Ω T E,
        e.hom.app
            ((pbcStageLocalization l Ω T E).obj K) =
          (pbcScalarExtension l Ω T hdim hl k).map
              ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K) ≫
            (pbcScalarIntegralComparison l Ω T hdim hl k).hom.app
              ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) ≫
            (pbcStageLocalization l Ω T G).map
              ((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K) ≫
            (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k)).inv.app K := by
  let c := pairTransportIso
    (pbcStageLocalization l Ω T E) (pbcStageLocalization l Ω T F)
    (pbcStageLocalization l Ω T G)
    (pbcIntegralScalarExtension l Ω T hdim hl h)
    (pbcIntegralScalarExtension l Ω T hdim hl k)
    (pbcIntegralScalarExtension l Ω T hdim hl (h.trans k))
    (pbcScalarExtension l Ω T hdim hl h)
    (pbcScalarExtension l Ω T hdim hl k)
    (pbcScalarExtension l Ω T hdim hl (h.trans k))
    (pbcScalarIntegralComparison l Ω T hdim hl h)
    (pbcScalarIntegralComparison l Ω T hdim hl k)
    (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k))
    (pbcIntegralScalarAssociator l Ω T hdim hl h k)
  refine ⟨pairRaw_natIso (pbcStageUniformizer.{u} l Ω E) c, ?_, ?_⟩
  · intro K
    change c.hom.app K = _
    exact pairTransportIso_hom _ _ _ _ _ _ _ _ _ _ _ _ _ K
  · intro e he
    apply Iso.ext
    ext K
    change e.hom.app K = c.hom.app K.obj
    exact (he K.obj).trans (pairTransportIso_hom _ _ _ _ _ _ _ _ _ _ _ _ _ K.obj).symm

/-- The scalar associator induced by tensor balancing, including the normalized units.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcScalarAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcScalarExtension l Ω T hdim hl h ⋙
        pbcScalarExtension l Ω T hdim hl k ≅
        pbcScalarExtension l Ω T hdim hl (h.trans k) :=
  (pbcScalarAssociator_exists l Ω T hdim hl h k).exists.choose

private lemma pbcPair_scalarAssociator_hom (h : E ≤ F) (k : F ≤ G)
    (K : pbcIntegralStage l Ω T E) :
    (pbcScalarAssociator l Ω T hdim hl h k).hom.app
        ((pbcStageLocalization l Ω T E).obj K) =
      (pbcScalarExtension l Ω T hdim hl k).map
          ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K) ≫
        (pbcScalarIntegralComparison l Ω T hdim hl k).hom.app
          ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) ≫
        (pbcStageLocalization l Ω T G).map
          ((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K) ≫
        (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k)).inv.app K := by
  exact (pbcScalarAssociator_exists l Ω T hdim hl h k).exists.choose_spec K

attribute [local irreducible] pbcScalarAssociator

private lemma pbcPair_integralAssociator_hom (h : E ≤ F) (k : F ≤ G)
    (K : pbcIntegralStage l Ω T E) :
    ((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K).hom =
      (pbcAmbientScalarAssociator l Ω T h k).hom.app K.obj := by
  unfold pbcIntegralScalarAssociator
  exact congrArg (fun η ↦ η.app K)
    (pbcIntegralScalarAssociator_exists l Ω T hdim hl h k).exists.choose_spec

private lemma pbcPair_integral_cocycle {H : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (k : F ≤ G) (j : G ≤ H) (K : pbcIntegralStage l Ω T E) :
    (pbcIntegralScalarExtension l Ω T hdim hl j).map
          ((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K) ≫
        (pbcIntegralScalarAssociator l Ω T hdim hl (h.trans k) j).hom.app K =
      (pbcIntegralScalarAssociator l Ω T hdim hl k j).hom.app
          ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) ≫
        (pbcIntegralScalarAssociator l Ω T hdim hl h (k.trans j)).hom.app K := by
  apply ObjectProperty.hom_ext
  change (pbcAmbientScalarExtension l Ω T j).map
      (((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K).hom) ≫
      ((pbcIntegralScalarAssociator l Ω T hdim hl (h.trans k) j).hom.app K).hom =
    ((pbcIntegralScalarAssociator l Ω T hdim hl k j).hom.app
      ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K)).hom ≫
      ((pbcIntegralScalarAssociator l Ω T hdim hl h (k.trans j)).hom.app K).hom
  rw [pbcPair_integralAssociator_hom, pbcPair_integralAssociator_hom,
    pbcPair_integralAssociator_hom, pbcPair_integralAssociator_hom]
  exact pbcPair_ambient_assoc T (pbcCompletedScalarMap l Ω T h)
    (pbcCompletedScalarMap l Ω T k) (pbcCompletedScalarMap l Ω T j)
    (pbcCompletedScalarMap l Ω T (h.trans k)) (pbcCompletedScalarMap l Ω T (k.trans j))
    (pbcCompletedScalarMap l Ω T ((h.trans k).trans j))
    (pbcCompletedScalarMap_comp l Ω T h k) (pbcCompletedScalarMap_comp l Ω T k j)
    (pbcCompletedScalarMap_comp l Ω T h (k.trans j))
    (pbcCompletedScalarMap_comp l Ω T (h.trans k) j) K.obj

/-- The tensor associators satisfy the pentagon in component form.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: the ambient associators are mates of identity-on-sections restriction
comparisons. Their two four-field composites therefore agree. Full integral
inclusions and rational integral comparisons transport that equality; every
rational object is an integral object, so these tests prove the displayed equality. -/
theorem pbcScalarAssociator_cocycle {H : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (k : F ≤ G) (j : G ≤ H)
    (K : pbcStageCategory l Ω T E) :
    (pbcScalarExtension l Ω T hdim hl j).map
          ((pbcScalarAssociator l Ω T hdim hl h k).hom.app K) ≫
        (pbcScalarAssociator l Ω T hdim hl (h.trans k) j).hom.app K =
      (pbcScalarAssociator l Ω T hdim hl k j).hom.app
          ((pbcScalarExtension l Ω T hdim hl h).obj K) ≫
        (pbcScalarAssociator l Ω T hdim hl h (k.trans j)).hom.app K := by
  exact pairTransport_cocycle
    (pbcStageLocalization l Ω T E) (pbcStageLocalization l Ω T F)
    (pbcStageLocalization l Ω T G) (pbcStageLocalization l Ω T H)
    (pbcIntegralScalarExtension l Ω T hdim hl h)
    (pbcIntegralScalarExtension l Ω T hdim hl k)
    (pbcIntegralScalarExtension l Ω T hdim hl j)
    (pbcIntegralScalarExtension l Ω T hdim hl (h.trans k))
    (pbcIntegralScalarExtension l Ω T hdim hl (k.trans j))
    (pbcIntegralScalarExtension l Ω T hdim hl (h.trans (k.trans j)))
    (pbcScalarExtension l Ω T hdim hl h) (pbcScalarExtension l Ω T hdim hl k)
    (pbcScalarExtension l Ω T hdim hl j) (pbcScalarExtension l Ω T hdim hl (h.trans k))
    (pbcScalarExtension l Ω T hdim hl (k.trans j))
    (pbcScalarExtension l Ω T hdim hl (h.trans (k.trans j)))
    (pbcIntegralScalarAssociator l Ω T hdim hl h k)
    (pbcIntegralScalarAssociator l Ω T hdim hl k j)
    (pbcIntegralScalarAssociator l Ω T hdim hl h (k.trans j))
    (pbcIntegralScalarAssociator l Ω T hdim hl (h.trans k) j)
    (pbcScalarAssociator l Ω T hdim hl h k) (pbcScalarAssociator l Ω T hdim hl k j)
    (pbcScalarAssociator l Ω T hdim hl h (k.trans j))
    (pbcScalarAssociator l Ω T hdim hl (h.trans k) j)
    (pbcScalarIntegralComparison l Ω T hdim hl h)
    (pbcScalarIntegralComparison l Ω T hdim hl k)
    (pbcScalarIntegralComparison l Ω T hdim hl j)
    (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k))
    (pbcScalarIntegralComparison l Ω T hdim hl (k.trans j))
    (pbcScalarIntegralComparison l Ω T hdim hl (h.trans (k.trans j)))
    (pbcPair_scalarAssociator_hom l Ω T hdim hl h k)
    (pbcPair_scalarAssociator_hom l Ω T hdim hl k j)
    (pbcPair_scalarAssociator_hom l Ω T hdim hl h (k.trans j))
    (pbcPair_scalarAssociator_hom l Ω T hdim hl (h.trans k) j)
    (pbcPair_integral_cocycle l Ω T hdim hl h k j) K.obj

private lemma pbcPair_ambientUnit_mate (E : Padic.FiniteCoefficientFields l Ω) :
    pbcAmbientScalarUnit l Ω T E =
      (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T (le_refl E))).leftAdjointIdIso
        (Functor.mapDerivedCategoryNatIso
          (pbcPair_restrictUnit T (pbcCompletedScalarMap l Ω T (le_refl E))
            (pbcPair_completedId l Ω T E)) ≪≫ Functor.mapDerivedCategoryIdIso _) := by
  exact pbcPair_unit_mate T (pbcCompletedScalarMap l Ω T (le_refl E))
    (pbcPair_restrictUnit T _ (pbcPair_completedId l Ω T E))
    (pbcPair_restrictUnit_sections T _ (pbcPair_completedId l Ω T E))
    (pbcOrdinaryScalarUnit l Ω T E)
    (pbcOrdinaryScalarUnit_exists l Ω T E).exists.choose_spec
    (pbcAmbientScalarUnit l Ω T E)
    (pbcAmbientScalarUnit_exists l Ω T E).exists.choose_spec

private lemma pbcPair_ambient_left_unit (h : E ≤ F) :
    pbcAmbientScalarAssociator l Ω T (le_refl E) h =
      Functor.isoWhiskerRight (pbcAmbientScalarUnit l Ω T E)
        (pbcAmbientScalarExtension l Ω T h) ≪≫
      Functor.leftUnitor (pbcAmbientScalarExtension l Ω T h) := by
  rw [pbcPair_ambientUnit_mate]
  exact Adjunction.leftAdjointCompIso_id_comp _ _ _ _
    (pbcPair_restrict_left_unit T (pbcCompletedScalarMap l Ω T (le_refl E))
      (pbcPair_completedId l Ω T E) (pbcCompletedScalarMap l Ω T h)
      (pbcCompletedScalarMap_comp l Ω T (le_refl E) h))

private lemma pbcPair_ambient_right_unit (h : E ≤ F) :
    pbcAmbientScalarAssociator l Ω T h (le_refl F) =
      Functor.isoWhiskerLeft (pbcAmbientScalarExtension l Ω T h)
        (pbcAmbientScalarUnit l Ω T F) ≪≫
      Functor.rightUnitor (pbcAmbientScalarExtension l Ω T h) := by
  rw [pbcPair_ambientUnit_mate]
  exact Adjunction.leftAdjointCompIso_comp_id _ _ _ _
    (pbcPair_restrict_right_unit T (pbcCompletedScalarMap l Ω T (le_refl F))
      (pbcPair_completedId l Ω T F) (pbcCompletedScalarMap l Ω T h)
      (pbcCompletedScalarMap_comp l Ω T h (le_refl F)))

private lemma pbcPair_integralUnit_hom (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω T E) :
    ((pbcIntegralScalarUnit l Ω T hdim hl E).hom.app K).hom =
      (pbcAmbientScalarUnit l Ω T E).hom.app K.obj := by
  exact congrArg (fun η ↦ η.app K)
    (pbcIntegralScalarUnit_exists l Ω T hdim hl E).exists.choose_spec

private lemma pbcPair_integral_left_unit (h : E ≤ F)
    (K : pbcIntegralStage l Ω T E) :
    (pbcIntegralScalarAssociator l Ω T hdim hl (le_refl E) h).hom.app K =
      (pbcIntegralScalarExtension l Ω T hdim hl h).map
        ((pbcIntegralScalarUnit l Ω T hdim hl E).hom.app K) := by
  apply ObjectProperty.hom_ext
  change ((pbcIntegralScalarAssociator l Ω T hdim hl (le_refl E) h).hom.app K).hom =
    (pbcAmbientScalarExtension l Ω T h).map
      (((pbcIntegralScalarUnit l Ω T hdim hl E).hom.app K).hom)
  rw [pbcPair_integralAssociator_hom, pbcPair_integralUnit_hom,
    pbcPair_ambient_left_unit]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  erw [Category.comp_id]

private lemma pbcPair_integral_right_unit (h : E ≤ F)
    (K : pbcIntegralStage l Ω T E) :
    (pbcIntegralScalarAssociator l Ω T hdim hl h (le_refl F)).hom.app K =
      (pbcIntegralScalarUnit l Ω T hdim hl F).hom.app
        ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) := by
  apply ObjectProperty.hom_ext
  rw [pbcPair_integralAssociator_hom, pbcPair_integralUnit_hom,
    pbcPair_ambient_right_unit]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  erw [Category.comp_id]
  rfl

private lemma pbcPair_comparison_unit (E : Padic.FiniteCoefficientFields l Ω) :
    HEq (pbcScalarIntegralComparison l Ω T hdim hl (le_refl E))
      (Functor.rightUnitor (pbcStageLocalization l Ω T E) ≪≫
        (Functor.leftUnitor (pbcStageLocalization l Ω T E)).symm ≪≫
        Functor.isoWhiskerRight (pbcIntegralScalarUnit l Ω T hdim hl E).symm
          (pbcStageLocalization l Ω T E)) := by
  unfold pbcScalarIntegralComparison
  exact (pbcScalarIntegralComparison_exists l Ω T hdim hl (le_refl E)).exists.choose_spec.1
    rfl

attribute [local irreducible] pbcIntegralScalarExtension pbcIntegralScalarUnit

/-- Normalized tensor identities give the literal identity transitions and unit associators.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: the equal-field branch of pbcScalarExtension is identity by definition.
The ambient tensor-unit comparison is multiplication on pure tensors, and the
ambient associator is tensor balancing with the same ordinary adjunction units.
Their unit equations hold on those generators. Faithful integral inclusions and
rationalization transport the equations, including repeated coefficient fields. -/
theorem pbcScalarSystem_units (h : E ≤ F) :
    pbcScalarExtension l Ω T hdim hl (le_refl E) = 𝟭 _ ∧
      HEq (pbcScalarAssociator l Ω T hdim hl (le_refl E) h)
        (Functor.leftUnitor (pbcScalarExtension l Ω T hdim hl h)) ∧
      HEq (pbcScalarAssociator l Ω T hdim hl h (le_refl F))
        (Functor.rightUnitor (pbcScalarExtension l Ω T hdim hl h)) := by
  classical
  have hE : pbcScalarExtension l Ω T hdim hl (le_refl E) = 𝟭 _ := by
    simp [pbcScalarExtension]
  have hF : pbcScalarExtension l Ω T hdim hl (le_refl F) = 𝟭 _ := by
    simp [pbcScalarExtension]
  refine ⟨hE, ?_, ?_⟩
  · exact pairTransport_left_unit
      (pbcStageLocalization l Ω T E) (pbcStageLocalization l Ω T F)
      (pbcIntegralScalarExtension l Ω T hdim hl (le_refl E))
      (pbcIntegralScalarExtension l Ω T hdim hl h)
      (pbcScalarExtension l Ω T hdim hl (le_refl E)) hE
      (pbcScalarExtension l Ω T hdim hl h) (pbcIntegralScalarUnit l Ω T hdim hl E)
      (pbcScalarIntegralComparison l Ω T hdim hl (le_refl E))
      (pbcScalarIntegralComparison l Ω T hdim hl h)
      (pbcPair_comparison_unit l Ω T hdim hl E)
      (pbcIntegralScalarAssociator l Ω T hdim hl (le_refl E) h)
      (pbcPair_integral_left_unit l Ω T hdim hl h)
      (pbcScalarAssociator l Ω T hdim hl (le_refl E) h)
      (pbcPair_scalarAssociator_hom l Ω T hdim hl (le_refl E) h)
      (fun K ↦ ⟨K.obj, rfl⟩)
  · exact pairTransport_right_unit
      (pbcStageLocalization l Ω T E) (pbcStageLocalization l Ω T F)
      (pbcIntegralScalarExtension l Ω T hdim hl (le_refl F))
      (pbcIntegralScalarExtension l Ω T hdim hl h)
      (pbcScalarExtension l Ω T hdim hl (le_refl F)) hF
      (pbcScalarExtension l Ω T hdim hl h) (pbcIntegralScalarUnit l Ω T hdim hl F)
      (pbcScalarIntegralComparison l Ω T hdim hl (le_refl F))
      (pbcScalarIntegralComparison l Ω T hdim hl h)
      (pbcPair_comparison_unit l Ω T hdim hl F)
      (pbcIntegralScalarAssociator l Ω T hdim hl h (le_refl F))
      (pbcPair_integral_right_unit l Ω T hdim hl h)
      (pbcScalarAssociator l Ω T hdim hl h (le_refl F))
      (pbcPair_scalarAssociator_hom l Ω T hdim hl h (le_refl F))
      (fun K ↦ ⟨K.obj, rfl⟩)

/-- Rationalized tensor extension is additive.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: tensor extension is additive on complexes and derived morphisms. The
localization formula sends sums of fractions to sums; identity fields are
literal identity functors, which are additive as well. -/
@[instance] theorem pbcScalarExtension_additive (h : E ≤ F) :
    (pbcScalarExtension l Ω T hdim hl h).Additive := by
  classical
  by_cases he : E = F
  · subst F
    have hi : pbcScalarExtension l Ω T hdim hl h = 𝟭 _ := by
      simp [pbcScalarExtension]
    rw [hi]
    infer_instance
  · unfold pbcScalarExtension
    rw [dif_neg he]
    have hB := (pbcRationalScalarExtension_exists l Ω T hdim hl h).unique
      (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose_spec
      (pbcPair_rational_fac l Ω T hdim hl h)
    rw [hB]
    let : Fact (∃ m : ℕ, topologicalKrullDim T ≤ m) := ⟨hdim⟩
    let : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t)) := ⟨hl⟩
    exact pbcRationalScalarAdditive l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T

/-- The concrete finite-stage scalar system on the PBC raw rational categories.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcScalarSystem :
    StageSystem (fun E : Padic.FiniteCoefficientFields l Ω ↦
      pbcStageCategory l Ω T E) where
  T h := pbcScalarExtension l Ω T hdim hl h
  assoc h k := pbcScalarAssociator l Ω T hdim hl h k
  cocycle h k j K := pbcScalarAssociator_cocycle l Ω T hdim hl h k j K


/-- Finite composita give the common coefficient stages.
Source: blueprint finite-stage pair category
(blueprint: def-weil-pbc-finite-stage-pair-category). -/
instance pbcFiniteCoefficientFields_directed :
    IsDirectedOrder (Padic.FiniteCoefficientFields l Ω) :=
  ⟨fun E F ↦ ⟨Padic.finiteCoefficientCompositum l Ω E F,
    (Padic.finiteCoefficientFields_properties l Ω).1 E F⟩⟩

/-- The concrete PBC finite-stage pair category, without an idempotent envelope.
Its quotient representatives, transport, identities and common-stage composition
are exactly StageSystem.PairCategory with this concrete coefficient system.
Source: blueprint finite-stage pair category
(blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev PbcFiniteStagePairCategory := (pbcScalarSystem l Ω T hdim hl).PairCategory

/-- The base field witnesses nonemptiness, including the empty-diagram case.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
instance pbcFiniteCoefficientFields_nonempty : Nonempty (Padic.FiniteCoefficientFields l Ω) :=
  ⟨Padic.finiteCoefficientBase l Ω⟩

end AlgebraicGeometry.Scheme

