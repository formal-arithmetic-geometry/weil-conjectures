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
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

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

attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
universe u c v'
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

namespace CategoryTheory.ScalarLocalization

universe r v
open scoped TensorProduct

private noncomputable def semilinearRationalComparison
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    ScalarLocalization R C p ⥤ Rationalization (Submonoid.powers p) C where
  obj X := (Rationalization.Q (Submonoid.powers p) C).obj X.obj
  map {X Y} f := Rationalization.tensorHomEquiv (Submonoid.powers p)
    (Localization.Away p) X.obj Y.obj f
  map_id X := by
    change Rationalization.tensorHomEquiv _ _ _ _ (1 ⊗ₜ[R] 𝟙 X.obj) = _
    simp
  map_comp {X Y Z} f g := by
    induction f using TensorProduct.induction_on with
    | zero => simp only [Limits.zero_comp, map_zero, Limits.zero_comp]
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero => simp only [Limits.comp_zero, map_zero, Limits.comp_zero]
      | tmul b g =>
        change Rationalization.tensorHomEquiv _ _ _ _
          (composition R C p _ _ _ (b ⊗ₜ[R] g) (a ⊗ₜ[R] f)) = _
        rw [composition_tmul]
        simp only [Rationalization.tensorHomEquiv_tmul, Functor.map_comp,
          Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
      | add g h hg hh =>
        rw [Preadditive.comp_add X Y Z (a ⊗ₜ[R] f) g h]
        simp only [_root_.map_add]
        rw [hg, hh]
        exact (Preadditive.comp_add _ _ _ _ _ _).symm
    | add f h hf hh =>
      rw [Preadditive.add_comp X Y Z f h g]
      simp only [_root_.map_add]
      rw [hf, hh]
      exact (Preadditive.add_comp _ _ _ _ _ _).symm

private theorem semilinear_localization_isLocalization
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    (localization R C p).IsLocalization (Rationalization.W (Submonoid.powers p) C) := by
  classical
  let M := Submonoid.powers p
  let E := semilinearRationalComparison R C p
  have : E.Full := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).surjective⟩
  have : E.Faithful := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).injective⟩
  have : E.EssSurj := ⟨fun X ↦ by
    obtain ⟨Y, ⟨e⟩⟩ := Rationalization.exists_iso_obj X
    exact ⟨⟨Y⟩, ⟨e⟩⟩⟩
  have : E.IsEquivalence := {}
  let Q := localization R C p
  have fac : Q ⋙ E ≅ Rationalization.Q M C :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [Q, E, localization, semilinearRationalComparison]
      simp only [Category.comp_id, Category.id_comp,
        Rationalization.tensorHomEquiv_tmul, one_smul]
      rfl)
  exact Functor.IsLocalization.of_equivalence_target (Rationalization.Q M C)
    (Rationalization.W M C) Q E.asEquivalence.symm
    (Functor.isoWhiskerRight fac.symm E.inv ≪≫ (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft Q E.asEquivalence.unitIso.symm ≪≫ Q.rightUnitor)

end CategoryTheory.ScalarLocalization

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma complexCounit_eq {C : Type u} [Category.{v'} C] [Abelian C]
    [HasDerivedCategory C] (L : C ⥤ C) [L.Additive]
    (LD : DerivedCategory C ⥤ DerivedCategory C)
    (α : DerivedCategory.Qh ⋙ LD ⟶ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ) :
    LD.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
      α.app ((HomotopyCategory.quotient _ _).obj P) ≫
      DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app
        ((L.mapHomologicalComplex (.up ℤ)).obj P) =
      α.app ((HomotopyCategory.quotient _ _).obj P) := by
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    Functor.mapHomotopyCategoryFactors, Functor.map_id, Category.id_comp, Category.comp_id]
  erw [LD.map_id, DerivedCategory.Qh.map_id, Category.comp_id, Category.id_comp]
  erw [Category.comp_id]

private lemma derivedUnit {C : Type u} [Category.{v'} C] [Abelian C]
    [HasDerivedCategory C] (L : C ⥤ C) [L.Additive] (e : L ≅ 𝟭 C)
    (LD : DerivedCategory C ⥤ DerivedCategory C)
    (α : DerivedCategory.Qh ⋙ LD ⟶ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [LD.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso C (.up ℤ))] :
    ∃! d : LD ≅ 𝟭 _, ∀ P : CochainComplex C ℤ,
      d.hom.app (DerivedCategory.Q.obj P) =
        α.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
  let eh : L.mapHomotopyCategory (.up ℤ) ≅ (𝟭 C).mapHomotopyCategory (.up ℤ) := {
    hom := NatTrans.mapHomotopyCategory e.hom _
    inv := NatTrans.mapHomotopyCategory e.inv _
    hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
      NatTrans.mapHomotopyCategory_id]
    inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
      NatTrans.mapHomotopyCategory_id] }
  let b : L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅ DerivedCategory.Qh :=
    Functor.isoWhiskerRight (eh ≪≫ Functor.mapHomotopyCategoryIdIso C (.up ℤ))
      DerivedCategory.Qh ≪≫ Functor.leftUnitor DerivedCategory.Qh
  have hi : (HomotopyCategory.quasiIso C (.up ℤ)).IsInvertedBy
      (L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) := by
    intro X Y f hf
    have : IsIso (DerivedCategory.Qh.map f) :=
      Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ)) f hf
    rw [← NatIso.naturality_2 b f]
    change IsIso (b.hom.app X ≫ DerivedCategory.Qh.map f ≫ b.inv.app Y)
    infer_instance
  have : IsIso α := Functor.isIso_of_isLeftDerivedFunctor_of_inverts LD α hi
  let c : DerivedCategory.Qh ⋙ LD ≅ DerivedCategory.Qh ⋙ 𝟭 _ :=
    asIso α ≪≫ b ≪≫ (Functor.rightUnitor DerivedCategory.Qh).symm
  let d := Localization.liftNatIso DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
    (DerivedCategory.Qh ⋙ LD) (DerivedCategory.Qh ⋙ 𝟭 _) LD (𝟭 _) c
  have hd (P : CochainComplex C ℤ) : d.hom.app (DerivedCategory.Q.obj P) =
      α.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
    change (Localization.liftNatTrans _ _ _ _ _ _ c.hom).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj P)) = _
    rw [Localization.liftNatTrans_app]
    simp only [Localization.Lifting.iso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      Category.id_comp, Category.comp_id, c, Iso.trans_hom, NatTrans.comp_app,
      Functor.leftUnitor_hom_app, b, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.map_comp, eh, NatTrans.mapHomotopyCategory_app,
      Functor.mapHomotopyCategoryIdIso_hom_app_eq_id,
      Category.comp_id]
    erw [DerivedCategory.Qh.map_id]
    erw [Category.comp_id, Category.comp_id, Category.comp_id]
    rfl
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  intro X
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  exact (hd' P).trans (hd P).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma derivedAssoc
    {C₀ C₁ C₂ C₃ : Type u} [Category.{v'} C₀] [Category.{v'} C₁]
    [Category.{v'} C₂] [Category.{v'} C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    (A : C₀ ⥤ C₁) (B : C₁ ⥤ C₂) (C : C₂ ⥤ C₃)
    (D : C₁ ⥤ C₃) (E : C₀ ⥤ C₂) (F : C₀ ⥤ C₃)
    [A.Additive] [B.Additive] [C.Additive] [D.Additive] [E.Additive] [F.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    [PreservesFiniteLimits C] [PreservesFiniteColimits C]
    [PreservesFiniteLimits D] [PreservesFiniteColimits D]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e₁ : B ⋙ C ≅ D) (e₂ : A ⋙ B ≅ E) (e₃ : A ⋙ D ≅ F) (e₄ : E ⋙ C ≅ F)
    (hr : Functor.isoWhiskerLeft A e₁ ≪≫ e₃ =
      (Functor.associator A B C).symm ≪≫ Functor.isoWhiskerRight e₂ C ≪≫ e₄) :
    Functor.isoWhiskerLeft A.mapDerivedCategory
        ((Functor.mapDerivedCategoryCompIso B C).symm ≪≫
          Functor.mapDerivedCategoryNatIso e₁) ≪≫
      ((Functor.mapDerivedCategoryCompIso A D).symm ≪≫
        Functor.mapDerivedCategoryNatIso e₃) =
    (Functor.associator A.mapDerivedCategory B.mapDerivedCategory
        C.mapDerivedCategory).symm ≪≫
      Functor.isoWhiskerRight
        ((Functor.mapDerivedCategoryCompIso A B).symm ≪≫
          Functor.mapDerivedCategoryNatIso e₂) C.mapDerivedCategory ≪≫
      ((Functor.mapDerivedCategoryCompIso E C).symm ≪≫
        Functor.mapDerivedCategoryNatIso e₄) := by
  have hassoc : Functor.associator A B C = Iso.refl _ := by ext; rfl
  erw [hassoc, Iso.refl_symm, Iso.refl_trans] at hr
  have hh := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom) hr
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hh
  have h₁ := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft A e₁
  have h₂ := Functor.mapDerivedCategoryNatIso_isoWhiskerRight e₂ C
  have hA := Functor.mapDerivedCategoryCompIso_assoc A B C
  apply Iso.ext
  ext K
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso A (B ⋙ C)).hom.app K ≫
    (Functor.mapDerivedCategoryCompIso B C).hom.app (A.mapDerivedCategory.obj K))).1
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app]
  simp only [Functor.map_comp, Category.id_comp, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  have h₁' := congr_app h₁ K
  have h₂' := congr_app h₂ K
  have hA' := congr_app hA K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h₁' h₂' hA'
  erw [← reassoc_of% h₁']
  erw [reassoc_of% hA']
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  erw [← reassoc_of% h₂']
  simp only [Iso.hom_inv_id_app_assoc]
  exact congr_app hh K

section
variable {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type u}
  [Category.{v'} C₀] [Category.{v'} C₁] [Category.{v'} C₂] [Category.{v'} C₃]
  [Category.{v'} D₀] [Category.{v'} D₁] [Category.{v'} D₂] [Category.{v'} D₃]
  (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) (Q₃ : C₃ ⥤ D₃)
  (L₀₁ : C₀ ⥤ C₁) (L₁₂ : C₁ ⥤ C₂) (L₂₃ : C₂ ⥤ C₃)
  (L₀₂ : C₀ ⥤ C₂) (L₁₃ : C₁ ⥤ C₃) (L₀₃ : C₀ ⥤ C₃)
  (R₀₁ : D₀ ⥤ D₁) (R₁₂ : D₁ ⥤ D₂) (R₂₃ : D₂ ⥤ D₃)
  (R₀₂ : D₀ ⥤ D₂) (R₁₃ : D₁ ⥤ D₃) (R₀₃ : D₀ ⥤ D₃)
  (c₀₁ : Q₀ ⋙ R₀₁ ≅ L₀₁ ⋙ Q₁) (c₁₂ : Q₁ ⋙ R₁₂ ≅ L₁₂ ⋙ Q₂)
  (c₂₃ : Q₂ ⋙ R₂₃ ≅ L₂₃ ⋙ Q₃) (c₀₂ : Q₀ ⋙ R₀₂ ≅ L₀₂ ⋙ Q₂)
  (c₁₃ : Q₁ ⋙ R₁₃ ≅ L₁₃ ⋙ Q₃) (c₀₃ : Q₀ ⋙ R₀₃ ≅ L₀₃ ⋙ Q₃)
  (a₀₁₂ : L₀₁ ⋙ L₁₂ ≅ L₀₂) (a₁₂₃ : L₁₂ ⋙ L₂₃ ≅ L₁₃)
  (a₀₂₃ : L₀₂ ⋙ L₂₃ ≅ L₀₃) (a₀₁₃ : L₀₁ ⋙ L₁₃ ≅ L₀₃)
  (b₀₁₂ : R₀₁ ⋙ R₁₂ ≅ R₀₂) (b₁₂₃ : R₁₂ ⋙ R₂₃ ≅ R₁₃)
  (b₀₂₃ : R₀₂ ⋙ R₂₃ ≅ R₀₃) (b₀₁₃ : R₀₁ ⋙ R₁₃ ≅ R₀₃)
  (hb₀₁₂ : ∀ X, b₀₁₂.hom.app (Q₀.obj X) = R₁₂.map (c₀₁.hom.app X) ≫
    c₁₂.hom.app (L₀₁.obj X) ≫ Q₂.map (a₀₁₂.hom.app X) ≫ c₀₂.inv.app X)
  (hb₁₂₃ : ∀ X, b₁₂₃.hom.app (Q₁.obj X) = R₂₃.map (c₁₂.hom.app X) ≫
    c₂₃.hom.app (L₁₂.obj X) ≫ Q₃.map (a₁₂₃.hom.app X) ≫ c₁₃.inv.app X)
  (hb₀₂₃ : ∀ X, b₀₂₃.hom.app (Q₀.obj X) = R₂₃.map (c₀₂.hom.app X) ≫
    c₂₃.hom.app (L₀₂.obj X) ≫ Q₃.map (a₀₂₃.hom.app X) ≫ c₀₃.inv.app X)
  (hb₀₁₃ : ∀ X, b₀₁₃.hom.app (Q₀.obj X) = R₁₃.map (c₀₁.hom.app X) ≫
    c₁₃.hom.app (L₀₁.obj X) ≫ Q₃.map (a₀₁₃.hom.app X) ≫ c₀₃.inv.app X)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include hb₀₁₂ hb₁₂₃ hb₀₂₃ hb₀₁₃ in
private lemma transport_assoc (X : C₀)
    (ha : L₂₃.map (a₀₁₂.hom.app X) ≫ a₀₂₃.hom.app X =
      a₁₂₃.hom.app (L₀₁.obj X) ≫ a₀₁₃.hom.app X) :
    R₂₃.map (b₀₁₂.hom.app (Q₀.obj X)) ≫ b₀₂₃.hom.app (Q₀.obj X) =
      b₁₂₃.hom.app (R₀₁.obj (Q₀.obj X)) ≫ b₀₁₃.hom.app (Q₀.obj X) := by
  have hn := b₁₂₃.hom.naturality (c₀₁.hom.app X)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [hb₀₁₃, ← reassoc_of% hn, hb₁₂₃, hb₀₁₂, hb₀₂₃]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  erw [R₂₃.map_id, Category.id_comp]
  have hn' := c₂₃.hom.naturality (a₀₁₂.hom.app X)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn'
  rw [reassoc_of% hn']
  simp only [← Functor.map_comp_assoc, ha]
end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma derived_unit_fac {C : Type u} [Category.{v'} C] [Abelian C] [HasDerivedCategory C]
    (R : C ⥤ C) [R.Additive] [Limits.PreservesFiniteLimits R]
    [Limits.PreservesFiniteColimits R] (r : R ≅ 𝟭 C) (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryNatIso r ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app
        (DerivedCategory.Q.obj P) =
      R.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex r.hom (.up ℤ)).app P) := by
  have hid : (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj P) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app P := by
    have h := Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj C
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
    rw [Functor.mapDerivedCategoryFactorsh_hom_app] at h
    dsimp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
      Functor.mapHomotopyCategoryFactors] at h
    erw [(𝟭 C).mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
      Category.comp_id, Category.comp_id, Category.id_comp] at h
    exact h
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  rw [hid]
  exact Functor.mapDerivedCategoryNatIso_fac r P

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma unitMate_on_complex {C : Type u} [Category.{v'} C] [Abelian C] [HasDerivedCategory C]
    (L R : C ⥤ C) [L.Additive] [R.Additive]
    [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
    (adj : L ⊣ R) (r : R ≅ 𝟭 C) (e₀ : L ≅ 𝟭 C)
    (hu : ∀ X, adj.unit.app X ≫ R.map (e₀.hom.app X) ≫ r.hom.app X = 𝟙 X)
    (LD : DerivedCategory C ⥤ DerivedCategory C) (d : LD ⊣ R.mapDerivedCategory)
    (e : LD ≅ 𝟭 _) (P : CochainComplex C ℤ)
    (c : LD.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P))
    (he : e.hom.app (DerivedCategory.Q.obj P) = c ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e₀.hom (.up ℤ)).app P))
    (hn : d.unit.app (DerivedCategory.Q.obj P) ≫ R.mapDerivedCategory.map c ≫
      R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P)) :
    d.unit.app (DerivedCategory.Q.obj P) ≫
      R.mapDerivedCategory.map (e.hom.app (DerivedCategory.Q.obj P)) ≫
      (Functor.mapDerivedCategoryNatIso r ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app
        (DerivedCategory.Q.obj P) = 𝟙 _ := by
  rw [he, Functor.map_comp, derived_unit_fac, Category.assoc]
  have hnat := R.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex e₀.hom (.up ℤ)).app P)
  dsimp only [Functor.comp_map] at hnat
  erw [reassoc_of% hnat]
  erw [reassoc_of% hn]
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hh : (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
      (R.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e₀.hom (.up ℤ)).app P) ≫
      (NatTrans.mapHomologicalComplex r.hom (.up ℤ)).app P = 𝟙 P := by
    ext n
    exact hu (P.X n)
  rw [hh]
  exact DerivedCategory.Q.map_id P

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma derived_unit_mate {C : Type u} [Category.{v'} C] [Abelian C] [HasDerivedCategory C]
    (R : C ⥤ C) [R.Additive] [Limits.PreservesFiniteLimits R]
    [Limits.PreservesFiniteColimits R] (r : R ≅ 𝟭 C)
    (LD : DerivedCategory C ⥤ DerivedCategory C) (d : LD ⊣ R.mapDerivedCategory)
    (e : LD ≅ 𝟭 _) (P₀ : CochainComplex C ℤ → Prop)
    (hres : ∀ P, ∃ (K : CochainComplex C ℤ) (s : K ⟶ P), P₀ K ∧ QuasiIso s)
    (hn : ∀ P, P₀ P → d.unit.app (DerivedCategory.Q.obj P) ≫
      R.mapDerivedCategory.map (e.hom.app (DerivedCategory.Q.obj P)) ≫
      (Functor.mapDerivedCategoryNatIso r ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app
        (DerivedCategory.Q.obj P) = 𝟙 _) :
    e = Adjunction.leftAdjointIdIso d
      (Functor.mapDerivedCategoryNatIso r ≪≫ Functor.mapDerivedCategoryIdIso C) := by
  let rd := Functor.mapDerivedCategoryNatIso r ≪≫ Functor.mapDerivedCategoryIdIso C
  let τ := conjugateEquiv (Adjunction.id : (𝟭 (DerivedCategory C)) ⊣ 𝟭 _) d e.hom
  have ht (X : DerivedCategory C) : τ.app X = d.unit.app X ≫
      R.mapDerivedCategory.map (e.hom.app X) := by
    have h := unit_conjugateEquiv
      (Adjunction.id : (𝟭 (DerivedCategory C)) ⊣ 𝟭 _) d e.hom X
    simpa only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj, Category.id_comp] using h
  apply Iso.ext
  apply (conjugateEquiv (Adjunction.id : (𝟭 (DerivedCategory C)) ⊣ 𝟭 _) d).injective
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom]
  apply (cancel_mono rd.hom).1
  rw [Iso.inv_hom_id]
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro P
  obtain ⟨K, s, hK, hs⟩ := hres P
  have : QuasiIso s := hs
  apply (cancel_epi (DerivedCategory.Q.map s)).1
  have hnat := (τ ≫ rd.hom).naturality (DerivedCategory.Q.map s)
  dsimp only [Functor.id_map] at hnat
  change DerivedCategory.Q.map s ≫ (τ ≫ rd.hom).app _ = _
  rw [hnat]
  have hk : (τ ≫ rd.hom).app (DerivedCategory.Q.obj K) = 𝟙 _ := by
    simpa only [NatTrans.comp_app, ht, Category.assoc] using hn K hK
  rw [hk]
  simp only [NatTrans.id_app, Category.id_comp]
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma derived_comp_unit {C : Type u} [Category.{v'} C] [Abelian C] [HasDerivedCategory C]
    (R : C ⥤ C) [R.Additive] [Limits.PreservesFiniteLimits R]
    [Limits.PreservesFiniteColimits R] (r : R ≅ 𝟭 C) (a : R ⋙ R ≅ R)
    (ha : a = Functor.isoWhiskerLeft R r ≪≫ Functor.rightUnitor R) :
    (Functor.mapDerivedCategoryCompIso R R).symm ≪≫
        Functor.mapDerivedCategoryNatIso a =
      Functor.isoWhiskerLeft R.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso r ≪≫ Functor.mapDerivedCategoryIdIso C) ≪≫
        Functor.rightUnitor R.mapDerivedCategory := by
  subst a
  have hr : Functor.rightUnitor R = Iso.refl R := rfl
  erw [hr, Iso.trans_refl]
  apply Iso.ext
  apply (cancel_epi (Functor.mapDerivedCategoryCompIso R R).hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_trans ]
  have h := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft R r
  have hu := Functor.mapDerivedCategoryCompIso_comp_id R
  have hrd : R.mapDerivedCategory.rightUnitor.hom = 𝟙 R.mapDerivedCategory := rfl
  erw [hrd, Category.comp_id]
  rw [← reassoc_of% h, hu]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma transport_diagonal {C D : Type u} [Category.{v'} C] [Category.{v'} D]
    (Q : C ⥤ D) (L : C ⥤ C) (R : D ⥤ D) (e : L ≅ 𝟭 C)
    (a : L ⋙ L ≅ L) (b : R ⋙ R ≅ R) (c : Q ⋙ R ≅ L ⋙ Q)
    (hR : R = 𝟭 D)
    (hc : HEq c (Q.rightUnitor ≪≫ Q.leftUnitor.symm ≪≫
      Functor.isoWhiskerRight e.symm Q))
    (ha : ∀ X, a.hom.app X = L.map (e.hom.app X))
    (hb : ∀ X, b.hom.app (Q.obj X) = R.map (c.hom.app X) ≫
      c.hom.app (L.obj X) ≫ Q.map (a.hom.app X) ≫ c.inv.app X)
    (X : C) : HEq (b.hom.app (Q.obj X)) (𝟙 (Q.obj X)) := by
  subst R
  have hc' := eq_of_heq hc
  rw [hc'] at hb
  have h := hb X
  have he : L.map (e.hom.app X) = e.hom.app (L.obj X) := by
    apply (cancel_mono (e.hom.app X)).1
    exact e.hom.naturality (e.hom.app X)
  simp only [ha, he, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.id_map, Category.id_comp, Category.comp_id] at h
  erw [Category.id_comp, Category.id_comp, Category.comp_id] at h
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app] at h
  erw [Category.comp_id] at h
  rw [← Q.map_comp, Iso.inv_hom_id_app, Q.map_id] at h
  exact heq_of_eq h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma left_unit_from_diagonal {C D : Type u} [Category.{v'} C] [Category.{v'} D]
    (R : C ⥤ C) (F : C ⥤ D) (a : R ⋙ R ≅ R) (b : R ⋙ F ≅ F)
    (hR : R = 𝟭 C) (hd : ∀ X, HEq (a.hom.app X) (𝟙 X))
    (hc : ∀ X, F.map (a.hom.app X) ≫ b.hom.app X =
      b.hom.app (R.obj X) ≫ b.hom.app X) :
    HEq b (Functor.leftUnitor F) := by
  subst R
  apply heq_of_eq
  apply Iso.ext
  ext X
  have h := hc X
  rw [eq_of_heq (hd X)] at h
  erw [F.map_id, Category.id_comp] at h
  apply (cancel_mono (b.hom.app X)).1
  exact h.symm.trans (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma right_unit_from_diagonal {C D : Type u} [Category.{v'} C] [Category.{v'} D]
    (F : C ⥤ D) (R : D ⥤ D) (a : R ⋙ R ≅ R) (b : F ⋙ R ≅ F)
    (hR : R = 𝟭 D) (hd : ∀ X, HEq (a.hom.app X) (𝟙 X))
    (hc : ∀ X, R.map (b.hom.app X) ≫ b.hom.app X =
      a.hom.app (F.obj X) ≫ b.hom.app X) :
    HEq b (Functor.rightUnitor F) := by
  subst R
  apply heq_of_eq
  apply Iso.ext
  ext X
  have h := hc X
  rw [eq_of_heq (hd (F.obj X))] at h
  erw [Category.id_comp] at h
  apply (cancel_mono (b.hom.app X)).1
  exact h.trans (Category.id_comp _).symm

namespace AlgebraicGeometry.Scheme
open scoped ChangeOfRings
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma restrictAssoc (T : Scheme.{u})
    {R S V W : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : V ⟶ W)
    (d : R ⟶ V) (e : S ⟶ W) (f : R ⟶ W)
    (hab : a ≫ b = d) (hbc : b ≫ c = e)
    (hdc : d ≫ c = f) (hae : a ≫ e = f) :
    Functor.isoWhiskerLeft (pbcRestrict c) (pbcRestrictComp a b d hab) ≪≫
      pbcRestrictComp d c f hdc =
    (Functor.associator (pbcRestrict c) (pbcRestrict b) (pbcRestrict a)).symm ≪≫
      Functor.isoWhiskerRight (pbcRestrictComp b c e hbc) (pbcRestrict a) ≪≫
      pbcRestrictComp a e f hae := by
  apply Iso.ext
  ext M U x
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Category.id_comp]
  dsimp only [SheafOfModules.comp_val, NatTrans.comp_app, ModuleCat.comp_apply]
  change ((pbcRestrictComp d c f hdc).hom.app M).val.app U
      (((pbcRestrictComp a b d hab).hom.app ((pbcRestrict c).obj M)).val.app U x) = _
  erw [(pbcRestrictComp_exists d c f hdc).exists.choose_spec,
    (pbcRestrictComp_exists a b d hab).exists.choose_spec]
  change x = _
  symm
  change ((pbcRestrictComp a e f hae).hom.app M).val.app U
    (((pbcRestrictComp b c e hbc).hom.app M).val.app U x) = x
  erw [(pbcRestrictComp_exists a e f hae).exists.choose_spec]
  exact (pbcRestrictComp_exists b c e hbc).exists.choose_spec M U x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma pbc_tensor_smul (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules T R) (U : T.ProEtᵒᵖ) (r : S.obj.obj U) (x : M.val.obj U) :
    pbcTensorSection φ M U r x = r • pbcTensorSection φ M U 1 x := by
  let P := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M
  let η := PresheafOfModules.toSheafify.{u + 1, u, u + 1, u + 1} (𝟙 ((adicLisseForget T).obj S).obj)
    (CategoryTheory.toSheafify (ProEt.topology T) P.presheaf)
  let q : SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M ⟶ (pbcExtend φ).obj M :=
    eqToHom ((pbcExtensionExistence φ).choose_spec.choose M).symm
  have hη := (η.app U).hom.map_smul r
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
  have hq := (q.val.app U).hom.map_smul r
    ((η.app U) ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  change _ = r • _ at hη hq
  dsimp only [pbcTensorSection, completedAdicChangeTensor]
  change (q.val.app U) ((η.app U) (r ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
    r • (q.val.app U) ((η.app U)
      ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  calc
    _ = (q.val.app U) ((η.app U)
        (r • ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) := by
      congr 2
      symm
      exact (ModuleCat.ExtendScalars.smul_tmul (φ.hom.app U).hom r 1 x).trans
        (by rw [mul_one])
    _ = (q.val.app U) (r • ((η.app U)
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) :=
      congrArg (q.val.app U) hη
    _ = _ := hq

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma ambient_unit_mate (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (φ : pbcAdicCompletion T (pbcIntegralDatum l E) ⟶
      pbcAdicCompletion T (pbcIntegralDatum l E)) (hφ : φ = 𝟙 _)
    (e₀ : pbcExtend φ ≅ 𝟭 _)
    (he₀ : ∀ (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))
      (U : T.ProEtᵒᵖ) (r : (pbcAdicCompletion T (pbcIntegralDatum l E)).obj.obj U)
      (x : M.val.obj U), (e₀.hom.app M).val.app U (pbcTensorSection φ M U r x) = r • x)
    (e : pbcDerivedExtend φ ≅ 𝟭 _)
    (he : ∀ P, e.hom.app (DerivedCategory.Q.obj P) = pbcComplexCounit φ P ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e₀.hom (.up ℤ)).app P)) :
    e = eqToIso (congrArg (fun a ↦ pbcDerivedExtend (X := T) a) hφ) ≪≫
      Adjunction.leftAdjointIdIso
        (pbcDerivedScalarAdjunction (𝟙 (pbcAdicCompletion T (pbcIntegralDatum l E))))
        (Functor.mapDerivedCategoryNatIso (pbcScalarRestrictId l E T) ≪≫
          Functor.mapDerivedCategoryIdIso
            (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))) := by
  subst φ
  let R := pbcAdicCompletion T (pbcIntegralDatum l E)
  erw [eqToIso_refl, Iso.refl_trans]
  let : CategoryTheory.EssentiallySmall.{u + 1} T.ProEt :=
    CategoryTheory.essentiallySmallSelf.{0, u, u + 1} _
  apply derived_unit_mate.{u + 2, u + 1, u + 2}
    (C := pbcModules T R) (pbcRestrict (𝟙 R)) (pbcScalarRestrictId l E T)
    (pbcDerivedExtend (𝟙 R)) (pbcDerivedScalarAdjunction (𝟙 R)) e
    (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology T) (R := R))
  · intro P
    obtain ⟨K, s, hK, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
        (J := ProEt.topology T) (R := R) P
    exact ⟨K, s, hK, hs⟩
  · intro P hP
    apply unitMate_on_complex (pbcExtend (𝟙 R)) (pbcRestrict (𝟙 R))
      (pbcScalarAdjunction (𝟙 R)) (pbcScalarRestrictId l E T) e₀ ?_
      (pbcDerivedExtend (𝟙 R)) (pbcDerivedScalarAdjunction (𝟙 R)) e P
      (pbcComplexCounit (𝟙 R) P) (he P)
      ((pbcDerivedScalarAdjunction_exists (𝟙 R)).exists.choose_spec P hP)
    intro M
    ext U x
    change ((pbcScalarRestrictId l E T).hom.app M).val.app U
      ((e₀.hom.app M).val.app U
        (((pbcScalarAdjunction (𝟙 R)).unit.app M).val.app U x)) = x
    erw [(pbcScalarAdjunction_exists (𝟙 R)).exists.choose_spec M U x, he₀, one_smul]
    simpa only [pbcScalarRestrictId] using
      (pbcScalarRestrictId_exists l E T).exists.choose_spec M U x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma restrict_diagonal (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (h : (𝟙 (pbcAdicCompletion T (pbcIntegralDatum l E))) ≫ 𝟙 _ = 𝟙 _) :
    pbcRestrictComp (𝟙 _) (𝟙 _) (𝟙 _) h =
      Functor.isoWhiskerLeft (pbcRestrict (𝟙 _)) (pbcScalarRestrictId l E T) ≪≫
        Functor.rightUnitor (pbcRestrict (𝟙 _)) := by
  apply Iso.ext
  ext M U x
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  erw [Category.comp_id]
  change ((pbcRestrictComp _ _ _ h).hom.app M).val.app U x =
    ((pbcScalarRestrictId l E T).hom.app ((pbcRestrict (𝟙 _)).obj M)).val.app U x
  erw [(pbcRestrictComp_exists _ _ _ h).exists.choose_spec M U x]
  symm
  simpa only [pbcScalarRestrictId] using
    (pbcScalarRestrictId_exists l E T).exists.choose_spec
      ((pbcRestrict (𝟙 _)).obj M) U x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma ambient_diagonal (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (φ : pbcAdicCompletion T (pbcIntegralDatum l E) ⟶
      pbcAdicCompletion T (pbcIntegralDatum l E)) (hφ : φ = 𝟙 _)
    (e₀ : pbcExtend φ ≅ 𝟭 _)
    (he₀ : ∀ (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))
      (U : T.ProEtᵒᵖ) (r : (pbcAdicCompletion T (pbcIntegralDatum l E)).obj.obj U)
      (x : M.val.obj U), (e₀.hom.app M).val.app U (pbcTensorSection φ M U r x) = r • x)
    (e : pbcDerivedExtend φ ≅ 𝟭 _)
    (he : ∀ P, e.hom.app (DerivedCategory.Q.obj P) = pbcComplexCounit φ P ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e₀.hom (.up ℤ)).app P))
    (hcomp : φ ≫ φ = φ) (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction φ)
      (pbcDerivedScalarAdjunction φ) (pbcDerivedScalarAdjunction φ)
      (pbcDerivedRestrictComp φ φ φ hcomp)).hom.app K =
      (pbcDerivedExtend φ).map (e.hom.app K) := by
  have hu := ambient_unit_mate l E T φ hφ e₀ he₀ e he
  subst φ
  erw [eqToIso_refl, Iso.refl_trans] at hu
  rw [hu]
  have hd := derived_comp_unit (pbcRestrict (𝟙 _)) (pbcScalarRestrictId l E T)
    (pbcRestrictComp _ _ _ hcomp) (restrict_diagonal l E T hcomp)
  have hh := Adjunction.leftAdjointCompIso_id_comp
    (pbcDerivedScalarAdjunction (𝟙 (pbcAdicCompletion T (pbcIntegralDatum l E))))
    (pbcDerivedScalarAdjunction (𝟙 (pbcAdicCompletion T (pbcIntegralDatum l E))))
    (pbcDerivedRestrictComp _ _ _ hcomp)
    (Functor.mapDerivedCategoryNatIso (pbcScalarRestrictId l E T) ≪≫
      Functor.mapDerivedCategoryIdIso _) hd
  have hh' := congrArg (fun a ↦ a.hom.app K) hh
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hh'
  erw [Category.comp_id] at hh'
  exact hh'


attribute [local instance 3000] DivisionSemiring.to_moduleIsTorsionFree

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
private lemma pbc_level_comparison (E : Padic.FiniteCoefficientFields l Ω) (n : ℕ) :
    (pbcLevelConstantComparison T (pbcStageDatum.{u} l Ω E) n).hom =
      AdicCoefficients.constantComparison T
        ((PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) ⧸
          (pbcStageDatum.{u} l Ω E).ideal ^ (n + 1)) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings T (pbcStageDatum.{u} l Ω E)).obj (op n)).property
  change toSheafify _ _ ≫ (pbcLevelConstantComparison T _ n).hom.hom =
    toSheafify _ _ ≫ sheafifyMap _ _
  rw [← toSheafify_naturality]
  ext U b
  exact (pbcLevelConstantComparison_exists T (pbcStageDatum.{u} l Ω E) n).exists.choose_spec U b

private lemma pbc_finite_scalar_map (h : E ≤ F) (n : ℕ) :
    pbcFiniteScalarMap l Ω T h n =
      AdicCoefficients.coefficientMap T
        (pbcScalarQuotientMap l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
          (pbcFiniteFieldInclusion l Ω h) n) := by
  apply (cancel_epi (pbcLevelConstantComparison T (pbcStageDatum.{u} l Ω E) n).hom).1
  dsimp only [pbcFiniteScalarMap]
  rw [Iso.hom_inv_id_assoc, pbc_level_comparison, pbc_level_comparison]
  change (presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1}).map _ ≫
      (presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1}).map _ =
    (presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1}).map _ ≫
      (presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1}).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

private lemma pbc_completed_scalar_map (h : E ≤ F) :
    pbcCompletedScalarMap l Ω T h =
      pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) T := by
  apply (pbcCompletedScalarMap_exists l Ω T h).unique
  · exact (pbcCompletedScalarMap_exists l Ω T h).exists.choose_spec
  · intro n
    rw [pbc_finite_scalar_map]
    exact (pbcScalarCoefficientMap_exists l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T).exists.choose_spec n

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
  dsimp only [pbcAmbientScalarExtension]
  rw [pbc_completed_scalar_map]
  exact pbcEmbeddingAmbientTensor_preserves l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T _hdim _hl K

variable [IsNoetherian T] (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
  (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

omit [IsAlgClosure (Padic l) Ω] in
private lemma pbc_stage_isLocalization (E : Padic.FiniteCoefficientFields l Ω) :
    let := pbcIntegralTriangulated l (pbcFiniteField.{u} l Ω E) T hdim hl
    (pbcStageLocalization l Ω T E).IsLocalization
      (Rationalization.W (Submonoid.powers (pbcStageUniformizer.{u} l Ω E))
        (pbcIntegralStage l Ω T E)) := by
  let := pbcIntegralTriangulated l (pbcFiniteField.{u} l Ω E) T hdim hl
  exact ScalarLocalization.semilinear_localization_isLocalization _ _ _

/-- Restriction of the specified ambient tensor extension to the integral subcategories.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcIntegralScalarExtension (h : E ≤ F) :
    pbcIntegralStage l Ω T E ⥤
      pbcIntegralStage l Ω T F :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F))
    ((pbcStageInclusion l Ω T E) ⋙
      pbcAmbientScalarExtension l Ω T h)
    (pbcAmbientScalarExtension_preserves l Ω T h hdim hl)

private lemma pbc_integral_scalar_extension (h : E ≤ F) :
    pbcIntegralScalarExtension l Ω T hdim hl h =
      pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) T hdim hl := by
  simp only [pbcIntegralScalarExtension, pbcEmbeddingIntegralTensor,
    pbcAmbientScalarExtension, pbcEmbeddingAmbientTensor, pbc_completed_scalar_map]

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
  let := pbcIntegralTriangulated l (pbcFiniteField.{u} l Ω E) T hdim hl
  let Q := pbcStageLocalization l Ω T E
  let W := Rationalization.W (Submonoid.powers (pbcStageUniformizer.{u} l Ω E))
    (pbcIntegralStage l Ω T E)
  let : Q.IsLocalization W := pbc_stage_isLocalization l Ω T hdim hl E
  let B := pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T hdim hl
  have fac : Q ⋙ B = pbcIntegralScalarExtension l Ω T hdim hl h ⋙
      pbcStageLocalization l Ω T F := by
    rw [pbc_integral_scalar_extension]
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro K L f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    let : Fact (∃ m : ℕ, topologicalKrullDim T ≤ m) := ⟨hdim⟩
    let : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t)) := ⟨hl⟩
    exact (by
      simpa only [Category.comp_id, Category.id_comp, B, Q, Functor.comp_map] using
        (pbcScalarLocalization_naturality l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T f).symm)
  refine ⟨B, fac, ?_⟩
  intro B' hB'
  have he : Q ⋙ B' = Q ⋙ B := hB'.trans fac.symm
  let e : B' ≅ B := Localization.liftNatIso Q W (Q ⋙ B') (Q ⋙ B) B' B (eqToIso he)
  refine Functor.ext_of_iso e
    (fun K ↦ congrArg (fun J : pbcIntegralStage l Ω T E ⥤ pbcStageCategory l Ω T F ↦
      J.obj K.obj) he) ?_
  intro K
  change (Localization.liftNatTrans Q W (Q ⋙ B') (Q ⋙ B) B' B (eqToIso he).hom).app
    (Q.obj K.obj) = _
  rw [Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso, eqToHom_app]


/-- Raw rationalized tensor extension. Equal coefficient fields use identity literally.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcScalarExtension (h : E ≤ F) :
    pbcStageCategory l Ω T E ⥤
      pbcStageCategory l Ω T F :=
  by
    classical
    exact if e : E = F then e ▸ 𝟭 _ else
      (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose


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
private lemma pbc_completed_scalar_map_id (E : Padic.FiniteCoefficientFields l Ω) :
    pbcCompletedScalarMap l Ω T (le_refl E) =
      𝟙 (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)) := by
  rw [pbc_completed_scalar_map]
  have hi : pbcFiniteFieldInclusion.{u} l Ω (le_refl E) =
      AlgHom.id (Padic l) (pbcFiniteField.{u} l Ω E) := by
    ext x
    change (Shrink.algEquiv (Padic l) E.val).symm
      ((Shrink.algEquiv (Padic l) E.val) x) = x
    exact AlgEquiv.symm_apply_apply _ x
  rw [hi, pbcScalarCoefficientMap_id]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
  rw [pbc_completed_scalar_map_id]
  let R := pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)
  let adj := pbcScalarAdjunction (𝟙 R)
  let r := pbcScalarRestrictId l (pbcFiniteField.{u} l Ω E) T
  let e := Adjunction.leftAdjointIdIso adj r
  have he (M : pbcModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
      (e.hom.app M).val.app U (pbcTensorSection (𝟙 R) M U 1 x) = x := by
    have h := unit_conjugateEquiv (Adjunction.id : (𝟭 (pbcModules T R)) ⊣ 𝟭 _)
      adj e.hom M
    rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom] at h
    have hh := congrArg (fun f ↦ f.val.app U x) h
    change (r.inv.app M).val.app U x =
      (e.hom.app M).val.app U ((adj.unit.app M).val.app U x) at hh
    erw [(pbcScalarAdjunction_exists (𝟙 R)).exists.choose_spec M U x] at hh
    have hr := (pbcScalarRestrictId_exists l (pbcFiniteField.{u} l Ω E) T).exists.choose_spec
    have hrx : (r.inv.app M).val.app U x = x := by
      have hx := congrArg (fun f ↦ f.val.app U x) (r.inv_hom_id_app M)
      change (r.hom.app M).val.app U ((r.inv.app M).val.app U x) = x at hx
      have hy : (r.hom.app M).val.app U ((r.inv.app M).val.app U x) =
          (r.inv.app M).val.app U x := by
        simpa only [r, pbcScalarRestrictId] using hr M U ((r.inv.app M).val.app U x)
      exact hy.symm.trans hx
    exact hh.symm.trans hrx
  refine ⟨e, ?_, ?_⟩
  · intro M U r x
    rw [pbc_tensor_smul, map_smul, he]
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (adj.homEquiv M M).injective
    ext U x
    change (e'.hom.app M).val.app U ((adj.unit.app M).val.app U x) =
      (e.hom.app M).val.app U ((adj.unit.app M).val.app U x)
    erw [(pbcScalarAdjunction_exists (𝟙 R)).exists.choose_spec M U x]
    have hh := he' M U 1 x
    rw [one_smul] at hh
    exact hh.trans (he M U x).symm


/-- The section-normalized ordinary tensor unit.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcOrdinaryScalarUnit (E : Padic.FiniteCoefficientFields l Ω) :
    pbcExtend (pbcCompletedScalarMap l Ω T (le_refl E)) ≅
        𝟭 (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) :=
  (pbcOrdinaryScalarUnit_exists l Ω T E).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
                (pbcOrdinaryScalarUnit l Ω T E).hom (.up ℤ)).app P)
:= by
  let φ := pbcCompletedScalarMap l Ω T (le_refl E)
  let : (pbcDerivedExtend φ).IsLeftDerivedFunctor (pbcExtensionCounit φ)
      (HomotopyCategory.quasiIso (pbcModules T (pbcAdicCompletion T
        (pbcStageDatum.{u} l Ω E))) (.up ℤ)) := pbcDerivedExtension_universal φ
  obtain ⟨e, he, hu⟩ := derivedUnit (pbcExtend φ) (pbcOrdinaryScalarUnit l Ω T E)
    (pbcDerivedExtend φ) (pbcExtensionCounit φ)
  have hc (P : CochainComplex (pbcModules T (pbcAdicCompletion T
      (pbcStageDatum.{u} l Ω E))) ℤ) :
      pbcComplexCounit φ P =
        (pbcExtensionCounit φ).app ((HomotopyCategory.quotient _ _).obj P) := by
    exact complexCounit_eq (pbcExtend φ) (pbcDerivedExtend φ) (pbcExtensionCounit φ) P
  refine ⟨e, ?_, ?_⟩
  · intro P
    rw [hc]
    exact he P
  · intro e' he'
    apply hu e'
    intro P
    rw [← hc]
    exact he' P


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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma pbc_derived_restrict_assoc {H : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (k : F ≤ G) (j : G ≤ H) :
    Functor.isoWhiskerLeft (pbcDerivedRestrict (pbcCompletedScalarMap l Ω T j))
        (pbcDerivedRestrictComp (pbcCompletedScalarMap l Ω T h)
          (pbcCompletedScalarMap l Ω T k) (pbcCompletedScalarMap l Ω T (h.trans k))
          (pbcCompletedScalarMap_comp l Ω T h k)) ≪≫
      pbcDerivedRestrictComp (pbcCompletedScalarMap l Ω T (h.trans k))
        (pbcCompletedScalarMap l Ω T j)
        (pbcCompletedScalarMap l Ω T ((h.trans k).trans j))
        (pbcCompletedScalarMap_comp l Ω T (h.trans k) j) =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (pbcDerivedRestrictComp (pbcCompletedScalarMap l Ω T k)
          (pbcCompletedScalarMap l Ω T j) (pbcCompletedScalarMap l Ω T (k.trans j))
          (pbcCompletedScalarMap_comp l Ω T k j)) _ ≪≫
      pbcDerivedRestrictComp (pbcCompletedScalarMap l Ω T h)
        (pbcCompletedScalarMap l Ω T (k.trans j))
        (pbcCompletedScalarMap l Ω T (h.trans (k.trans j)))
        (pbcCompletedScalarMap_comp l Ω T h (k.trans j)) := by
  exact derivedAssoc
    (pbcRestrict (pbcCompletedScalarMap l Ω T j))
    (pbcRestrict (pbcCompletedScalarMap l Ω T k))
    (pbcRestrict (pbcCompletedScalarMap l Ω T h))
    (pbcRestrict (pbcCompletedScalarMap l Ω T (h.trans k)))
    (pbcRestrict (pbcCompletedScalarMap l Ω T (k.trans j)))
    (pbcRestrict (pbcCompletedScalarMap l Ω T (h.trans (k.trans j))))
    _ _ _ _
    (restrictAssoc T (pbcCompletedScalarMap l Ω T h)
      (pbcCompletedScalarMap l Ω T k) (pbcCompletedScalarMap l Ω T j)
      (pbcCompletedScalarMap l Ω T (h.trans k))
      (pbcCompletedScalarMap l Ω T (k.trans j))
      (pbcCompletedScalarMap l Ω T (h.trans (k.trans j)))
      (pbcCompletedScalarMap_comp l Ω T h k)
      (pbcCompletedScalarMap_comp l Ω T k j)
      (pbcCompletedScalarMap_comp l Ω T (h.trans k) j)
      (pbcCompletedScalarMap_comp l Ω T h (k.trans j)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma pbc_ambient_assoc {H : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (k : F ≤ G) (j : G ≤ H) (K : pbcAmbientStage l Ω T E) :
    (pbcAmbientScalarExtension l Ω T j).map
        ((pbcAmbientScalarAssociator l Ω T h k).hom.app K) ≫
      (pbcAmbientScalarAssociator l Ω T (h.trans k) j).hom.app K =
    (pbcAmbientScalarAssociator l Ω T k j).hom.app
        ((pbcAmbientScalarExtension l Ω T h).obj K) ≫
      (pbcAmbientScalarAssociator l Ω T h (k.trans j)).hom.app K := by
  have hh := Adjunction.leftAdjointCompIso_assoc
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T h))
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T k))
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T j))
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T (h.trans k)))
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T (k.trans j)))
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T ((h.trans k).trans j)))
    _ _ _ _ (pbc_derived_restrict_assoc l Ω T h k j)
  simpa only [pbcAmbientScalarAssociator, pbcAmbientScalarExtension, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] using
    (congrArg (fun e ↦ e.hom.app K) hh).symm

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma pbc_integral_assoc {H : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (k : F ≤ G) (j : G ≤ H) (K : pbcIntegralStage l Ω T E) :
    (pbcIntegralScalarExtension l Ω T hdim hl j).map
        ((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K) ≫
      (pbcIntegralScalarAssociator l Ω T hdim hl (h.trans k) j).hom.app K =
    (pbcIntegralScalarAssociator l Ω T hdim hl k j).hom.app
        ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) ≫
      (pbcIntegralScalarAssociator l Ω T hdim hl h (k.trans j)).hom.app K := by
  have ha (E F G : Padic.FiniteCoefficientFields l Ω) (h : E ≤ F) (k : F ≤ G)
      (K : pbcIntegralStage l Ω T E) :
      ((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K).hom =
        (pbcAmbientScalarAssociator l Ω T h k).hom.app K.obj :=
    congrArg (fun η ↦ η.app K)
      (pbcIntegralScalarAssociator_exists l Ω T hdim hl h k).exists.choose_spec
  apply ObjectProperty.hom_ext
  change (pbcAmbientScalarExtension l Ω T j).map
      (((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K).hom) ≫
      ((pbcIntegralScalarAssociator l Ω T hdim hl (h.trans k) j).hom.app K).hom =
    ((pbcIntegralScalarAssociator l Ω T hdim hl k j).hom.app
      ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K)).hom ≫
    ((pbcIntegralScalarAssociator l Ω T hdim hl h (k.trans j)).hom.app K).hom
  simp only [ha]
  exact pbc_ambient_assoc l Ω T h k j K.obj

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
  let := pbcIntegralTriangulated l (pbcFiniteField.{u} l Ω E) T hdim hl
  let Q := pbcStageLocalization l Ω T E
  let W := Rationalization.W (Submonoid.powers (pbcStageUniformizer.{u} l Ω E))
    (pbcIntegralStage l Ω T E)
  let : Q.IsLocalization W := pbc_stage_isLocalization l Ω T hdim hl E
  let B := pbcScalarExtension l Ω T hdim hl h ⋙ pbcScalarExtension l Ω T hdim hl k
  let B' := pbcScalarExtension l Ω T hdim hl (h.trans k)
  let c : Q ⋙ B ≅ Q ⋙ B' :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pbcScalarIntegralComparison l Ω T hdim hl h) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (pbcScalarIntegralComparison l Ω T hdim hl k) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pbcIntegralScalarAssociator l Ω T hdim hl h k) _ ≪≫
      (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k)).symm
  let e := Localization.liftNatIso Q W (Q ⋙ B) (Q ⋙ B') B B' c
  have he : ∀ K : pbcIntegralStage l Ω T E,
      e.hom.app ((pbcStageLocalization l Ω T E).obj K) =
        (pbcScalarExtension l Ω T hdim hl k).map
            ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K) ≫
          (pbcScalarIntegralComparison l Ω T hdim hl k).hom.app
            ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) ≫
          (pbcStageLocalization l Ω T G).map
            ((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K) ≫
          (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k)).inv.app K := by
    intro K
    change (Localization.liftNatTrans Q W (Q ⋙ B) (Q ⋙ B') B B' c.hom).app
      (Q.obj K) = _
    rw [Localization.liftNatTrans_app]
    simp only [c, Localization.Lifting.iso, Iso.refl_hom, Iso.refl_inv,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, NatTrans.id_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_obj, Category.id_comp, Category.comp_id]
    exact Category.id_comp _
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact (he' K.obj).trans (he K.obj).symm


/-- The scalar associator induced by tensor balancing, including the normalized units.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcScalarAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcScalarExtension l Ω T hdim hl h ⋙
        pbcScalarExtension l Ω T hdim hl k ≅
        pbcScalarExtension l Ω T hdim hl (h.trans k) :=
  (pbcScalarAssociator_exists l Ω T hdim hl h k).exists.choose

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
  exact transport_assoc
    (pbcStageLocalization l Ω T E) (pbcStageLocalization l Ω T F)
    (pbcStageLocalization l Ω T G) (pbcStageLocalization l Ω T H)
    (pbcIntegralScalarExtension l Ω T hdim hl h)
    (pbcIntegralScalarExtension l Ω T hdim hl k)
    (pbcIntegralScalarExtension l Ω T hdim hl j)
    (pbcIntegralScalarExtension l Ω T hdim hl (h.trans k))
    (pbcIntegralScalarExtension l Ω T hdim hl (k.trans j))
    (pbcIntegralScalarExtension l Ω T hdim hl (h.trans (k.trans j)))
    (pbcScalarExtension l Ω T hdim hl h)
    (pbcScalarExtension l Ω T hdim hl k)
    (pbcScalarExtension l Ω T hdim hl j)
    (pbcScalarExtension l Ω T hdim hl (h.trans k))
    (pbcScalarExtension l Ω T hdim hl (k.trans j))
    (pbcScalarExtension l Ω T hdim hl (h.trans (k.trans j)))
    (pbcScalarIntegralComparison l Ω T hdim hl h)
    (pbcScalarIntegralComparison l Ω T hdim hl k)
    (pbcScalarIntegralComparison l Ω T hdim hl j)
    (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k))
    (pbcScalarIntegralComparison l Ω T hdim hl (k.trans j))
    (pbcScalarIntegralComparison l Ω T hdim hl (h.trans (k.trans j)))
    (pbcIntegralScalarAssociator l Ω T hdim hl h k)
    (pbcIntegralScalarAssociator l Ω T hdim hl k j)
    (pbcIntegralScalarAssociator l Ω T hdim hl (h.trans k) j)
    (pbcIntegralScalarAssociator l Ω T hdim hl h (k.trans j))
    (pbcScalarAssociator l Ω T hdim hl h k)
    (pbcScalarAssociator l Ω T hdim hl k j)
    (pbcScalarAssociator l Ω T hdim hl (h.trans k) j)
    (pbcScalarAssociator l Ω T hdim hl h (k.trans j))
    (pbcScalarAssociator_exists l Ω T hdim hl h k).exists.choose_spec
    (pbcScalarAssociator_exists l Ω T hdim hl k j).exists.choose_spec
    (pbcScalarAssociator_exists l Ω T hdim hl (h.trans k) j).exists.choose_spec
    (pbcScalarAssociator_exists l Ω T hdim hl h (k.trans j)).exists.choose_spec
    K.obj (pbc_integral_assoc l Ω T hdim hl h k j K.obj)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma pbc_integral_diagonal (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω T E) :
    (pbcIntegralScalarAssociator l Ω T hdim hl (le_refl E) (le_refl E)).hom.app K =
      (pbcIntegralScalarExtension l Ω T hdim hl (le_refl E)).map
        ((pbcIntegralScalarUnit l Ω T hdim hl E).hom.app K) := by
  have ha := congrArg (fun η ↦ η.app K)
    (pbcIntegralScalarAssociator_exists l Ω T hdim hl (le_refl E)
      (le_refl E)).exists.choose_spec
  have he := congrArg (fun η ↦ η.app K)
    (pbcIntegralScalarUnit_exists l Ω T hdim hl E).exists.choose_spec
  apply ObjectProperty.hom_ext
  change (((pbcIntegralScalarAssociator l Ω T hdim hl (le_refl E)
      (le_refl E)).hom.app K).hom) =
    (pbcAmbientScalarExtension l Ω T (le_refl E)).map
      (((pbcIntegralScalarUnit l Ω T hdim hl E).hom.app K).hom)
  change ((pbcIntegralScalarAssociator l Ω T hdim hl (le_refl E)
    (le_refl E)).hom.app K).hom =
      (pbcAmbientScalarAssociator l Ω T (le_refl E) (le_refl E)).hom.app K.obj at ha
  change ((pbcIntegralScalarUnit l Ω T hdim hl E).hom.app K).hom =
    (pbcAmbientScalarUnit l Ω T E).hom.app K.obj at he
  erw [ha, he]
  exact ambient_diagonal l (pbcFiniteField.{u} l Ω E) T
    (pbcCompletedScalarMap l Ω T (le_refl E)) (pbc_completed_scalar_map_id l Ω T E)
    (pbcOrdinaryScalarUnit l Ω T E)
    (pbcOrdinaryScalarUnit_exists l Ω T E).exists.choose_spec
    (pbcAmbientScalarUnit l Ω T E)
    (pbcAmbientScalarUnit_exists l Ω T E).exists.choose_spec
    (pbcCompletedScalarMap_comp l Ω T (le_refl E) (le_refl E)) K.obj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma pbc_scalar_diagonal (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcStageCategory l Ω T E) :
    HEq ((pbcScalarAssociator l Ω T hdim hl (le_refl E) (le_refl E)).hom.app K)
      (𝟙 K) := by
  exact transport_diagonal (pbcStageLocalization l Ω T E)
    (pbcIntegralScalarExtension l Ω T hdim hl (le_refl E))
    (pbcScalarExtension l Ω T hdim hl (le_refl E))
    (pbcIntegralScalarUnit l Ω T hdim hl E)
    (pbcIntegralScalarAssociator l Ω T hdim hl (le_refl E) (le_refl E))
    (pbcScalarAssociator l Ω T hdim hl (le_refl E) (le_refl E))
    (pbcScalarIntegralComparison l Ω T hdim hl (le_refl E))
    (by simp [pbcScalarExtension])
    ((pbcScalarIntegralComparison_exists l Ω T hdim hl (le_refl E)).exists.choose_spec.1
      rfl)
    (pbc_integral_diagonal l Ω T hdim hl E)
    (pbcScalarAssociator_exists l Ω T hdim hl (le_refl E) (le_refl E)).exists.choose_spec
    K.obj

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
  refine ⟨by simp [pbcScalarExtension], ?_, ?_⟩
  · exact left_unit_from_diagonal
      (pbcScalarExtension l Ω T hdim hl (le_refl E))
      (pbcScalarExtension l Ω T hdim hl h)
      (pbcScalarAssociator l Ω T hdim hl (le_refl E) (le_refl E))
      (pbcScalarAssociator l Ω T hdim hl (le_refl E) h)
      (by simp [pbcScalarExtension]) (pbc_scalar_diagonal l Ω T hdim hl E)
      (pbcScalarAssociator_cocycle l Ω T hdim hl (le_refl E) (le_refl E) h)
  · exact right_unit_from_diagonal
      (pbcScalarExtension l Ω T hdim hl h)
      (pbcScalarExtension l Ω T hdim hl (le_refl F))
      (pbcScalarAssociator l Ω T hdim hl (le_refl F) (le_refl F))
      (pbcScalarAssociator l Ω T hdim hl h (le_refl F))
      (by simp [pbcScalarExtension]) (pbc_scalar_diagonal l Ω T hdim hl F)
      (pbcScalarAssociator_cocycle l Ω T hdim hl h (le_refl F) (le_refl F))

/-- Rationalized tensor extension is additive.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: tensor extension is additive on complexes and derived morphisms. The
localization formula sends sums of fractions to sums; identity fields are
literal identity functors, which are additive as well. -/
@[instance] theorem pbcScalarExtension_additive (h : E ≤ F) :
    (pbcScalarExtension l Ω T hdim hl h).Additive := by
  let := pbcIntegralTriangulated l (pbcFiniteField.{u} l Ω E) T hdim hl
  let := pbc_stage_isLocalization l Ω T hdim hl E
  have : (pbcDerivedRestrict (pbcCompletedScalarMap l Ω T h)).Additive := by
    dsimp only [pbcDerivedRestrict]
    infer_instance
  have : (pbcAmbientScalarExtension l Ω T h).Additive :=
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T h)).left_adjoint_additive
  have : (pbcIntegralScalarExtension l Ω T hdim hl h).Additive := by
    dsimp only [pbcIntegralScalarExtension]
    infer_instance
  have : (pbcStageLocalization l Ω T E ⋙
      pbcScalarExtension l Ω T hdim hl h).Additive :=
    Functor.additive_of_iso (pbcScalarIntegralComparison l Ω T hdim hl h).symm
  exact (Localization.functor_additive_iff (pbcStageLocalization l Ω T E)
    (Rationalization.W (Submonoid.powers (pbcStageUniformizer.{u} l Ω E))
      (pbcIntegralStage l Ω T E)) _).2 inferInstance

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

