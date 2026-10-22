/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.StrictQuotientDiagonalPresentation
import all Sheaf.Paper.ConstantSequenceModuleEquivalence
import Sheaf.CategoryTheory.SystemEvaluationTopos
import all Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.SystemScalarCoherence
import all Sheaf.Paper.ConstantCompletionEquivalence
import all Sheaf.CategoryTheory.SystemRingedSequenceSite

/-! # The ordinary flat model for strict quotient reduction

Source: Stacks Project, Tags 03DA, 03EK, 0940 and 06YN.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 2000] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [CommRing A] (I : Ideal A)

private def quotientSequenceMap : strictDiagonalRing J A ⟶ strictQuotientRing J A I where
  hom :=
    { app := fun X ↦ (quotient J A I X.unop.1).hom.app (op X.unop.2)
      naturality := by
        intro X Y f
        change (constant J A).obj.map f.unop.2.op ≫
            (quotient J A I Y.unop.1).hom.app (op Y.unop.2) =
          (quotient J A I X.unop.1).hom.app (op X.unop.2) ≫
            ((finiteSystem J A I).map f.unop.1.op).hom.app (op X.unop.2) ≫
              (finite J A I Y.unop.1).obj.map f.unop.2.op
        rw [(quotient J A I Y.unop.1).hom.naturality]
        have h := congrArg (fun t ↦ t.hom.app (op X.unop.2))
          ((quotientCone J A I).w f.unop.1.op)
        change (quotient J A I X.unop.1).hom.app (op X.unop.2) ≫
          ((finiteSystem J A I).map f.unop.1.op).hom.app (op X.unop.2) =
            (quotient J A I Y.unop.1).hom.app (op X.unop.2) at h
        rw [← Category.assoc, h] }

private def ordinaryDiagonal : Mod (constant J A) ⥤ Mod (strictDiagonalRing J A) :=
  constantTower J (constant J A) ⋙ (systemTowerEquivalence (constant J A)).inverse ⋙
    (SheafOfModules.strictSystemSequenceEquivalence.{u, u, u} (J := J)
      ((Functor.const ℕᵒᵖ).obj (constant J A))).functor

private theorem ordinaryDiagonal_objects (M : Mod (constant J A)) (n : ℕ) (U : Cᵒᵖ) :
    HEq (((ordinaryDiagonal J A).obj M).val.obj (op (n, U.unop))) (M.val.obj U) := by
  rfl

private theorem ordinaryDiagonal_restrictions (M : Mod (constant J A))
    {X Y : (ℕ × C)ᵒᵖ} (f : X ⟶ Y) :
    HEq (((ordinaryDiagonal J A).obj M).val.map f) (M.val.map f.unop.2.op) := by
  apply heq_of_eq
  ext x
  change M.val.map f.unop.2.op x = _
  rfl

private instance ordinaryDiagonal_additive : (ordinaryDiagonal J A).Additive := by
  constructor
  intro M N f g
  ext X x
  rfl

private theorem ordinaryDiagonal_maps {M N : Mod (constant J A)} (f : M ⟶ N)
    (n : ℕ) (U : Cᵒᵖ) :
    HEq (((ordinaryDiagonal J A).map f).val.app (op (n, U.unop))) (f.val.app U) := by
  rfl

private def ordinaryDiagonalTowerIso :
    ordinaryDiagonal J A ⋙
      (SheafOfModules.strictSystemSequenceEquivalence.{u, u, u} (J := J)
        ((Functor.const ℕᵒᵖ).obj (constant J A))).inverse ⋙
      (systemTowerEquivalence (constant J A)).functor ≅ constantTower J (constant J A) :=
  Functor.isoWhiskerLeft (constantTower J (constant J A))
    ((Functor.isoWhiskerLeft (systemTowerEquivalence (constant J A)).inverse
      (Functor.isoWhiskerRight
        (SheafOfModules.strictSystemSequenceEquivalence.{u, u, u} (J := J)
          ((Functor.const ℕᵒᵖ).obj (constant J A))).unitIso.symm
        (systemTowerEquivalence (constant J A)).functor)) ≪≫
      (systemTowerEquivalence (constant J A)).counitIso)

private instance ordinaryDiagonal_limits : PreservesFiniteLimits (ordinaryDiagonal J A) := by
  let E := (SheafOfModules.strictSystemSequenceEquivalence.{u, u, u} (J := J)
    ((Functor.const ℕᵒᵖ).obj (constant J A))).symm.trans
      (systemTowerEquivalence (constant J A))
  have : PreservesFiniteLimits (ordinaryDiagonal J A ⋙ E.functor) :=
    preservesFiniteLimits_of_natIso (ordinaryDiagonalTowerIso J A).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (ordinaryDiagonal J A) E.functor

private instance ordinaryDiagonal_colimits : PreservesFiniteColimits (ordinaryDiagonal J A) := by
  let E := (SheafOfModules.strictSystemSequenceEquivalence.{u, u, u} (J := J)
    ((Functor.const ℕᵒᵖ).obj (constant J A))).symm.trans
      (systemTowerEquivalence (constant J A))
  have : PreservesFiniteColimits (ordinaryDiagonal J A ⋙ E.functor) :=
    preservesFiniteColimits_of_natIso (ordinaryDiagonalTowerIso J A).symm
  exact preservesFiniteColimits_of_reflects_of_preserves (ordinaryDiagonal J A) E.functor

private instance projectionContinuous :
    (Prod.snd ℕ C).IsContinuous (WeilConjectures.coefficientSequenceTopology J) J where
  op_comp_isSheaf_of_types G := by
    apply SheafOfModules.sequence_sheaf_of_slices.{u, u, u, max u 0}
    intro n
    exact (isSheaf_iff_isSheaf_of_type _ _).1 G.property

private instance projectionCocontinuous :
    (Prod.snd ℕ C).IsCocontinuous (WeilConjectures.coefficientSequenceTopology J) J where
  cover_lift h := h

private def projectionAlgebraicInverseImage : SheafOfModules.AlgebraicInverseImage
    ((Prod.snd ℕ C).sheafPushforwardContinuous (Type u)
      (WeilConjectures.coefficientSequenceTopology J) J)
    (constant J A) (strictDiagonalRing J A) where
  ringUnderlying := ObjectProperty.isoMk _ (NatIso.ofComponents (fun X ↦ Iso.refl _) (by
    intro X Y f
    ext x
    change (constant J A).obj.map f.unop.2.op x =
      (constant J A).obj.map f.unop.2.op x
    rfl))
  ringAdd := by intro T a b t h X x; exact h (op X.unop.2) x
  ringMul := by intro T a b t h X x; exact h (op X.unop.2) x
  ringZero := by intro T a h X x; exact h (op X.unop.2) x
  ringOne := by intro T a h X x; exact h (op X.unop.2) x
  modules := ordinaryDiagonal J A
  moduleUnderlying := NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      ext x
      rfl))) (by intro M N f; ext X x; rfl)
  moduleAdd := by intro M T a b t h X x; exact h (op X.unop.2) x
  moduleZero := by intro M T a h X x; exact h (op X.unop.2) x
  moduleSMul := by intro M T a b t h X x; exact h (op X.unop.2) x

private local instance (X : Cᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (Prod.snd ℕ C).op) (Type u) :=
  hasLimitsOfShape_of_essentiallySmall _ _

private theorem ordinaryDiagonal_flat (P : Cx (constant J A))
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := constant J A) P)
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := constant J A) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := strictDiagonalRing J A)
      (((ordinaryDiagonal J A).mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite
        (J := WeilConjectures.coefficientSequenceTopology J) (R := strictDiagonalRing J A)
        ((ordinaryDiagonal J A).obj (P.X i)) := by
  classical
  let S := strictDiagonalRing J A
  let D := ordinaryDiagonal J A
  let M : SheafOfModules.SystemScalarModel.{u, u, u}
      (J := WeilConjectures.coefficientSequenceTopology J) (𝟙 S) :=
    (SheafOfModules.nonempty_systemScalarModel.{u, u, u}
      (J := WeilConjectures.coefficientSequenceTopology J) (𝟙 S)).some
  let T := D ⋙ M.model.E
  have : D.Additive := inferInstance
  have : T.Additive := inferInstance
  have ht := SheafOfModules.isKFlat_ringedToposPullback
    ((Prod.snd ℕ C).sheafPushforwardContinuous (Type u)
      (WeilConjectures.coefficientSequenceTopology J) J)
    ((Prod.snd ℕ C).sheafPushforwardCocontinuous (Type u)
      (WeilConjectures.coefficientSequenceTopology J) J)
    ((Prod.snd ℕ C).sheafAdjunctionCocontinuous (Type u)
      (WeilConjectures.coefficientSequenceTopology J) J)
    (projectionAlgebraicInverseImage J A) (𝟙 S) T
    (fun N ↦ M.model.obj_eq (D.obj N)) (fun f ↦ M.model.map_eq (D.map f)) P hP hf
  let e : T ≅ D := Functor.isoWhiskerLeft D
    (SheafOfModules.systemScalarModelUnit rfl M) ≪≫ D.rightUnitor
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  exact ⟨SheafOfModules.kFlat_iso_independent S ec ht.1,
    fun i ↦ SheafOfModules.flatOnSite_of_iso S
      ((HomologicalComplex.eval _ (.up ℤ) i).mapIso ec) (ht.2 i)⟩

private theorem normalizedScalarInsertion {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    ∃ η : 𝟭 (Mod R) ⟶ change φ ⋙ res φ,
      ∀ (M : Mod R) (U : Cᵒᵖ) (m : M.val.obj U),
        (η.app M).val.app U m = tensorSection φ M U 1 m := by
  exact scalarExtensionUnit_exists J φ

private theorem sheafificationRestriction_eq
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
    (R : Sheaf K RingCat.{u}) (S : Sheaf J RingCat.{u})
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (M : PresheafOfModules.{u} R.obj) :
    ∃ z : (PresheafOfModules.sheafification (𝟙 S.obj)).obj
          ((PresheafOfModules.pushforward φ.hom).obj M) ≅
        (SheafOfModules.pushforward φ).obj
          ((PresheafOfModules.sheafification (𝟙 R.obj)).obj M),
      ∀ (U : Cᵒᵖ) (x : M.obj (F.op.obj U)),
        z.hom.val.app U
          (((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).unit.app
            ((PresheafOfModules.pushforward φ.hom).obj M)).app U x) =
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M).app
          (F.op.obj U) x := by
  let V := PresheafOfModules.pushforward φ.hom
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)
  let g : V.obj M ⟶
      (SheafOfModules.forget S ⋙ PresheafOfModules.restrictScalars (𝟙 S.obj)).obj
        ((SheafOfModules.pushforward φ).obj
          ((PresheafOfModules.sheafification (𝟙 R.obj)).obj M)) :=
    V.map ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M)
  let f := (adj.homEquiv _ _).symm g
  have hW : J.W ((PresheafOfModules.toPresheaf S.obj).map g) := by
    change J.W (Functor.whiskerLeft F.op (toSheafify K M.presheaf))
    have : Presheaf.IsLocallyInjective J
        (Functor.whiskerLeft F.op (toSheafify K M.presheaf)) :=
      Presheaf.isLocallyInjective_whisker J K F _
    have : Presheaf.IsLocallySurjective J
        (Functor.whiskerLeft F.op (toSheafify K M.presheaf)) :=
      Presheaf.isLocallySurjective_whisker J K F _
    exact J.W_of_isLocallyBijective _
  have : IsIso ((PresheafOfModules.sheafification (𝟙 S.obj)).map g) := by
    change ((MorphismProperty.isomorphisms _).inverseImage
      (PresheafOfModules.sheafification (𝟙 S.obj))) g
    rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
    exact hW
  have : IsIso f := by
    dsimp only [f]
    rw [Adjunction.homEquiv_counit]
    infer_instance
  refine ⟨asIso f, ?_⟩
  intro U x
  exact congrArg (fun t ↦ t.app U x) ((adj.homEquiv _ _).apply_symm_apply g)

private theorem localTensorRestriction
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {R S : Sheaf K CommRingCat.{u}} (φ : R ⟶ S) (M : Mod R)
    {X Y : Dᵒᵖ} (f : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M).map f
        (s ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m) =
      S.obj.map f s ⊗ₜ[R.obj.obj Y, (φ.hom.app Y).hom] M.val.map f m :=
  Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap.{u, u, u} φ M f) s m

private theorem quotientSliceSheafification (M : Mod (constant J A)) (n : ℕ) :
    ∃ z : (change (quotient J A I n)).obj M ≅
        (SheafOfModules.systemSequenceEvaluation (finiteSystem J A I) n).obj
          ((change (quotientSequenceMap J A I)).obj ((ordinaryDiagonal J A).obj M)),
      ∀ (U : Cᵒᵖ) (s : (finite J A I n).obj.obj U) (m : M.val.obj U),
        z.hom.val.app U (tensorSection (quotient J A I n) M U s m) =
          tensorSection (quotientSequenceMap J A I) ((ordinaryDiagonal J A).obj M)
            (op (n, U.unop)) s m := by
  let F := Prod.sectR n C
  let R := siteModuleRings (strictQuotientRing J A I)
  let S := siteModuleRings (finite J A I n)
  let φ := SheafOfModules.systemSequenceVerticalRingMap (finiteSystem J A I) n
  let P := SheafOfModules.changeOfRingsPresheaf.{u, u, u}
    (quotientSequenceMap J A I) ((ordinaryDiagonal J A).obj M)
  obtain ⟨z, hz⟩ := sheafificationRestriction_eq J F R S φ P
  let e : SheafOfModules.changeOfRingsPresheaf.{u, u, u} (quotient J A I n) M ≅
      (PresheafOfModules.pushforward φ.hom).obj P :=
    PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by
      intro U V f
      ext t
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul s m =>
        change (SheafOfModules.changeOfRingsPresheaf (quotient J A I n) M).map f
            (s ⊗ₜ[(constant J A).obj.obj U, ((quotient J A I n).hom.app U).hom] m) =
          P.map (F.map f.unop).op
            (s ⊗ₜ[(constant J A).obj.obj U, ((quotient J A I n).hom.app U).hom] m)
        have h := localTensorRestriction (quotientSequenceMap J A I)
          ((ordinaryDiagonal J A).obj M) (F.map f.unop).op s m
        rw [localTensorRestriction]
        change P.map (F.map f.unop).op
            (s ⊗ₜ[(constant J A).obj.obj U, ((quotient J A I n).hom.app U).hom] m) =
          (finite J A I n).obj.map f
            (((finiteSystem J A I).map (𝟙 (op n))).hom.app U s)
              ⊗ₜ[(constant J A).obj.obj V, ((quotient J A I n).hom.app V).hom]
                M.val.map f m at h
        rw [(finiteSystem J A I).map_id] at h
        exact h.symm
      | add t t' ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht')
  refine ⟨(PresheafOfModules.sheafification (𝟙 S.obj)).mapIso e ≪≫ z, ?_⟩
  intro U s m
  have he := congrArg (fun f ↦ f.app U
    (s ⊗ₜ[(constant J A).obj.obj U, ((quotient J A I n).hom.app U).hom] m))
      ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).unit.naturality e.hom)
  change z.hom.val.app U
    (((PresheafOfModules.sheafification (𝟙 S.obj)).map e.hom).val.app U
      (tensorSection (quotient J A I n) M U s m)) = _
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).unit.app
      ((PresheafOfModules.pushforward φ.hom).obj P)).app U
        (s ⊗ₜ[(constant J A).obj.obj U, ((quotient J A I n).hom.app U).hom] m) =
      (((PresheafOfModules.sheafification (𝟙 S.obj)).map e.hom).val.app U)
        (tensorSection (quotient J A I n) M U s m) at he
  exact (congrArg (fun t ↦ z.hom.val.app U t) he.symm).trans (hz U _)

private theorem scalarSection_restrict
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {R S : Sheaf K CommRingCat.{u}} (φ : R ⟶ S) (M : Mod R)
    {X Y : Dᵒᵖ} (f : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    ((change φ).obj M).val.map f (tensorSection φ M X s m) =
      tensorSection φ M Y (S.obj.map f s) (M.val.map f m) := by
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M)
  have h := PresheafOfModules.naturality_apply η f
    (s ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m)
  change η.app Y
      ((SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M).map f
        (s ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m)) =
    ((change φ).obj M).val.map f (tensorSection φ M X s m) at h
  exact h.symm.trans (congrArg (fun x ↦ η.app Y x) (localTensorRestriction φ M f s m))

private def canonicalTowers : Mod (strictDiagonalRing J A) ≌
    (ℕᵒᵖ ⥤ Mod (constant J A)) :=
  (SheafOfModules.strictSystemSequenceEquivalence.{u, u, u} (J := J)
    ((Functor.const ℕᵒᵖ).obj (constant J A))).symm.trans
      (systemTowerEquivalence (constant J A))

private theorem ordinaryReductionIso :
    ∃ e : ordinaryDiagonal J A ⋙ change (quotientSequenceMap J A I) ⋙
        res (quotientSequenceMap J A I) ⋙ (canonicalTowers J A).functor ≅
      reductionTower J A I false,
      ∀ (M : Mod (constant J A)) (n : ℕ) (U : Cᵒᵖ)
        (s : (finite J A I n).obj.obj U) (m : M.val.obj U),
        (((e.inv.app M).app (op n)).val.app U)
          (tensorSection (quotient J A I n) M U s m) =
            tensorSection (quotientSequenceMap J A I) ((ordinaryDiagonal J A).obj M)
              (op (n, U.unop)) s m := by
  classical
  let F := ordinaryDiagonal J A ⋙ change (quotientSequenceMap J A I) ⋙
    res (quotientSequenceMap J A I) ⋙ (canonicalTowers J A).functor
  let e (M : Mod (constant J A)) (n : ℕ) :
      ((reductionTower J A I false).obj M).obj (op n) ≅ (F.obj M).obj (op n) :=
    (res (quotient J A I n)).mapIso (quotientSliceSheafification J A I M n).choose
  have he (M : Mod (constant J A)) (n : ℕ) (U : Cᵒᵖ)
      (s : (finite J A I n).obj.obj U) (m : M.val.obj U) :
      ((e M n).hom.val.app U) (tensorSection (quotient J A I n) M U s m) =
        tensorSection (quotientSequenceMap J A I) ((ordinaryDiagonal J A).obj M)
          (op (n, U.unop)) s m :=
    (quotientSliceSheafification J A I M n).choose_spec U s m
  have hs (M : Mod (constant J A)) (n : ℕ) :
      ((reductionTower J A I false).obj M).map (homOfLE (Nat.le_succ n)).op ≫
          (e M n).hom =
        (e M (n + 1)).hom ≫ (F.obj M).map (homOfLE (Nat.le_succ n)).op := by
    simp only [reductionTower, Functor.flip_obj_map,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply restrictedTensor_hom_ext (quotient J A I (n + 1)) M
    intro U s m
    change (e M n).hom.val.app U
        (((reductionStep J A I false n).app M).val.app U
          (tensorSection (quotient J A I (n + 1)) M U s m)) =
      (((change (quotientSequenceMap J A I)).obj ((ordinaryDiagonal J A).obj M)).val.map
        (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op)
          ((e M (n + 1)).hom.val.app U
            (tensorSection (quotient J A I (n + 1)) M U s m))
    have hstep : ((reductionStep J A I false n).app M).val.app U
        (tensorSection (quotient J A I (n + 1)) M U s m) =
      tensorSection (quotient J A I n) M U ((transition J A I n).hom.app U s) m :=
        (reductionStep_existsUnique J A I false n).exists.choose_spec M U s m
    rw [hstep, he, he, scalarSection_restrict]
    congr 1
    · have h := SheafOfModules.systemSequenceRing_horizontal (finiteSystem J A I)
        (Nat.le_succ n) U
      rw [finiteSystem, Functor.ofOpSequence_map_homOfLE_succ] at h
      exact congrArg (fun f ↦ f s) h.symm
    · change m = (M.val.map (𝟙 U)) m
      rw [M.val.map_id]
      rfl
  let t (M : Mod (constant J A)) : (reductionTower J A I false).obj M ≅ F.obj M :=
    NatIso.ofComponents (fun n ↦ e M n.unop)
      (fun f ↦ (NatTrans.ofOpSequence (fun n ↦ (e M n).hom) (hs M)).naturality f)
  let z : reductionTower J A I false ≅ F := NatIso.ofComponents t (by
    intro M N f
    apply NatTrans.ext
    funext n
    apply restrictedTensor_hom_ext (quotient J A I n.unop) M
    intro U s m
    change (e N n.unop).hom.val.app U
        (((change (quotient J A I n.unop)).map f).val.app U
          (tensorSection (quotient J A I n.unop) M U s m)) =
      (((change (quotientSequenceMap J A I)).map ((ordinaryDiagonal J A).map f)).val.app
        (op (n.unop, U.unop)))
          ((e M n.unop).hom.val.app U (tensorSection (quotient J A I n.unop) M U s m))
    rw [tensorSection_map, he, he, tensorSection_map]
    rfl)
  exact ⟨z.symm, he⟩

private theorem ordinaryInsertion :
    ∃ η : ordinaryDiagonal J A ⟶ ordinaryDiagonal J A ⋙
        change (quotientSequenceMap J A I) ⋙ res (quotientSequenceMap J A I),
      ∀ (M : Mod (constant J A)) (X : (ℕ × C)ᵒᵖ)
        (x : ((ordinaryDiagonal J A).obj M).val.obj X),
        (η.app M).val.app X x =
          tensorSection (quotientSequenceMap J A I) ((ordinaryDiagonal J A).obj M) X 1 x := by
  obtain ⟨η, hη⟩ := normalizedScalarInsertion
    (J := WeilConjectures.coefficientSequenceTopology J) (quotientSequenceMap J A I)
  exact ⟨Functor.whiskerLeft (ordinaryDiagonal J A) η, fun M X x ↦ hη _ X x⟩

/-- A section-normalized ordinary quotient presentation whose diagonal preserves flat
modules and K-flat complexes with flat terms.

Source: Stacks Project, Tags 03DA and 03EK (vertical sheafification and tensor),
0940 (the sequence site), and 06YN (K-flatness)
(blueprint: lem-pur-strict-quotient-ordinary-flat-presentation).

Proof: take the sequence ring of the quotient coefficient system, with the ring map
induced by the quotient cone. Restricting a constant-ring sequence module to its slices
and reassembling these restrictions are inverse constructions, with identity section
maps. Use the canonical normalized equivalence for this part of the presentation.
The diagonal is reassembly of a constant tower. Its sections and restrictions are those
of the original module, and
componentwise kernels and cokernels prove its exactness. The scalar-extension insertion
is the sheafification of x mapped to 1 tensor x. Sheafification on the sequence site is
vertical: sheafify every slice, extending the transitions uniquely by the sheafification
adjunction. Therefore the comparison with the ordinary reduction tower is identity on
pure tensors and respects the quotient transitions. For flatness, projection from the
sequence site to the base is continuous and
cocontinuous, and its inverse image on modules is the diagonal. Apply the existing
ringed-topos K-flat pullback theorem followed by extension along the identity ring map.
The normalized scalar-unit isomorphism removes this identity extension, so the diagonal
preserves K-flat complexes with flat terms, and preserves flatness of every term.
This argument is valid for the
zero ring, the zero and unit ideals, empty sites, and unbounded complexes. -/
theorem strictQuotientOrdinaryFlatPresentation
    :
    ∃ d : StrictQuotientDiagonalPresentation J A I,
      ∀ P : Cx (constant J A),
        CochainComplex.IsKFlatIndependentCoefficients (R := constant J A) P →
        (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := constant J A) (P.X q)) →
        CochainComplex.IsKFlatIndependentCoefficients (R := strictDiagonalRing J A)
          ((d.diagonal.mapHomologicalComplex (.up ℤ)).obj P) ∧
        (∀ q : ℤ, SheafOfModules.IsFlatOnSite
          (J := WeilConjectures.coefficientSequenceTopology J)
          (R := strictDiagonalRing J A) (d.diagonal.obj (P.X q))) := by
  obtain ⟨e, he⟩ := ordinaryReductionIso J A I
  obtain ⟨η, hη⟩ := ordinaryInsertion J A I
  have ht : (toTower (constant J A)).Additive := by
    constructor
    intro M N f g
    apply NatTrans.ext
    funext n
    exact (SheafOfModules.systemEvaluation ((Functor.const ℕᵒᵖ).obj (constant J A))
      n.unop).map_add
  have : (canonicalTowers J A).functor.Additive := by
    change ((SheafOfModules.sequenceToStrictSystemFunctor.{u, u, u} (J := J)
      ((Functor.const ℕᵒᵖ).obj (constant J A))) ⋙ toTower (constant J A)).Additive
    infer_instance
  refine ⟨{
      ringMap := quotientSequenceMap J A I
      ringMap_sections := fun _ _ ↦ HEq.rfl
      towers := canonicalTowers J A
      towers_objects := fun _ _ _ ↦ HEq.rfl
      towers_restrictions := fun _ _ {_ _} _ ↦ HEq.rfl
      towers_transitions := ?_
      towers_maps := fun _ _ _ ↦ HEq.rfl
      diagonal := ordinaryDiagonal J A
      diagonal_objects := ordinaryDiagonal_objects J A
      diagonal_restrictions := ordinaryDiagonal_restrictions J A
      diagonal_maps := ordinaryDiagonal_maps J A
      insertion := η
      insertion_sections := hη
      reductionIso := e
      reductionIso_sections := ?_
      restrictionModel := (res (quotientSequenceMap J A I)).mapDerivedCategory ⋙
        (canonicalTowers J A).functor.mapDerivedCategory
      restrictionModel_eq := rfl
      reductionModel := (ordinaryDiagonal J A).mapDerivedCategory ⋙
        extend (quotientSequenceMap J A I)
      reductionModel_eq := rfl }, ordinaryDiagonal_flat J A⟩
  · intro M m n h U
    change HEq (SheafOfModules.sequenceSystemTransitionApp
      ((Functor.const ℕᵒᵖ).obj (constant J A)) M h U)
        (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
    let φ := ((SheafOfModules.derivedChangeRingIndependentCoefficients
      (WeilConjectures.coefficientSequenceTopology J) (strictDiagonalRing J A)).obj.map
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op).hom
    have hφ : φ = RingHom.id _ := by
      have hh := SheafOfModules.systemSequenceRing_horizontal
        ((Functor.const ℕᵒᵖ).obj (constant J A)) h U
      dsimp only [Functor.const_obj_map] at hh
      exact congrArg (fun t ↦ t.hom) hh
    exact identityRestriction_hom_heq φ hφ _ _ _ _ (fun x ↦ rfl)
  · intro M n U s x m z hx hz
    have hx' : x = m := eq_of_heq hx
    subst x
    have hz' : z = tensorSection (quotientSequenceMap J A I)
        ((ordinaryDiagonal J A).obj M) (op (n, U.unop)) s m := eq_of_heq hz
    rw [hz', ← he M n U s m]
    exact congrArg (fun f ↦ f.val.app U (tensorSection (quotient J A I n) M U s m))
      (congrArg (fun t ↦ t.app (op n)) (e.inv_hom_id_app M))


end CategoryTheory.ConstantCompletion
