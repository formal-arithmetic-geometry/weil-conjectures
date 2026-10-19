/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.ConstantWeilStructure
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Lean.Elab.Tactic.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility

/-! # Normalized scalar extension of constant coefficient objects

Source: blueprint, ordinary compact cohomology, order 1869, coefficient-object paragraph;
Bhatt--Scholze, Lemma 6.8.2 (blueprint: lem-weil-constant-coefficient-objects-constructible).
This supplements the existing constructibility module with the canonical coefficient-unit
comparison, including its strict-cone normalization, in the intrinsic rational category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
universe v c r
namespace ConstantScalarNormalization
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (α : R ⟶ S)
set_option hygiene false in
local notation "ring" A => (sheafCompose J (forget₂ CommRingCat RingCat)).obj A
private def regRaw :
    SheafOfModules.changeOfRingsPresheaf α (SheafOfModules.unit (ring R)) ≅
      (SheafOfModules.unit (ring S)).val :=
  PresheafOfModules.isoMk (fun U ↦ by
    letI := (α.hom.app U).hom.toAlgebra
    exact (TensorProduct.AlgebraTensorModule.rid (R.obj.obj U) (S.obj.obj U)
      (S.obj.obj U)).toModuleIso) (by
        intro U V f
        apply ModuleCat.hom_ext
        ext z
        induction z using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | add a b ha hb => simp only [map_add, ha, hb]
        | tmul s x =>
          change ↑(S.obj.obj U) at s
          change ↑(R.obj.obj U) at x
          let := (α.hom.app V).hom.toAlgebra
          change (TensorProduct.AlgebraTensorModule.rid (R.obj.obj V) (S.obj.obj V)
            (S.obj.obj V))
              (SheafOfModules.changeOfRingsMap α (SheafOfModules.unit (ring R)) f
                (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)) =
            S.obj.map f (α.hom.app U x * s)
          calc
            _ = α.hom.app V (R.obj.map f x) * S.obj.map f s :=
              congrArg (TensorProduct.AlgebraTensorModule.rid (R.obj.obj V)
                (S.obj.obj V) (S.obj.obj V))
                  (Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap α
                    (SheafOfModules.unit (ring R)) f) s x)
            _ = _ := by
              rw [map_mul]
              exact congrArg (fun z ↦ z * S.obj.map f s)
                (ConcreteCategory.congr_hom (α.hom.naturality f) x))

private def regIso :
    SheafOfModules.changeOfRings α (SheafOfModules.unit (ring R)) ≅
      SheafOfModules.unit (ring S) :=
  (PresheafOfModules.sheafification (𝟙 (ring S).obj)).mapIso (regRaw α) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 (ring S).obj)).counit.app
      (SheafOfModules.unit (ring S)))
private theorem regIso_hom_tmul (U : Cᵒᵖ) (s : S.obj.obj U) (x : R.obj.obj U) :
    (regIso α).hom.val.app U
      ((toSheafify J
        (SheafOfModules.changeOfRingsPresheaf α
          (SheafOfModules.unit (ring R))).presheaf).app U
            (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)) = α.hom.app U x * s := by
  have h := ((PresheafOfModules.sheafificationAdjunction (𝟙 (ring S).obj)).homEquiv
    _ (SheafOfModules.unit (ring S))).apply_symm_apply ((regRaw α).hom)
  rw [Adjunction.homEquiv_counit] at h
  have hh := congrArg
    (fun g ↦ g.app U (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)) h
  exact hh

private theorem regIso_inv_one (U : Cᵒᵖ) :
    (regIso α).inv.val.app U (1 : S.obj.obj U) =
      (toSheafify J (SheafOfModules.changeOfRingsPresheaf α
        (SheafOfModules.unit (ring R))).presheaf).app U
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] (1 : R.obj.obj U)) := by
  have h := regIso_hom_tmul α U 1 1
  simp only [map_one, one_mul] at h
  have hi := congrArg (fun f ↦ f.val.app U) (regIso α).hom_inv_id
  have ht := ConcreteCategory.congr_hom hi
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf α
      (SheafOfModules.unit (ring R))).presheaf).app U
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] (1 : R.obj.obj U)))
  exact (congrArg (fun x ↦ (regIso α).inv.val.app U x) h.symm).trans ht

private theorem cone_component_ext {A : Type*} [Category A] [Preadditive A]
    {K L : CochainComplex A ℤ} (r : K ⟶ L) [HomologicalComplex.HasHomotopyCofiber r]
    {M : A} (i : ℤ) (a b : M ⟶ (CochainComplex.mappingCocone r).X i)
    (hf : a ≫ (CochainComplex.mappingCocone.fst r).f i =
      b ≫ (CochainComplex.mappingCocone.fst r).f i)
    (hs : a ≫ (CochainComplex.mappingCocone.snd r).v i (i - 1) (by omega) =
      b ≫ (CochainComplex.mappingCocone.snd r).v i (i - 1) (by omega)) : a = b := by
  have hi := CochainComplex.mappingCocone.id_X r i (i - 1) (by omega)
  calc
    a = a ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = b ≫ 𝟙 _ := by
      rw [← hi]
      simp only [Preadditive.comp_add, ← Category.assoc, hf, hs]
    _ = b := Category.comp_id _

end ConstantScalarNormalization

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : Scheme.{u})

private def ordinaryRegularIso :
    (completedOrdinaryScalarExtension l E L ι Y).obj
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) ≅
        SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l L Y) :=
  eqToIso ((completedScalarChangeData l E L ι Y).choose_spec.choose _) ≪≫
    ConstantScalarNormalization.regIso (completedCoefficientMap l E L ι Y)
private def ordinaryRegularComplexIso :
    (completedOrdinaryScalarComplex l E L ι Y).obj (constantWeilIntegralComplex l E Y) ≅
      constantWeilIntegralComplex l L Y :=
  (HomologicalComplex.singleMapHomologicalComplex
    (completedOrdinaryScalarExtension l E L ι Y) (ComplexShape.up ℤ) 0).app
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) ≪≫
    (CochainComplex.singleFunctor (integralTowerModules l L Y) 0).mapIso
      (ordinaryRegularIso l E L ι Y)
private theorem scalarUnit_ext
    (a b : constantWeilIntegralComplex l L Y ⟶
      (integralScalarComplexFunctor l E L ι Y).obj (constantWeilIntegralComplex l E Y))
    (hunit : ∀ (n : ℕ) (V : Y.ProEt),
      ((a.f 0 ≫ (CochainComplex.mappingCocone.fst
        (completedScalarRoosEndomorphism l E L ι Y
          (constantWeilIntegralComplex l E Y))).f 0 ≫
        (Pi.π (fun m ↦ ((integralScalarTowerFunctor l E L ι Y).obj
          (constantWeilIntegralComplex l E Y)).obj (op m)) n).f 0).val.app (op V))
            (constantWeilUnitSection l L Y V) =
      ((b.f 0 ≫ (CochainComplex.mappingCocone.fst
        (completedScalarRoosEndomorphism l E L ι Y
          (constantWeilIntegralComplex l E Y))).f 0 ≫
        (Pi.π (fun m ↦ ((integralScalarTowerFunctor l E L ι Y).obj
          (constantWeilIntegralComplex l E Y)).obj (op m)) n).f 0).val.app (op V))
            (constantWeilUnitSection l L Y V))
    (hs : ∀ i : ℤ,
      a.f i ≫ (CochainComplex.mappingCocone.snd
        (completedScalarRoosEndomorphism l E L ι Y
          (constantWeilIntegralComplex l E Y))).v i (i - 1) (by omega) =
      b.f i ≫ (CochainComplex.mappingCocone.snd
        (completedScalarRoosEndomorphism l E L ι Y
          (constantWeilIntegralComplex l E Y))).v i (i - 1) (by omega)) : a = b := by
  let r := completedScalarRoosEndomorphism l E L ι Y
    (constantWeilIntegralComplex l E Y)
  have hf : a ≫ CochainComplex.mappingCocone.fst r =
      b ≫ CochainComplex.mappingCocone.fst r := by
    apply Pi.hom_ext
    intro n
    apply HomologicalComplex.from_single_hom_ext
    apply (cancel_epi (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l L Y))).inv).mp
    apply (SheafOfModules.unitHomEquiv _).injective
    apply Subtype.ext
    funext V
    exact hunit n V.unop
  apply HomologicalComplex.from_single_hom_ext
  have hf0 := congrArg (fun f ↦ f.f 0) hf
  change a.f 0 ≫ (CochainComplex.mappingCocone.fst r).f 0 =
    b.f 0 ≫ (CochainComplex.mappingCocone.fst r).f 0 at hf0
  exact ConstantScalarNormalization.cone_component_ext r 0 (a.f 0) (b.f 0) hf0 (hs 0)

private theorem ordinaryRegularComplexIso_unit (V : Y.ProEt) :
    ((ordinaryRegularComplexIso l E L ι Y).inv.f 0).val.app (op V)
      (constantWeilUnitSection l L Y V) =
    completedScalarTensorSection l E L ι Y
      ((constantWeilIntegralComplex l E Y).X 0) (op V) 1
        (constantWeilUnitSection l E Y V) := by
  change (ordinaryRegularIso l E L ι Y).inv.val.app (op V)
      (1 : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj (op V)) =
    completedScalarTensorSection l E L ι Y
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))
      (op V) 1
        (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))
  dsimp only [ordinaryRegularIso, Iso.trans_inv, eqToIso.inv,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    completedScalarTensorSection]
  apply congrArg (fun x ↦ (eqToHom
    ((completedScalarChangeData l E L ι Y).choose_spec.choose _).symm).val.app (op V) x)
  exact ConstantScalarNormalization.regIso_inv_one (completedCoefficientMap l E L ι Y) (op V)


private def scalarUnitCandidate :
    constantWeilIntegralComplex l L Y ⟶
      (integralScalarComplexFunctor l E L ι Y).obj (constantWeilIntegralComplex l E Y) :=
  (ordinaryRegularComplexIso l E L ι Y).inv ≫
    (completedScalarChainComparison l E L ι Y).app (constantWeilIntegralComplex l E Y)

private theorem scalarUnitCandidate_spec :
      (∀ (n : ℕ) (V : Y.ProEt),
        (((scalarUnitCandidate l E L ι Y).f 0 ≫
          (CochainComplex.mappingCocone.fst
            (completedScalarRoosEndomorphism l E L ι Y
              (constantWeilIntegralComplex l E Y))).f 0 ≫
          (Pi.π (fun m ↦ ((integralScalarTowerFunctor l E L ι Y).obj
            (constantWeilIntegralComplex l E Y)).obj (op m)) n).f 0).val.app (op V))
              (constantWeilUnitSection l L Y V) =
          integralScalarTensorSection l E L ι Y n
            ((constantWeilIntegralComplex l E Y).X 0) (op V) 1
            (constantWeilUnitSection l E Y V)) ∧
      (∀ i : ℤ, (scalarUnitCandidate l E L ι Y).f i ≫
        (CochainComplex.mappingCocone.snd
          (completedScalarRoosEndomorphism l E L ι Y
            (constantWeilIntegralComplex l E Y))).v i (i - 1) (by omega) = 0) := by
  let P := constantWeilIntegralComplex l E Y
  let e := ordinaryRegularComplexIso l E L ι Y
  let b := completedScalarChainComparison l E L ι Y
  let η := e.inv ≫ b.app P
  have hc := (completedScalarChainComparison_existsUnique l E L ι Y).exists.choose_spec
  have hη :
      (∀ (n : ℕ) (V : Y.ProEt),
        ((η.f 0 ≫ (CochainComplex.mappingCocone.fst
          (completedScalarRoosEndomorphism l E L ι Y P)).f 0 ≫
          (Pi.π (fun m ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj
            (op m)) n).f 0).val.app (op V))
              (constantWeilUnitSection l L Y V) =
          integralScalarTensorSection l E L ι Y n (P.X 0) (op V) 1
            (constantWeilUnitSection l E Y V)) ∧
      (∀ i : ℤ, η.f i ≫ (CochainComplex.mappingCocone.snd
          (completedScalarRoosEndomorphism l E L ι Y P)).v i (i - 1) (by omega) = 0) := by
    constructor
    · intro n V
      have hu := ordinaryRegularComplexIso_unit l E L ι Y V
      have hc' := hc.1 P 0 n (op V) 1 (constantWeilUnitSection l E Y V)
      calc
        _ = ((b.app P).f 0 ≫
            (CochainComplex.mappingCocone.fst
              (completedScalarRoosEndomorphism l E L ι Y P)).f 0 ≫
            (Pi.π (fun m ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj
              (op m)) n).f 0).val.app (op V)
                (((e.inv.f 0).val.app (op V)) (constantWeilUnitSection l L Y V)) := rfl
        _ = _ := by
          exact (congrArg (fun x ↦ ((b.app P).f 0 ≫
            (CochainComplex.mappingCocone.fst
              (completedScalarRoosEndomorphism l E L ι Y P)).f 0 ≫
            (Pi.π (fun m ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj
              (op m)) n).f 0).val.app (op V) x) hu).trans
                (by
                  exact hc'.trans (congrArg
                    (fun s ↦ integralScalarTensorSection l E L ι Y n (P.X 0) (op V) s
                      (constantWeilUnitSection l E Y V))
                    ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app
                      (op V)).hom.map_one))
    · intro i
      dsimp only [η, HomologicalComplex.comp_f]
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun f ↦ e.inv.f i ≫ f) (hc.2 P i)).trans Limits.comp_zero)
  exact hη

/-- The coefficient-unit inverse is fixed by its quotient coordinates and zero shifted
component, on the regular module itself.
Source: blueprint order 1869; Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-weil-constant-coefficient-objects-constructible).
Proof: multiplication identifies each finite scalar extension of the regular module
with the finite target coefficient module. Send s to 1 tensor pi_n(s) in each factor.
These maps commute with reductions, hence their product is killed by 1-shift. The strict
mapping cocone lift with zero shifted component gives eta. The regular module is generated
locally by one, so these formulas fix the first component in degree zero; the source is
zero in every other degree. The two cone projections then prove uniqueness. -/
theorem constantCoefficientScalarUnit_existsUnique :
    ∃! η : constantWeilIntegralComplex l L Y ⟶
        (integralScalarComplexFunctor l E L ι Y).obj (constantWeilIntegralComplex l E Y),
      (∀ (n : ℕ) (V : Y.ProEt),
        ((η.f 0 ≫
          (CochainComplex.mappingCocone.fst
            (completedScalarRoosEndomorphism l E L ι Y
              (constantWeilIntegralComplex l E Y))).f 0 ≫
          (Pi.π (fun m ↦ ((integralScalarTowerFunctor l E L ι Y).obj
            (constantWeilIntegralComplex l E Y)).obj (op m)) n).f 0).val.app (op V))
              (constantWeilUnitSection l L Y V) =
          integralScalarTensorSection l E L ι Y n
            ((constantWeilIntegralComplex l E Y).X 0) (op V) 1
            (constantWeilUnitSection l E Y V)) ∧
      (∀ i : ℤ, η.f i ≫
        (CochainComplex.mappingCocone.snd
          (completedScalarRoosEndomorphism l E L ι Y
            (constantWeilIntegralComplex l E Y))).v i (i - 1) (by omega) = 0) := by
  refine ⟨scalarUnitCandidate l E L ι Y, scalarUnitCandidate_spec l E L ι Y, ?_⟩
  intro b hb
  apply scalarUnit_ext l E L ι Y b (scalarUnitCandidate l E L ι Y)
  · intro n V
    exact (hb.1 n V).trans ((scalarUnitCandidate_spec l E L ι Y).1 n V).symm
  · intro i
    exact (hb.2 i).trans ((scalarUnitCandidate_spec l E L ι Y).2 i).symm

/-- The strict scalar unit, with both cone components determined uniquely.
Source: blueprint order 1869 (blueprint: lem-weil-constant-coefficient-objects-constructible).
-/
def constantCoefficientScalarUnit :=
  (constantCoefficientScalarUnit_existsUnique l E L ι Y).exists.choose

private theorem scalarChainComparison_isIso
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hcomplete : IsDerivedCompleteUnrestricted l E Y (DerivedCategory.Q.obj P.obj)) :
    IsIso (DerivedCategory.Q.map ((completedScalarChainComparison l E L ι Y).app
      P.obj)) := by
  have hχ := ((finiteFreeCompletedScalarComparison l E L ι Y).2.1 _ hcomplete).1
  have hc := (completedScalarComparison_existsUnique l E L ι Y).exists.choose_spec P
  have hε :=
    (completedScalarChangeData l E L ι Y).choose_spec.choose_spec.choose_spec.choose_spec.2.2
      |>.choose_spec.choose_spec.2.2 P.obj P.property.1
  have : IsIso (completedScalarCounit l E L ι Y P.obj) := by
    -- Use the stored proof directly; the kernel checks its definitional conversion.
    -- Elaborator unification otherwise unfolds the sheafified tensor repeatedly.
    run_tac do
      let h ← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `hε)
      (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkFVar h)
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ inferInstance
    (IsIso.comp_isIso' hχ
      ((integralScalarExtensionComparisonOfUniverses l E L ι Y).app P).isIso_hom) hc.symm

/-- The normalized coefficient-unit map is a quasi-isomorphism.
Source: blueprint order 1869; Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-weil-constant-coefficient-objects-constructible).
Proof: the constant regular coefficient object is derived complete. The finite-free
completed scalar comparison is invertible on this object. Its normalized descent equation
and the invertible K-flat counit imply invertibility of the localized chain comparison.
The ordinary regular-module scalar isomorphism identifies its composite with the strict
unit by uniqueness of the quotient and shifted coordinates. Thus Q sends the unit to an
isomorphism. -/
theorem constantCoefficientScalarUnit_isIso :
    IsIso (DerivedCategory.Q.map (constantCoefficientScalarUnit l E L ι Y)) := by
  obtain ⟨p, hlp, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := le_rfl
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := Nat.ne_of_lt (Nat.lt_of_succ_le hlp)
  have hcomplete := (integralConstantCoefficient_constructible l E Y D hl).2.2.1
  have hchain := scalarChainComparison_isIso l E L ι Y
    (constantWeilIntegralGood l E Y) hcomplete
  have heq : constantCoefficientScalarUnit l E L ι Y = scalarUnitCandidate l E L ι Y :=
    (constantCoefficientScalarUnit_existsUnique l E L ι Y).unique
      (constantCoefficientScalarUnit_existsUnique l E L ι Y).exists.choose_spec
      (scalarUnitCandidate_spec l E L ι Y)
  rw [heq]
  change IsIso (DerivedCategory.Q.map
    ((ordinaryRegularComplexIso l E L ι Y).inv ≫
      (completedScalarChainComparison l E L ι Y).app (constantWeilIntegralComplex l E Y)))
  rw [Functor.map_comp]
  exact IsIso.comp_isIso' (by infer_instance) hchain

/-- The integral beta is the inverse strict unit after the normalized representative
comparison. Its inverse sends s to the compatible pi_n(s) and zero shifted coordinate.
Source: blueprint order 1869 (blueprint: lem-weil-constant-coefficient-objects-constructible).
-/
def constantCoefficientIntegralScalarIso :
    (integralScalarExtensionOfUniverses l E L ι Y).obj
        (integralConstantCoefficientObject l E Y) ≅ integralConstantCoefficientObject l L Y :=
  (integralScalarExtensionComparisonOfUniverses l E L ι Y).app
      (constantWeilIntegralGood l E Y) ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map (constantCoefficientScalarUnit l E L ι Y))
      (constantCoefficientScalarUnit_isIso l E L ι Y)).symm

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- Lift the normalized beta to the full intrinsic integral category.
Source: blueprint order 1869 (blueprint: lem-weil-constant-coefficient-objects-constructible).
-/
def constantCoefficientConstructibleScalarIso :
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj
        (constantWeilIntegralObject l E D hl Y) ≅ constantWeilIntegralObject l L D hl Y :=
  ObjectProperty.isoMk _ (constantCoefficientIntegralScalarIso l E L ι Y)

private theorem iso_existsUnique_of_source_eq {C : Type*} [Category C]
    {X X' Z : C} (h : X = X') (e : X' ≅ Z) :
    ∃! e' : X ≅ Z, HEq e'.hom e.hom := by
  subst X'
  exact ⟨e, HEq.rfl, fun e' he' ↦ Iso.ext (eq_of_heq he')⟩

/-- The rational alpha is uniquely the image of the normalized integral beta.
Source: blueprint order 1869; Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-weil-constant-coefficient-objects-constructible).
Proof: the prescribed rational scalar functor has the integral scalar object formula.
Use this equality to identify the source, and apply raw rationalization to beta.
Its inverse is the rationalization of beta inverse. The displayed hom formula determines
an isomorphism uniquely since an isomorphism is determined by its hom. -/
theorem constantCoefficientRationalScalarIso_existsUnique :
    ∃! α : (sfRationalScalarExtension l E Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
          (constantWeilRationalObject l E D hl Y) ≅ constantWeilRationalObject l L D hl Y,
      HEq α.hom ((sfRationalConstructibleLocalization l L Y).map
        (constantCoefficientConstructibleScalarIso l E L ι Y D hl).hom) := by
  apply iso_existsUnique_of_source_eq
    ((sfRationalScalarExtension_existsUnique l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1
        (constantWeilRationalObject l E D hl Y))
    ((sfRationalConstructibleLocalization l L Y).mapIso
      (constantCoefficientConstructibleScalarIso l E L ι Y D hl))

/-- The canonical scalar isomorphism alpha, normalized before rationalization.
Source: blueprint order 1869 (blueprint: lem-weil-constant-coefficient-objects-constructible).
-/
def constantCoefficientRationalScalarIso :=
  (constantCoefficientRationalScalarIso_existsUnique l E L ι Y D hl).exists.choose

end WeilConjectures
