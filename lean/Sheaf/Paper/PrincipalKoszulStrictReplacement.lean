/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.Algebra.Homology.KFlatTotalTensorModel
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
import all Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import Sheaf.Paper.CompletedIntegralScalarRegular
import Sheaf.Paper.CompletedIntegralProjectionDivisibility
import all Sheaf.Paper.CompletedIntegralFiniteQuotientHomExt
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.ShortExact
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Principal Koszul strict replacements of completed quotient towers

Source: Stacks Project, Tags 093M, 099L and 06YS; the explicit principal argument
in proof steps 1--8 (blueprint: lem-a1-principal-koszul-strict-replacement).
The index `n : ℕ` denotes exponent `n + 1`. Tensor products keep the order `P ⊗ Q`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.PrincipalKoszulStrictReplacement

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : AlgebraicGeometry.Scheme.{t})

/-- The canonical size witness, without identifying the two input universes.
Source: Stacks 099L (blueprint: lem-a1-principal-koszul-strict-replacement). -/
instance siteSmall : EssentiallySmall.{max u (t + 1)} W.ProEt :=
  essentiallySmallSelf.{u} _

/-- Canonical additive sheafification at the actual coefficient size.
Source: Stacks 099L (blueprint: lem-a1-principal-koszul-strict-replacement). -/
instance (priority := 4000) abSheafify :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} W

/-- The canonical locally bijective criterion at the actual coefficient size.
Source: Stacks 099L (blueprint: lem-a1-principal-koszul-strict-replacement). -/
instance (priority := 4000) abLocallyBijective :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} W

/-- The existing completed coefficient module category.
Source: Stacks 099L (blueprint: lem-a1-principal-koszul-strict-replacement). -/
abbrev Modules := SheafOfModules.{max u (t + 1)}
  (completedIntegralCoefficientSheafUnrestricted l E W)

/-- The constant uniformizer, sent into the specified inverse limit.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def uniformizer :
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ (integralConstantToCompletionOfUniverses l E W).hom.app U
      ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
            (ULift.up (Padic.coefficientExtensionUniformizer l E))))
    (by
      intro U V f
      let c := integralConstantToCompletionOfUniverses l E W
      let η := toSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))
      let a := ULift.up (Padic.coefficientExtensionUniformizer l E)
      have hc := congrArg (fun h ↦ h (η.app U a)) (c.hom.naturality f)
      have hη := congrArg (fun h ↦ h a) (η.naturality f)
      change c.hom.app V ((integralConstantRingOfUniverses l E W).obj.map f
        (η.app U a)) = (completedIntegralCoefficientSheafUnrestricted l E W).obj.map f
          (c.hom.app U (η.app U a)) at hc
      change η.app V a = (integralConstantRingOfUniverses l E W).obj.map f
        (η.app U a) at hη
      exact hc.symm.trans (congrArg (c.hom.app V) hη.symm))

/-- The actual constant quotient module, restricted along the limit projection.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def residue (n : ℕ) : Modules l E W :=
  (SheafOfModules.restrictScalars
    (limit.π (integralCoefficientSheafSystem l E W) (op n))).obj
      (SheafOfModules.unit (integralCoefficientSheaf l E W n))

/-- The specified projection, as a linear map from the unit.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def projection (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W) ⟶
      residue l E W n :=
  (residue l E W n).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun U ↦ (1 : (integralCoefficientSheaf l E W n).obj.obj U))
      (by
        intro U V f
        change (integralCoefficientSheaf l E W n).obj.map f 1 = 1
        exact map_one _))

/-- The existing two-term mapping-cone Koszul complex.
Source: Stacks 0A0E (blueprint: lem-a1-principal-koszul-strict-replacement). -/
abbrev koszul (n : ℕ) : CochainComplex (Modules l E W) ℤ :=
  principalKoszul (completedIntegralCommRingSheafUnrestricted l E W)
    (uniformizer l E W) n

/-- The existing multiplication endomorphism raised to exponent n+1.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement). -/
abbrev multiplication (n : ℕ) :=
  endoPow (globalSectionMultiplication (completedIntegralCommRingSheafUnrestricted l E W)
    (uniformizer l E W)) (n + 1)

private abbrev scalar (U : W.ProEtᵒᵖ) :
    (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U :=
  (integralConstantToCompletionOfUniverses l E W).hom.app U
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
          (ULift.up (Padic.coefficientExtensionUniformizer l E)))

private lemma scalar_projection_zero (n : ℕ) (U : W.ProEtᵒᵖ) :
    (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app U
      ((scalar l E W U) ^ (n + 1)) = 0 := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology W
  let π := Padic.coefficientExtensionUniformizer l E
  let c := integralConstantToCompletionOfUniverses l E W
  let A := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
  let B := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let η := toSheafify J ((Functor.const W.ProEtᵒᵖ).obj A)
  let η' := toSheafify J ((Functor.const W.ProEtᵒᵖ).obj B)
  let q : A ⟶ B := CommRingCat.ofHom
    (RingHom.ulift (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))))
  have hc := congrArg (fun h ↦ h.hom.app U ((η.app U (ULift.up π)) ^ (n + 1)))
    (limit.lift_π (integralConstantConeOfUniverses l E W) (op n))
  change (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app U
    (c.hom.app U ((η.app U (ULift.up π)) ^ (n + 1))) = _ at hc
  rw [map_pow] at hc
  rw [hc]
  have hn := congrArg (fun h ↦ h.app U (ULift.up π ^ (n + 1)))
    (toSheafify_naturality J ((Functor.const W.ProEtᵒᵖ).map q))
  change η'.app U (q (ULift.up π ^ (n + 1))) =
    (integralConstantQuotientOfUniverses l E W n).hom.app U
      (η.app U (ULift.up π ^ (n + 1))) at hn
  have ht : q (ULift.up π ^ (n + 1)) = 0 := by
    apply ULift.ext
    change Ideal.Quotient.mk _ (π ^ (n + 1)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Padic.coefficientExtensionIdeal]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton π)) _
  have ha : (η.app U (ULift.up π)) ^ (n + 1) =
      η.app U (ULift.up π ^ (n + 1)) := (map_pow (η.app U).hom _ _).symm
  erw [ha, ← hn, ht, map_zero]

private lemma projection_apply (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U) :
    (projection l E W n).val.app U x =
      (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app U x := by
  change (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app U x * 1 = _
  exact mul_one _

private lemma multiplication_apply (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U) :
    (multiplication l E W n).val.app U x = x * (scalar l E W U) ^ (n + 1) := by
  have hmul (y : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U) :
      (globalSectionMultiplication (completedIntegralCommRingSheafUnrestricted l E W)
        (uniformizer l E W)).val.app U y = y * scalar l E W U := by rfl
  have hp (k : ℕ) :
      (endoPow (globalSectionMultiplication
        (completedIntegralCommRingSheafUnrestricted l E W) (uniformizer l E W)) k).val.app U
          x = x * (scalar l E W U) ^ k := by
    induction k with
    | zero => change x = x * _ ^ 0; simp
    | succ k ih =>
      change (globalSectionMultiplication (completedIntegralCommRingSheafUnrestricted l E W)
        (uniformizer l E W)).val.app U
          ((endoPow (globalSectionMultiplication
            (completedIntegralCommRingSheafUnrestricted l E W) (uniformizer l E W)) k).val.app U
              x) = _
      rw [hmul, ih, pow_succ, mul_assoc]
  exact hp (n + 1)

/-- The actual projection kills the indicated uniformizer power.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement).
Proof: compose the constant-to-limit map with its nth projection. This is the constant
quotient homomorphism, which kills t^(n+1); multiplication then kills every section. -/
theorem multiplication_projection (n : ℕ) :
    multiplication l E W n ≫ projection l E W n = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U at x
  change (projection l E W n).val.app U ((multiplication l E W n).val.app U x) = 0
  rw [projection_apply, multiplication_apply, map_mul, scalar_projection_zero, mul_zero]

/-- The canonical cokernel comparison, fixed by the actual projection.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def quotientComparison (n : ℕ) :
    principalQuotient (completedIntegralCommRingSheafUnrestricted l E W)
      (uniformizer l E W) n ⟶ residue l E W n :=
  cokernel.desc (multiplication l E W n) (projection l E W n) (multiplication_projection l E W n)

/-- The quotient augmentation is zero on the shifted summand and pi_n on degree zero.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def augmentation (n : ℕ) : koszul l E W n ⟶
    (CochainComplex.singleFunctor (Modules l E W) 0).obj (residue l E W n) :=
  principalAugmentation (completedIntegralCommRingSheafUnrestricted l E W)
    (uniformizer l E W) n ≫
      (CochainComplex.singleFunctor (Modules l E W) 0).map (quotientComparison l E W n)

/-- Total tensor with P in the first variable, using the recorded direct-sum total.
Source: Stacks 06YM (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def tensorWith (P : CochainComplex (Modules l E W) ℤ) :
    CochainComplex (Modules l E W) ℤ ⥤ CochainComplex (Modules l E W) ℤ :=
  (SheafOfModules.KFlatTotalTensorModel.tensor.{t + 1, t, max u (t + 1)}
    (completedIntegralCommRingSheafUnrestricted l E W)).map₂CochainComplex.obj P

/-- The source strict tower, whose successive transition is id_P tensor (t,1).
Source: Stacks 0A0E (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def sourceTower (P : CochainComplex (Modules l E W) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (Modules l E W) ℤ :=
  principalKoszulTower (completedIntegralCommRingSheafUnrestricted l E W)
    (uniformizer l E W) ⋙ tensorWith l E W P

/-- The actual quotient map on the restricted quotient modules.
Source: Stacks 099L (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def residueStep (n : ℕ) : residue l E W (n + 1) ⟶ residue l E W n where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (residue l E W (n + 1)).val.obj U)
        (Y := (residue l E W n).val.obj U)
        { toFun := (integralCoefficientSheafTransition l E W n).hom.app U
          map_add' := map_add _
          map_smul' := by
            intro r x
            let p (k : ℕ) : completedIntegralCoefficientSheafUnrestricted l E W ⟶
                integralCoefficientSheaf l E W k :=
              limit.π (integralCoefficientSheafSystem l E W) (op k)
            change (integralCoefficientSheaf l E W (n + 1)).obj.obj U at x
            change (integralCoefficientSheafTransition l E W n).hom.app U
              ((p (n + 1)).hom.app U r
                * x) =
              (p n).hom.app U r *
                (integralCoefficientSheafTransition l E W n).hom.app U x
            rw [map_mul]
            congr 1
            have h := limit.w (integralCoefficientSheafSystem l E W)
              (homOfLE n.le_succ).op
            simp only [integralCoefficientSheafSystem,
              Functor.ofOpSequence_map_homOfLE_succ] at h
            exact ConcreteCategory.congr_hom (congrArg (fun h ↦ h.hom.app U) h) r }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom
          ((integralCoefficientSheafTransition l E W n).hom.naturality f) x }

/-- The strict target tower uses actual quotient maps before any localization.
Source: Stacks 099L (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def targetTower (P : CochainComplex (Modules l E W) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (Modules l E W) ℤ :=
  Functor.ofOpSequence (residueStep l E W) ⋙
    CochainComplex.singleFunctor (Modules l E W) 0 ⋙ tensorWith l E W P

/-- Strict augmentation compatibility with adjacent quotient maps.
Source: Stacks 093M, 0A0E (blueprint: lem-a1-principal-koszul-strict-replacement).
Proof: on degree zero the equality is pi_(n+1) followed by q = pi_n, the limit-cone
equation. In degree -1 both augmentations vanish. Tensor functoriality preserves it. -/
theorem augmentation_compatible (P : CochainComplex (Modules l E W) ℤ) (n : ℕ) :
    (sourceTower l E W P).map (homOfLE n.le_succ).op ≫
        (tensorWith l E W P).map (augmentation l E W n) =
      (tensorWith l E W P).map (augmentation l E W (n + 1)) ≫
        (targetTower l E W P).map (homOfLE n.le_succ).op := by
  have hp : projection l E W (n + 1) ≫ residueStep l E W n = projection l E W n := by
    apply (residue l E W n).unitHomEquiv.injective
    rw [SheafOfModules.unitHomEquiv_comp_apply]
    simp only [projection, Equiv.apply_symm_apply]
    ext U
    change (integralCoefficientSheafTransition l E W n).hom.app U 1 = 1
    exact map_one _
  have hq :
      cokernel.desc _ (cokernel.π (multiplication l E W n))
          (principalQuotient_transition_zero
            (completedIntegralCommRingSheafUnrestricted l E W) (uniformizer l E W) n) ≫
        quotientComparison l E W n =
      quotientComparison l E W (n + 1) ≫ residueStep l E W n := by
    apply (cancel_epi (cokernel.π (multiplication l E W (n + 1)))).1
    simpa only [quotientComparison, cokernel.π_desc_assoc, cokernel.π_desc] using hp.symm
  simp only [sourceTower, targetTower, Functor.comp_map, principalKoszulTower,
    Functor.ofOpSequence_map_homOfLE_succ]
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (tensorWith l E W P).map
  change
      (principalKoszulTransition (completedIntegralCommRingSheafUnrestricted l E W)
        (uniformizer l E W) n) ≫ augmentation l E W n =
      augmentation l E W (n + 1) ≫
        (CochainComplex.singleFunctor _ 0).map (residueStep l E W n)
  unfold augmentation
  rw [← Category.assoc, principalAugmentation_naturality]
  simp only [Category.assoc]
  apply congrArg (fun z ↦ principalAugmentation
    (completedIntegralCommRingSheafUnrestricted l E W) (uniformizer l E W) (n + 1) ≫ z)
  change (CochainComplex.singleFunctor (Modules l E W) 0).map _ ≫
      (CochainComplex.singleFunctor (Modules l E W) 0).map _ = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (CochainComplex.singleFunctor (Modules l E W) 0).map hq

/-- The required strict tower morphism, with components id_P tensor epsilon_n.
Source: Stacks 099L (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def comparison (P : CochainComplex (Modules l E W) ℤ) :
    sourceTower l E W P ⟶ targetTower l E W P :=
  NatTrans.ofOpSequence (fun n ↦ (tensorWith l E W P).map (augmentation l E W n))
    (augmentation_compatible l E W P)

/-- The coefficient datum and its explicit principal two-term free resolutions.
Source: Stacks 00PD, 0657, 099L (blueprint: lem-a1-principal-koszul-strict-replacement).
Proof: the coefficient DVR theorem gives a nonzero uniformizer generating the maximal
ideal. Principal ideals are finitely generated, so A is Noetherian. The finite-quotient
theorem gives every positive quotient finite. Since the extending absolute value of ell
is less than one, ell lies in (t), killing A/(t). Multiplication by any t^(n+1) is
injective in the domain A; its image is precisely the kernel of the quotient map.
The resulting two-term resolution has free rank-one terms and is bounded, proving
perfectness of every quotient. These are exactly the fields of AdicCoefficientDatum. -/
theorem coefficient_datum :
    ∃ d : AlgebraicGeometry.Scheme.AdicCoefficientDatum
        (Padic.coefficientExtensionIntegers l E),
      d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E} ∧
      ∀ n : ℕ,
        Function.Injective (fun a : Padic.coefficientExtensionIntegers l E ↦
          Padic.coefficientExtensionUniformizer l E ^ (n + 1) * a) ∧
        Function.Exact (fun a : Padic.coefficientExtensionIntegers l E ↦
          Padic.coefficientExtensionUniformizer l E ^ (n + 1) * a)
          (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) ∧
        Function.Surjective
          (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) := by
  let A := Padic.coefficientExtensionIntegers l E
  let t := Padic.coefficientExtensionUniformizer l E
  have hd := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsPrincipalIdealRing A := hd.2.2.2.2.2.2.2.2.1
  have hf (n : ℕ) : Finite (A ⧸ Ideal.span {t} ^ (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  have ht : t ≠ 0 := by
    intro ht
    have hgen : Ideal.span {t} = Padic.coefficientExtensionMaximalIdeal l E :=
      hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    have hm := hd.2.2.2.2.2.2.2.2.2.1
    apply hm
    exact hgen.symm.trans (by rw [ht, Ideal.span_singleton_zero])
  refine ⟨{ ideal := Ideal.span {t}
            noetherian := inferInstance
            finitelyGenerated := Submodule.fg_span_singleton _
            quotientTorsion := ?_
            quotientPerfect := ?_
            quotientFinite := hf }, rfl, ?_⟩
  · have : Finite (A ⧸ Ideal.span {t}) := by simpa only [Nat.zero_add, pow_one] using hf 0
    intro x
    exact (isOfFinAddOrder_of_finite x).exists_nsmul_eq_zero
  · intro n hn
    obtain ⟨P, hge, hle, hfree, _, hrest⟩ :=
      (AlgebraicGeometry.standard_quotients_perfect l n hn).2 E
    obtain ⟨_, _, _, φ, ε, hε, _⟩ := hrest
    have hqi : QuasiIso ε := by
      apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ ε).1
      rw [hε]
      infer_instance
    let := HasDerivedCategory.standard (ModuleCat.{u} A)
    unfold AlgebraicGeometry.Scheme.adicQuotientPerfect
    refine ⟨P, -1, 0, hge, hle, ?_, ⟨(asIso (DerivedCategory.Q.map ε)).symm⟩⟩
    intro i
    have := (hfree i).1
    exact ⟨inferInstance, (hfree i).2⟩
  · intro n
    refine ⟨?_, ?_, Ideal.Quotient.mk_surjective⟩
    · intro x y hxy
      exact mul_left_cancel₀ (pow_ne_zero (n + 1) ht) hxy
    · intro y
      rw [Ideal.Quotient.eq_zero_iff_mem, Padic.coefficientExtensionIdeal,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, ha.symm⟩
      · rintro ⟨a, ha⟩
        exact ⟨a, ha.symm⟩

private theorem shortExact_of_app {C : Type (t + 1)} [Category.{t} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max u (t + 1)}]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u (t + 1)}))
    (h : ∀ U, ((S.map (sheafToPresheaf J AddCommGrpCat.{max u (t + 1)})).map
      ((evaluation Cᵒᵖ AddCommGrpCat.{max u (t + 1)}).obj U)).ShortExact) :
    S.ShortExact := by
  let F := sheafToPresheaf J AddCommGrpCat.{max u (t + 1)}
  let K := S.map F
  have he : K.Exact := by
    apply (ShortComplex.exact_iff_isZero_homology _).2
    rw [IsZero.iff_id_eq_zero]
    apply NatTrans.ext
    funext U
    have hz := (ShortComplex.exact_iff_isZero_homology _).1 (h U).exact
    have hz' : IsZero (K.homology.obj U) :=
      hz.of_iso (K.mapHomologyIso
        ((evaluation Cᵒᵖ AddCommGrpCat.{max u (t + 1)}).obj U)).symm
    exact hz'.eq_of_src _ _
  have hm : Mono K.f := (NatTrans.mono_iff_mono_app _).2 (fun U ↦ (h U).mono_f)
  have hg : Epi K.g := (NatTrans.epi_iff_epi_app _).2 (fun U ↦ (h U).epi_g)
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful F ⟨he⟩

/-- Exactness through the specified completed projection, and the canonical quotient iso.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement).
Proof: uniformizer regularity gives injectivity on sections. The projection kernel
consists of divisible sections, and the constant quotient surjection factors through
completion. These three sectionwise assertions give a short exact sequence of additive
sheaves, reflected by the faithful exact forgetful functor from module sheaves.
Its cokernel universal property makes the specified quotient comparison invertible. -/
theorem completed_exact (n : ℕ) :
    (ShortComplex.mk (multiplication l E W n) (projection l E W n)
      (multiplication_projection l E W n)).ShortExact ∧
      IsIso (quotientComparison l E W n) := by
  let S := ShortComplex.mk (multiplication l E W n) (projection l E W n)
    (multiplication_projection l E W n)
  have hs : S.ShortExact := by
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
      (SheafOfModules.toSheaf.{max u (t + 1)}
        (completedIntegralCoefficientSheafUnrestricted l E W))
    apply shortExact_of_app.{t, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
    intro U
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · apply (ShortComplex.ab_exact_iff _).2
      intro x hx
      change (projection l E W n).val.app U x = 0 at hx
      rw [projection_apply] at hx
      obtain ⟨y, hy⟩ := AlgebraicGeometry.ProEtale.completedIntegralProjection_divisible
        l E W n U x hx
      refine ⟨y, ?_⟩
      change (multiplication l E W n).val.app U y = x
      exact (multiplication_apply l E W n U y).trans
        ((completedIntegralCoefficient_mul_commUnrestricted l E W U _ _).trans hy.symm)
    · apply (AddCommGrpCat.mono_iff_injective _).2
      intro x y hxy
      apply AlgebraicGeometry.ProEtale.completedIntegralScalar_regular l E W (n + 1) U
      change (multiplication l E W n).val.app U x =
        (multiplication l E W n).val.app U y at hxy
      rw [multiplication_apply, multiplication_apply] at hxy
      exact (completedIntegralCoefficient_mul_commUnrestricted l E W U _ _).trans
        (hxy.trans (completedIntegralCoefficient_mul_commUnrestricted l E W U _ _))
    · apply (AddCommGrpCat.epi_iff_surjective _).2
      intro x
      obtain ⟨y, hy⟩ := AlgebraicGeometry.ProEtale.constantQuotient_surjective l E W n U x
      refine ⟨(integralConstantToCompletionOfUniverses l E W).hom.app U y, ?_⟩
      change (projection l E W n).val.app U _ = x
      rw [projection_apply]
      exact (congrArg (fun h ↦ h.hom.app U y)
        (limit.lift_π (integralConstantConeOfUniverses l E W) (op n))).trans hy
  refine ⟨hs, ?_⟩
  change IsIso ((cokernelIsCokernel (multiplication l E W n)).coconePointUniqueUpToIso
    hs.gIsCokernel).hom
  infer_instance

private lemma koszul_flat (n : ℕ) :
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := completedIntegralCommRingSheafUnrestricted l E W) ((koszul l E W n).X i) := by
  let R := completedIntegralCommRingSheafUnrestricted l E W
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let : MonoidalCategory (Modules l E W) := SheafOfModules.monoidalCategory R
  let : MonoidalPreadditive (Modules l E W) := SheafOfModules.tensorPreadditive R
  let A := Modules l E W
  let U := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)
  let D := (CochainComplex.singleFunctor A 0).obj U
  let f := (CochainComplex.singleFunctor A 0).map (multiplication l E W n)
  have hu : ObjectProperty.flat U := ObjectProperty.prop_unit ObjectProperty.flat
  intro i
  have hf : ObjectProperty.flat ((koszul l E W n).X i) := by
    let e := HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl
    by_cases hi : i = 0
    · subst i
      have hz : IsZero (D.X (0 + 1)) :=
        HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U _ (by omega)
      let e' := e ≪≫ (isoZeroBiprod hz).symm ≪≫
        HomologicalComplex.singleObjXSelf (.up ℤ) 0 U
      exact ObjectProperty.prop_of_iso ObjectProperty.flat e'.symm hu
    · by_cases hm : i = -1
      · subst i
        have hz : IsZero (D.X (-1)) :=
          HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U _ (by omega)
        let e' := e ≪≫ (isoBiprodZero hz).symm ≪≫
          HomologicalComplex.singleObjXSelf (.up ℤ) 0 U
        exact ObjectProperty.prop_of_iso ObjectProperty.flat e'.symm hu
      · apply ObjectProperty.flat_of_isZero
        apply (CochainComplex.mappingCone.isZero_X_iff f i).2
        exact ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U _ (by omega),
          HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U i hi⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R _).symm hf.2

private lemma koszul_bounded (n : ℕ) : (koszul l E W n).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  apply (CochainComplex.mappingCone.isZero_X_iff _ i).2
  exact ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ _ (by omega),
    HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ _ (by omega)⟩

private lemma augmentation_quasiIso (n : ℕ) : QuasiIso (augmentation l E W n) := by
  obtain ⟨hs, hq⟩ := completed_exact l E W n
  have hm := hs.mono_f
  let F := CochainComplex.singleFunctor (Modules l E W) 0
  let f := multiplication l E W n
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  have : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits (HomologicalComplex.single _ (.up ℤ) 0))
  have : PreservesFiniteColimits F :=
    inferInstanceAs (PreservesFiniteColimits (HomologicalComplex.single _ (.up ℤ) 0))
  have : QuasiIso (principalAugmentation
      (completedIntegralCommRingSheafUnrestricted l E W) (uniformizer l E W) n) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex (hS.map_of_exact F)
  unfold augmentation
  infer_instance

private lemma quasiIso_conjugate {A : Type*} [Category A] [Abelian A]
    {X X' Y Y' : CochainComplex A ℤ} (e₁ : X ≅ X') (e₂ : Y ≅ Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (hn : f ≫ e₂.hom = e₁.hom ≫ g)
    [QuasiIso g] : QuasiIso f := by
  have hf : f = e₁.hom ≫ g ≫ e₂.inv := by
    simpa only [Category.assoc] using (Iso.eq_comp_inv e₂).2 hn
  rw [hf]
  infer_instance

private lemma tensor_replacement {C : Type (t + 1)} [Category.{t} C]
    [EssentiallySmall.{max u (t + 1)} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u (t + 1)})
    (P Q Q' : CochainComplex (SheafOfModules.KFlatTotalTensorModel.Modules R) ℤ)
    (f : Q ⟶ Q') (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q)
    (hPflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X i))
    (hQflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X i))
    (hf : QuasiIso f) :
    QuasiIso (((SheafOfModules.KFlatTotalTensorModel.tensor R).map₂CochainComplex.obj P).map f) ∧
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
        ((SheafOfModules.KFlatTotalTensorModel.total R).obj (P, Q)) ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R)
        (((SheafOfModules.KFlatTotalTensorModel.total R).obj (P, Q)).X i) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  have (M : SheafOfModules.KFlatTotalTensorModel.Modules R) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (MonoidalCategory.tensorLeft M)
  have (M : SheafOfModules.KFlatTotalTensorModel.Modules R) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  refine ⟨?_, ?_, SheafOfModules.KFlatTotalTensorModel.totalFlat R P Q hPflat hQflat⟩
  · have := kFlatTensorPreservesQuasiIsoIndependentCoefficients R P hP f hf
    exact quasiIso_conjugate (CochainComplex.Monoidal.braiding P Q)
      (CochainComplex.Monoidal.braiding P Q') _ ((koszulTensorFunctor R P).map f)
      (CochainComplex.Monoidal.braiding_naturality_right (K := P) f)
  · intro H hH
    exact fun i ↦ (hQ _ (hP H hH) i).of_iso (HomologicalComplex.associator H P Q)

/-- Principal Koszul tensor levels are flat-term K-flat replacements of actual reductions.
Source: Stacks 093M, 06YQ, 06YP, 07A2, 099L
(blueprint: lem-a1-principal-koszul-strict-replacement).
Proof: completed_exact identifies H^0 of Q with S via the actual projection and makes
H^-1 zero, so epsilon is a quasi-isomorphism. Its two unit terms are flat, and the
bounded-flat theorem makes Q K-flat. K-flat tensor invariance and the signed symmetry
give a quasi-isomorphism id_P tensor epsilon. The total-tensor model theorem makes
P tensor Q K-flat with flat terms, even for unbounded P. The target is precisely the
strict reduction tower on the K-flat representative P, with the actual quotient maps;
finite constant coefficients identify it with the adic datum's reduction tower. -/
theorem principal_koszul_strict_replacement
    (P : CochainComplex (Modules l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i)) :
    ∀ n : ℕ, QuasiIso ((comparison l E W P).app (op n)) ∧
      CochainComplex.IsKFlatIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E W)
        ((sourceTower l E W P).obj (op n)) ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := completedIntegralCommRingSheafUnrestricted l E W)
        (((sourceTower l E W P).obj (op n)).X i) := by
  intro n
  have := koszul_bounded l E W n
  have hQ := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    (completedIntegralCommRingSheafUnrestricted l E W) (koszul l E W n) 0
    (koszul_flat l E W n)
  exact tensor_replacement (completedIntegralCommRingSheafUnrestricted l E W)
    P (koszul l E W n) _ (augmentation l E W n) hP hQ hflat (koszul_flat l E W n)
    (augmentation_quasiIso l E W n)

/-- The strict source-tower map induced by f tensor identity.
Source: Stacks 06YM (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def sourceTowerMap {P P' : CochainComplex (Modules l E W) ℤ} (f : P ⟶ P') :
    sourceTower l E W P ⟶ sourceTower l E W P' :=
  Functor.whiskerLeft
    (principalKoszulTower (completedIntegralCommRingSheafUnrestricted l E W)
      (uniformizer l E W))
    ((SheafOfModules.KFlatTotalTensorModel.tensor.{t + 1, t, max u (t + 1)}
      (completedIntegralCommRingSheafUnrestricted l E W)).map₂CochainComplex.map f)

/-- The strict actual reduction-tower map induced by f tensor identity.
Source: Stacks 06YM (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def targetTowerMap {P P' : CochainComplex (Modules l E W) ℤ} (f : P ⟶ P') :
    targetTower l E W P ⟶ targetTower l E W P' :=
  Functor.whiskerLeft
    (Functor.ofOpSequence (residueStep l E W) ⋙
      CochainComplex.singleFunctor (Modules l E W) 0)
    ((SheafOfModules.KFlatTotalTensorModel.tensor.{t + 1, t, max u (t + 1)}
      (completedIntegralCommRingSheafUnrestricted l E W)).map₂CochainComplex.map f)

/-- Naturality in the representative as an equality of strict tower morphisms.
Source: Stacks 06YM, 099L (blueprint: lem-a1-principal-koszul-strict-replacement).
Proof: both composites on a homogeneous tensor p tensor q send it to
f(p) tensor epsilon(q). With a transition in place of epsilon both send it to
f(p) tensor tau(q). Balanced tensor functoriality and total direct sums extend
these formulas to equalities of chain maps. This works for every chain map, hence
in particular for chain maps between the flat-term K-flat representatives above. -/
theorem comparison_naturality
    {P P' : CochainComplex (Modules l E W) ℤ} (f : P ⟶ P') :
    sourceTowerMap l E W f ≫ comparison l E W P' =
      comparison l E W P ≫ targetTowerMap l E W f := by
  apply NatTrans.ext
  funext n
  dsimp only [NatTrans.comp_app, sourceTowerMap, targetTowerMap,
    Functor.whiskerLeft_app, comparison, NatTrans.ofOpSequence_app]
  exact ((SheafOfModules.KFlatTotalTensorModel.tensor
    (completedIntegralCommRingSheafUnrestricted l E W)).map₂CochainComplex.map f).naturality
      (augmentation l E W n.unop) |>.symm

end WeilConjectures.PrincipalKoszulStrictReplacement
