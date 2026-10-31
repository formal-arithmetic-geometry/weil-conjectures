/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralScalarData
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Constant values and prescribed integral bases on connected schemes

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 4.2.12,
Definition 6.8.1 and Lemma 6.8.2(1), printed pp. 30 and 58--59
(blueprint: lem-pur-connected-adic-integral-basis).

The positive quotient exponent is n+1. The finite direct sum is represented by its
finite product in module sheaves. The basis is prescribed, rather than chosen by the theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped BigOperators

namespace WeilConjectures

private def continuousRingPresheaf (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    X.ProEtᵒᵖ ⥤ CommRingCat.{max u (t + 1)} where
  obj V := CommRingCat.of C(V.unop.left, A)
  map h := CommRingCat.ofHom
    (ContinuousMap.compRightAlgHom A A h.unop.left.base.hom).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private def constantToContinuous (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ continuousRingPresheaf X A where
  app V := CommRingCat.ofHom (ContinuousMap.C : A →+* C(V.unop.left, A))
  naturality _ _ h := by ext; rfl

private theorem continuousRingPresheaf_isSheaf (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (continuousRingPresheaf X A) := by
  let G := forget CommRingCat.{max u (t + 1)}
  let : HasLimitsOfSize.{t, t + 1} CommRingCat.{max u (t + 1)} :=
    hasLimitsOfSizeShrink.{_, _, t + 1, t} _
  let : PreservesLimitsOfSize.{t, t + 1} G :=
    preservesLimitsOfSize_shrink.{t + 1, 0, t, max u (t + 1)} G
  rw [Presheaf.isSheaf_iff_isSheaf_comp (Scheme.ProEt.topology X)
    (continuousRingPresheaf X A) G]
  exact (Scheme.ProEt.forget X ⋙ Over.forget X).op_comp_isSheaf_of_isSheaf
    (Scheme.ProEt.topology X) Scheme.proetaleTopology (continuousMapPresheaf A)
    ((isSheaf_fpqcTopology_continuousMapPresheaf A).of_le
      Scheme.proetaleTopology_le_fpqcTopology)

private theorem constantToContinuous_locallyInjective
    (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) (constantToContinuous X A) where
  equalizerSieve_mem {V} a b h := by
    classical
    by_cases he : IsEmpty V.unop.left
    · let _ := he
      exact (Scheme.ProEt.topology X).superset_covering bot_le
        (Scheme.ProEt.bot_mem_topology V.unop)
    · obtain ⟨x⟩ := not_isEmpty_iff.mp he
      have hab : a = b := congrArg (fun f : C(V.unop.left, A) ↦ f x) h
      subst b
      simp

private theorem constantToContinuous_locallySurjective
    (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (constantToContinuous X A) where
  imageSieve_mem {V} f := by
    classical
    change C(V.left, A) at f
    let U (x : V.left) : V.left.Opens :=
      ⟨f ⁻¹' {f x}, (isOpen_discrete {f x}).preimage f.continuous⟩
    let W (x : V.left) : X.ProEt := Scheme.ProEt.mk ((U x).ι ≫ V.hom)
    let i (x : V.left) : W x ⟶ V :=
      MorphismProperty.Over.homMk (U x).ι rfl
    have hm : Presieve.ofArrows W i ∈ Scheme.ProEt.precoverage X V := by
      change (Presieve.ofArrows W i).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
        Scheme.proetalePrecoverage V.left
      rw [Presieve.map_ofArrows]
      apply Scheme.zariskiPrecoverage_le_propQCPrecoverage
      rw [Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨?_, ?_⟩
      · intro x
        exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
      · intro x
        change IsOpenImmersion (U x).ι
        infer_instance
    apply (Scheme.ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hm)
    rw [Sieve.generate_le_iff]
    rintro Y g ⟨x⟩
    refine ⟨f x, ?_⟩
    apply ContinuousMap.ext
    intro y
    exact y.property.symm



private theorem connected_constant_bijective (X : Scheme.{t}) [ConnectedSpace X]
    (A : Type (max u (t + 1))) [CommRing A] :
    Function.Bijective ((toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app
        (op (Scheme.ProEt.mk (𝟙 X)))) := by
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective
      CommRingCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let J := Scheme.ProEt.topology X
  let P := (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)
  let F := continuousRingPresheaf X A
  let φ := constantToContinuous X A
  have hF : Presheaf.IsSheaf J F := continuousRingPresheaf_isSheaf X A
  have : Presheaf.IsLocallyInjective J φ := constantToContinuous_locallyInjective X A
  have : Presheaf.IsLocallySurjective J φ := constantToContinuous_locallySurjective X A
  have : IsIso ((presheafToSheaf J CommRingCat.{max u (t + 1)}).map φ) :=
    (J.W_iff φ).mp (J.W_of_isLocallyBijective φ)
  have : IsIso (sheafifyMap J φ) := inferInstance
  let e : sheafify J P ≅ F := asIso (sheafifyMap J φ) ≪≫ (isoSheafify J hF).symm
  have he : toSheafify J P ≫ e.hom = φ := by
    dsimp [e]
    rw [← Category.assoc, ← toSheafify_naturality]
    simp only [toSheafify_naturality, isoSheafify_inv, Category.assoc,
      sheafifyMap_sheafifyLift, toSheafify_sheafifyLift]
    exact Category.comp_id φ
  let U := op (Scheme.ProEt.mk (𝟙 X))
  let θ : (sheafify J P).obj U ≃+* C(X, A) := (e.app U).commRingCatIsoToRingEquiv
  have hθ (a : A) : θ ((toSheafify J P).app U a) = ContinuousMap.const X a :=
    congrArg (fun k ↦ k.app U a) he
  let x : X := Classical.choice inferInstance
  constructor
  · intro a b h
    have hh := congrArg (fun z ↦ θ z x) h
    change θ ((toSheafify J P).app U a) x = θ ((toSheafify J P).app U b) x at hh
    simpa only [hθ, ContinuousMap.const_apply] using hh
  · intro s
    refine ⟨θ s x, θ.injective ?_⟩
    rw [hθ]
    apply ContinuousMap.ext
    intro y
    have hlc := (IsLocallyConstant.iff_continuous _).mpr (θ s).continuous
    exact hlc.apply_eq_of_preconnectedSpace x y

section
universe cs vs rs is js
private theorem ringSheafLimit_ext
    {C : Type cs} [Category.{vs} C] {J : GrothendieckTopology C}
    {I : Type is} [Category.{js} I] (D : I ⥤ Sheaf J RingCat.{rs})
    [HasLimit D] [PreservesLimit D (sheafToPresheaf J RingCat)]
    (U : Cᵒᵖ)
    [PreservesLimit (D ⋙ sheafToPresheaf J RingCat) ((evaluation _ _).obj U)]
    [PreservesLimit ((D ⋙ sheafToPresheaf J RingCat) ⋙ (evaluation _ _).obj U)
      (forget RingCat)]
    (x y : (limit D).obj.obj U)
    (h : ∀ i, ((limit.π D i).hom.app U) x = ((limit.π D i).hom.app U) y) : x = y := by
  let h₁ := isLimitOfPreserves (sheafToPresheaf J RingCat) (limit.isLimit D)
  let h₂ := isLimitOfPreserves ((evaluation _ _).obj U) h₁
  exact Concrete.isLimit_ext _ h₂ x y h

end

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{t})

private noncomputable def scalarValue (U : Y.ProEtᵒᵖ) :
    Padic.coefficientExtensionIntegers l E →+*
      (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U :=
  ((integralConstantToCompletionOfUniverses l E Y).hom.app U).hom.comp
    (((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U).hom.comp
      ULift.ringEquiv.symm.toRingHom)

private theorem scalarValue_projection (U : Y.ProEtᵒᵖ)
    (x : Padic.coefficientExtensionIntegers l E) (n : ℕ) :
    (completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U
      (scalarValue l E Y U x) = integralScalarFiniteConstant l E Y n U x := by
  have hc := congrArg (fun f ↦ f.hom.app U
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
          (ULift.up x)))
    (limit.lift_π (integralConstantConeOfUniverses l E Y) (op n))
  let A := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
  let B := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let q : A ⟶ B := CommRingCat.ofHom
    (RingHom.ulift (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))))
  have hn := congrArg (fun f ↦ f.app U (ULift.up x))
    (toSheafify_naturality (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map q))
  exact hc.trans hn.symm

private theorem scalarValue_naturality {U V : Y.ProEtᵒᵖ} (f : U ⟶ V)
    (x : Padic.coefficientExtensionIntegers l E) :
    (completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f
      (scalarValue l E Y U x) = scalarValue l E Y V x := by
  let α := Functor.whiskerRight
    (toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))))
    (forget₂ CommRingCat RingCat) ≫ (integralConstantToCompletionOfUniverses l E Y).hom
  exact (ConcreteCategory.congr_hom (α.naturality f) (ULift.up x)).symm

private theorem scalarValue_eq (U : Y.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    scalarValue l E Y U a = integralScalarConstant l E Y U a := by
  exact (integralScalarConstant_existsUnique l E Y U a).unique
    (scalarValue_projection l E Y U a)
    (integralScalarConstant_existsUnique l E Y U a).exists.choose_spec

private noncomputable def finiteConstantEquiv [ConnectedSpace Y] (n : ℕ) :
    Padic.coefficientExtensionRing l E (n + 1) ≃+*
      (integralCoefficientSheaf l E Y n).obj.obj (op (Scheme.ProEt.mk (𝟙 Y))) :=
  ULift.ringEquiv.symm.trans (RingEquiv.ofBijective
    ((toSheafify (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
          (op (Scheme.ProEt.mk (𝟙 Y)))).hom
    (connected_constant_bijective Y _))

private theorem finiteConstantEquiv_mk [ConnectedSpace Y] (n : ℕ)
    (a : Padic.coefficientExtensionIntegers l E) :
    finiteConstantEquiv l E Y n (Ideal.Quotient.mk _ a) =
      integralScalarFiniteConstant l E Y n (op (Scheme.ProEt.mk (𝟙 Y))) a := rfl

private theorem finiteConstantEquiv_transition [ConnectedSpace Y] (n : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 2)) :
    (integralCoefficientSheafTransition l E Y n).hom.app
        (op (Scheme.ProEt.mk (𝟙 Y))) (finiteConstantEquiv l E Y (n + 1) a) =
      finiteConstantEquiv l E Y n (Padic.coefficientExtensionTransition l E (n + 1) a) := by
  let q : CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l E (n + 2))) ⟶
      CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1))) :=
    CommRingCat.ofHom (RingHom.ulift (Padic.coefficientExtensionTransition l E (n + 1)))
  exact (congrArg (fun f ↦ f.app (op (Scheme.ProEt.mk (𝟙 Y))) (ULift.up a))
    (toSheafify_naturality (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map q))).symm

private noncomputable def residueValue [ConnectedSpace Y] (n : ℕ) :
    (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
      (op (Scheme.ProEt.mk (𝟙 Y))) →+* Padic.coefficientExtensionRing l E (n + 1) :=
  (finiteConstantEquiv l E Y n).symm.toRingHom.comp
    ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app
      (op (Scheme.ProEt.mk (𝟙 Y)))).hom

private theorem residueValue_transition [ConnectedSpace Y] (n : ℕ)
    (x : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
      (op (Scheme.ProEt.mk (𝟙 Y)))) :
    Padic.coefficientExtensionTransition l E (n + 1) (residueValue l E Y (n + 1) x) =
      residueValue l E Y n x := by
  apply (finiteConstantEquiv l E Y n).injective
  rw [← finiteConstantEquiv_transition]
  simp only [residueValue, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  have hw := limit.w (integralCoefficientSheafSystem l E Y)
    (homOfLE (Nat.le_succ n)).op
  have hm : (integralCoefficientSheafSystem l E Y).map
      (homOfLE (Nat.le_succ n)).op = integralCoefficientSheafTransition l E Y n := by
    simp only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ]
  rw [hm] at hw
  exact congrArg (fun f ↦ (f.hom.app (op (Scheme.ProEt.mk (𝟙 Y)))).hom x) hw

private theorem scalarValue_bijective [ConnectedSpace Y] :
    Function.Bijective (scalarValue l E Y (op (Scheme.ProEt.mk (𝟙 Y)))) := by
  classical
  let A := Padic.coefficientExtensionIntegers l E
  let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set A)
  have hc := (Padic.finite_module_adic_complete_and_hom.{u, u, u} l E).1 A
  let : IsAdicComplete I A := AdicCompletion.of_bijective_iff.mp hc.2.1
  let S := (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
    (op (Scheme.ProEt.mk (𝟙 Y)))
  let f : (n : ℕ) → S →+* A ⧸ I ^ n
    | 0 => by
      have : Subsingleton (A ⧸ I ^ 0) := by rw [pow_zero, Ideal.one_eq_top]; infer_instance
      exact
        { toFun := fun _ ↦ 0
          map_one' := Subsingleton.elim _ _
          map_mul' := fun _ _ ↦ Subsingleton.elim _ _
          map_zero' := rfl
          map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
    | n + 1 => residueValue l E Y n
  have hf : ∀ {m n : ℕ} (h : m ≤ n),
      (Ideal.Quotient.factorPow I h).comp (f n) = f m := by
    intro m n h
    ext x
    apply Eq.symm
    apply Ideal.Quotient.eq_factor_of_eq_factor_succ
      (fun _ _ h ↦ Ideal.pow_le_pow_right h) (fun n ↦ f n x)
    · intro n
      cases n with
      | zero =>
        have : Subsingleton (A ⧸ I ^ 0) := by rw [pow_zero, Ideal.one_eq_top]; infer_instance
        exact Subsingleton.elim _ _
      | succ n => exact (residueValue_transition l E Y n x).symm
    · exact h
  let g := (AdicCompletion.ofAlgEquiv I).symm.toRingHom.comp
    (AdicCompletion.liftRingHom I f hf)
  have hg (n : ℕ) (x : S) :
      Ideal.Quotient.mk (I ^ (n + 1)) (g x) = residueValue l E Y n x := by
    exact (AdicCompletion.mk_ofAlgEquiv_symm I (n + 1) _).trans
      (AdicCompletion.evalₐ_liftRingHom I f hf (n + 1) x)
  have hres (n : ℕ) (a : A) :
      residueValue l E Y n (scalarValue l E Y (op (Scheme.ProEt.mk (𝟙 Y))) a) =
        Ideal.Quotient.mk (I ^ (n + 1)) a := by
    apply (finiteConstantEquiv l E Y n).injective
    exact (finiteConstantEquiv l E Y n).apply_symm_apply _ |>.trans
      ((scalarValue_projection l E Y _ a n).trans (finiteConstantEquiv_mk l E Y n a).symm)
  constructor
  · intro a b hab
    apply congrFun (IsHausdorff.StrictMono.funext' I (f := fun _ : Unit ↦ a)
      (g := fun _ : Unit ↦ b) (a := Nat.succ) (fun _ _ h ↦ Nat.succ_lt_succ h) ?_) ()
    intro n _
    rw [← hres n a, ← hres n b, hab]
  · intro x
    refine ⟨g x, ?_⟩
    apply ringSheafLimit_ext (integralCoefficientSheafSystem l E Y) _
    rintro ⟨n⟩
    have hp := scalarValue_projection l E Y (op (Scheme.ProEt.mk (𝟙 Y))) (g x) n
    change ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app _).hom
      (scalarValue l E Y _ (g x)) = _ at hp
    refine hp.trans ?_
    have h := congrArg (finiteConstantEquiv l E Y n) (hg n x)
    change finiteConstantEquiv l E Y n (Ideal.Quotient.mk _ (g x)) = _ at h
    rw [finiteConstantEquiv_mk] at h
    dsimp only [residueValue, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom] at h
    rw [RingEquiv.apply_symm_apply] at h
    exact h

private theorem scalarValue_map
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (U : Y.ProEtᵒᵖ) (x : Padic.coefficientExtensionIntegers l E) :
    (completedCoefficientMap l E L ι Y).hom.app U (scalarValue l E Y U x) =
      scalarValue l L Y U (integralScalarIntegerInclusion l E L ι x) := by
  apply ringSheafLimit_ext (integralCoefficientSheafSystem l L Y) U
  intro n
  have hφ := congrArg (fun f ↦ f.hom.app U (scalarValue l E Y U x))
    ((completedCoefficientMap_existsUnique l E L ι Y).exists.choose_spec n.unop)
  change (completedIntegralCommRingProjectionUnrestricted l L Y n.unop).hom.app U
    ((completedCoefficientMap l E L ι Y).hom.app U (scalarValue l E Y U x)) =
    (integralScalarQuotientSheafMap l E L ι Y n.unop).hom.app U
      ((completedIntegralCommRingProjectionUnrestricted l E Y n.unop).hom.app U
        (scalarValue l E Y U x)) at hφ
  erw [hφ, scalarValue_projection, scalarValue_projection]
  let q : CommRingCat.of
      (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n.unop + 1))) ⟶
      CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l L (n.unop + 1))) :=
    CommRingCat.ofHom (RingHom.ulift (integralScalarQuotientMap l E L ι n.unop))
  have hn := congrArg (fun f ↦ f.app U
    (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1)) x)))
    (toSheafify_naturality (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map q))
  exact hn.symm

section FreeDetection
universe ca cv cr
variable {C : Type ca} [Category.{cv} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{cr}) (T : C) (hT : IsTerminal T)
include hT

private theorem sections_eval_bijective (M : SheafOfModules.{cr} R) :
    Function.Bijective (fun s : M.sections ↦ s.val (op T)) := by
  constructor
  · intro s t h
    apply PresheafOfModules.sections_ext
    intro U
    exact ((s.property ((hT.from U.unop).op)).symm.trans
      (congrArg (fun x ↦ M.val.map ((hT.from U.unop).op) x) h)).trans
      (t.property ((hT.from U.unop).op))
  · intro x
    refine ⟨PresheafOfModules.sectionsMk
      (fun U ↦ M.val.map ((hT.from U.unop).op) x) ?_, ?_⟩
    · intro U V f
      have h : (hT.from U.unop).op ≫ f = (hT.from V.unop).op :=
        Quiver.Hom.unop_inj (hT.hom_ext _ _)
      rw [← PresheafOfModules.map_comp_apply, h]
    · change ((M.val.presheaf ⋙ forget _).map (hT.from T).op) x = x
      have h : (hT.from T).op = 𝟙 (op T) := by
        exact congrArg Quiver.Hom.op (hT.hom_ext _ (𝟙 T))
      rw [h]
      exact ConcreteCategory.congr_hom ((M.val.presheaf ⋙ forget _).map_id (op T)) x

private theorem unit_eval_bijective (M : SheafOfModules.{cr} R) :
    Function.Bijective (fun f : SheafOfModules.unit R ⟶ M ↦
      f.val.app (op T) (1 : R.obj.obj (op T))) :=
  (sections_eval_bijective R T hT M).comp M.unitHomEquiv.bijective

private theorem free_iso_of_global_bijective (d : ℕ)
    [HasFiniteBiproducts (SheafOfModules.{cr} R)]
    (N : SheafOfModules.{cr} R)
    (ψ : N ≅ ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit R)
    (f : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit R) ⟶ N)
    (hf : Function.Bijective (f.val.app (op T))) : IsIso f := by
  classical
  let P := ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit R
  have h₁ : Function.Bijective (fun a : SheafOfModules.unit R ⟶ P ↦ a ≫ f) := by
    have hp := unit_eval_bijective R T hT P
    have hn := unit_eval_bijective R T hT N
    constructor
    · intro a b h
      apply hp.injective
      apply hf.injective
      exact congrArg (fun k ↦ k.val.app (op T) (1 : R.obj.obj (op T))) h
    · intro a
      obtain ⟨x, hx⟩ := hf.surjective (a.val.app (op T) (1 : R.obj.obj (op T)))
      obtain ⟨b, hb⟩ := hp.surjective x
      refine ⟨b, hn.injective ?_⟩
      exact (congrArg (fun x ↦ f.val.app (op T) x) hb).trans hx
  let e : P ≅ ∐ fun _ : Fin d ↦ SheafOfModules.unit R := biproductIso _
  have hP : Function.Bijective (fun a : P ⟶ P ↦ a ≫ f) := by
    constructor
    · intro a b h
      apply (cancel_epi e.inv).mp
      apply Sigma.hom_ext
      intro i
      apply h₁.injective
      change a ≫ f = b ≫ f at h
      simp only [Category.assoc]
      rw [h]
    · intro a
      choose b hb using fun i ↦ h₁.surjective
        (Sigma.ι (fun _ : Fin d ↦ SheafOfModules.unit R) i ≫ e.inv ≫ a)
      refine ⟨e.hom ≫ Sigma.desc b, ?_⟩
      apply (cancel_epi e.inv).mp
      apply Sigma.hom_ext
      intro i
      simpa only [← Category.assoc, e.inv_hom_id_assoc, Sigma.ι_desc] using hb i
  obtain ⟨g, hg⟩ := hP.surjective ψ.inv
  let k := ψ.hom ≫ g
  have hk : k ≫ f = 𝟙 N := by simp only [k, Category.assoc, hg, ψ.hom_inv_id]
  have hk' : f ≫ k = 𝟙 P := by
    apply hP.injective
    simp only [Category.assoc, hk, Category.comp_id, Category.id_comp]
  exact ⟨⟨k, hk', hk⟩⟩
end FreeDetection

/-- The canonical completed coefficient inclusion, with commutativity forgotten so that
Mathlib's restriction of module scalars applies. This is the recorded scalar map c.
Source: Bhatt--Scholze 6.8.2(1)
(blueprint: lem-pur-connected-adic-integral-basis). -/
abbrev connectedAdicScalarRingMap
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{t}) :
    completedIntegralCoefficientSheafUnrestricted l E X ⟶
      completedIntegralCoefficientSheafUnrestricted l L X :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat RingCat)).map
    (completedIntegralScalarCoefficientMap l E L ι X)

private noncomputable def scalarColumn
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (b : Padic.coefficientExtensionIntegers l L) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
      (SheafOfModules.restrictScalars.{max u (t + 1)}
        (connectedAdicScalarRingMap l E L ι Y)).obj
          (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l L Y)) :=
  SheafOfModules.unitHomEquiv _ |>.symm
    (PresheafOfModules.sectionsMk (fun U ↦ scalarValue l L Y U b)
      (fun {_ _} k ↦ scalarValue_naturality l L Y k b))

private noncomputable def scalarForward
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (d : ℕ) (β : Fin d → Padic.coefficientExtensionIntegers l L) :=
  ∑ i : Fin d, Pi.π
    (fun _ : Fin d ↦ SheafOfModules.unit
      (completedIntegralCoefficientSheafUnrestricted l E Y)) i ≫
        scalarColumn l E Y L ι (β i)

private theorem scalarForward_apply
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (d : ℕ) (β : Fin d → Padic.coefficientExtensionIntegers l L)
    (U : Y.ProEtᵒᵖ)
    (x : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit
      (completedIntegralCoefficientSheafUnrestricted l E Y)).val.obj U) :
    (scalarForward l E Y L ι d β).val.app U x = ∑ i,
      (connectedAdicScalarRingMap l E L ι Y).hom.app U
        ((Pi.π (fun _ : Fin d ↦ SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l E Y)) i).val.app U x) *
            scalarValue l L Y U (β i) := by
  let E₀ := SheafOfModules.evaluation.{max u (t + 1)}
    (completedIntegralCoefficientSheafUnrestricted l E Y) U
  let : E₀.Additive := inferInstanceAs
    (SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ U).Additive
  change (E₀.map (∑ i : Fin d, Pi.π _ i ≫ scalarColumn l E Y L ι (β i))) x = _
  rw [Functor.map_sum]
  change (∑ i : Fin d, E₀.map (Pi.π _ i ≫ scalarColumn l E Y L ι (β i))).hom x = _
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  rfl

private noncomputable def freeCoordinates (d : ℕ) (U : Y.ProEtᵒᵖ) :
    (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit
      (completedIntegralCoefficientSheafUnrestricted l E Y)).val.obj U ≃
        (Fin d → (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U) :=
  (asIso (piComparison (SheafOfModules.evaluation.{max u (t + 1)}
    (completedIntegralCoefficientSheafUnrestricted l E Y) U)
      (fun _ : Fin d ↦ SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l E Y))) ≪≫
          ModuleCat.piIsoPi _).toLinearEquiv.toEquiv

private theorem freeCoordinates_apply (d : ℕ) (U : Y.ProEtᵒᵖ)
    (x : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit
      (completedIntegralCoefficientSheafUnrestricted l E Y)).val.obj U) (i : Fin d) :
    freeCoordinates l E Y d U x i =
      (Pi.π (fun _ : Fin d ↦ SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l E Y)) i).val.app U x := by
  change ((piComparison (SheafOfModules.evaluation.{max u (t + 1)}
    (completedIntegralCoefficientSheafUnrestricted l E Y) U) _ ≫
      (ModuleCat.piIsoPi _).hom ≫ ModuleCat.ofHom (LinearMap.proj i)) x) = _
  rw [ModuleCat.piIsoPi_hom_ker_subtype, piComparison_comp_π]
  rfl

/-- On a connected scheme, the canonical constant-value maps are ring equivalences,
compatible with all residues and coefficient inclusion. Every prescribed integral basis
induces the displayed sheaf isomorphism, with exactly its residue columns and the same
basis on global sections.

Source: Bhatt--Scholze 4.2.12, 6.8.1 and 6.8.2(1), printed pp. 30 and 58--59
(blueprint: lem-pur-connected-adic-integral-basis).

Proof: (1) Realize each constant quotient sheaf as continuous functions into the
quotient with its discrete topology. The comparison is locally bijective: sections
are constant on their open fibers, and equality is detected on nonempty objects.
On connected X every such function is constant, and nonemptiness gives a unique value.
The construction allows the independent coefficient and scheme universes of this statement.
(2) Evaluate the inverse limit sectionwise. Apply adic completeness of the rank-one
integer module to reconstruct each section from its compatible residues. Hausdorffness
gives uniqueness. This proves that the canonical constant maps are ring equivalences.
(3) The actual coefficient map is characterized by its quotient projections. Naturality
of sheafification sends constant residues to their actual included residues; joint
injectivity of the inverse-limit projections gives coefficient compatibility.
(4) Construct the prescribed-basis morphism as the sum of its coordinate columns,
using the unit-module hom/section equivalence. Its map on global sections is the
original integral basis map conjugated by the ring equivalences from (2), hence bijective.
The existing finite-free completed scalar comparison identifies the target with a finite
product of unit modules. Global sections are homomorphisms from the unit, since X is terminal.
Finite products are finite coproducts, so the global bijection induces a bijection on
homomorphisms from the free source. Lift the inverse of the known trivialization and
use injectivity to obtain both inverse identities. The resulting isomorphism has exactly
the constructed columns and the asserted global-section formula, including rank zero.
-/
theorem connected_adic_integral_basis
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{t}) [ConnectedSpace X] :
    ∃ (eE : Padic.coefficientExtensionIntegers l E ≃+*
        (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
          (op (Scheme.ProEt.mk (𝟙 X))))
      (eL : Padic.coefficientExtensionIntegers l L ≃+*
        (completedIntegralCoefficientSheafUnrestricted l L X).obj.obj
          (op (Scheme.ProEt.mk (𝟙 X)))),
      (∀ a, eE a = integralScalarConstant l E X (op (Scheme.ProEt.mk (𝟙 X))) a) ∧
      (∀ a, eL a = integralScalarConstant l L X (op (Scheme.ProEt.mk (𝟙 X))) a) ∧
      (∀ n a, (completedIntegralCommRingProjectionUnrestricted l E X n).hom.app
        (op (Scheme.ProEt.mk (𝟙 X))) (eE a) =
          integralScalarFiniteConstant l E X n (op (Scheme.ProEt.mk (𝟙 X))) a) ∧
      (∀ n a, (completedIntegralCommRingProjectionUnrestricted l L X n).hom.app
        (op (Scheme.ProEt.mk (𝟙 X))) (eL a) =
          integralScalarFiniteConstant l L X n (op (Scheme.ProEt.mk (𝟙 X))) a) ∧
      (∀ a, (completedIntegralScalarCoefficientMap l E L ι X).hom.app
        (op (Scheme.ProEt.mk (𝟙 X))) (eE a) =
          eL (integralScalarIntegerInclusion l E L ι a)) ∧
      ∀ β : Fin (completedScalarRelativeDegree l E L ι) →
          Padic.coefficientExtensionIntegers l L,
        Function.Bijective
          (fun a : Fin (completedScalarRelativeDegree l E L ι) →
              Padic.coefficientExtensionIntegers l E ↦
            ∑ i, integralScalarIntegerInclusion l E L ι (a i) * β i) →
        ∃ Φ : (∏ᶜ (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
            SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X))) ≅
          (SheafOfModules.restrictScalars.{max u (t + 1)}
            (connectedAdicScalarRingMap l E L ι X)).obj
              (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l L X)),
          (∀ U x, Φ.hom.val.app U x = ∑ i,
            (connectedAdicScalarRingMap l E L ι X).hom.app U
              ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
                SheafOfModules.unit
                  (completedIntegralCoefficientSheafUnrestricted l E X)) i).val.app U x) *
              integralScalarConstant l L X U (β i)) ∧
          (∀ (U : X.ProEtᵒᵖ) (n : ℕ) (i : Fin (completedScalarRelativeDegree l E L ι)),
            (completedIntegralCommRingProjectionUnrestricted l L X n).hom.app U
              (integralScalarConstant l L X U (β i)) =
                integralScalarFiniteConstant l L X n U (β i)) ∧
          (∀ x, Φ.hom.val.app (op (Scheme.ProEt.mk (𝟙 X))) x =
            eL (∑ i, integralScalarIntegerInclusion l E L ι
              (eE.symm ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
                SheafOfModules.unit
                  (completedIntegralCoefficientSheafUnrestricted l E X)) i).val.app
                    (op (Scheme.ProEt.mk (𝟙 X))) x)) * β i)) := by
  classical
  let U₀ := op (Scheme.ProEt.mk (𝟙 X))
  let eE := RingEquiv.ofBijective (scalarValue l E X U₀) (scalarValue_bijective l E X)
  let eL := RingEquiv.ofBijective (scalarValue l L X U₀) (scalarValue_bijective l L X)
  refine ⟨eE, eL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact scalarValue_eq l E X U₀
  · exact scalarValue_eq l L X U₀
  · intro n a
    exact scalarValue_projection l E X U₀ a n
  · intro n a
    exact scalarValue_projection l L X U₀ a n
  · exact scalarValue_map l E X L ι U₀
  · intro β hβ
    let d := completedScalarRelativeDegree l E L ι
    let R := completedIntegralCoefficientSheafUnrestricted l E X
    let N := (SheafOfModules.restrictScalars.{max u (t + 1)}
      (connectedAdicScalarRingMap l E L ι X)).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l L X))
    let F : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit R) ⟶ N :=
      scalarForward l E X L ι d β
    have hform (x : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit R).val.obj U₀) :
        F.val.app U₀ x = eL (∑ i,
          integralScalarIntegerInclusion l E L ι
            (eE.symm ((Pi.π (fun _ : Fin d ↦ SheafOfModules.unit R) i).val.app U₀ x)) *
              β i) := by
      rw [scalarForward_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul]
      congr 1
      have h := scalarValue_map l E X L ι U₀
        (eE.symm ((Pi.π (fun _ : Fin d ↦ SheafOfModules.unit R) i).val.app U₀ x))
      change (connectedAdicScalarRingMap l E L ι X).hom.app U₀
        (eE (eE.symm _)) = eL _ at h
      rw [eE.apply_symm_apply] at h
      exact h
    have hb : Function.Bijective (F.val.app U₀) := by
      let c := (freeCoordinates l E X d U₀).trans
        (Equiv.piCongrRight fun _ : Fin d ↦ eE.symm.toEquiv)
      have hcomp := eL.bijective.comp (hβ.comp c.bijective)
      have heq : (fun x ↦ F.val.app U₀ x) =
          (fun x ↦ eL (∑ i, integralScalarIntegerInclusion l E L ι (c x i) * β i)) := by
        funext x
        exact (hform x).trans (congrArg eL (by
          apply Finset.sum_congr rfl
          intro i _
          change integralScalarIntegerInclusion l E L ι
              (eE.symm ((Pi.π (fun _ : Fin d ↦ SheafOfModules.unit R) i).val.app U₀ x)) *
                β i = integralScalarIntegerInclusion l E L ι
                  (eE.symm (freeCoordinates l E X d U₀ x i)) * β i
          exact congrArg (fun z ↦ integralScalarIntegerInclusion l E L ι
            (eE.symm z) * β i) (freeCoordinates_apply l E X d U₀ x i).symm))
      constructor
      · intro x y h
        apply hcomp.injective
        exact (congrFun heq x).symm.trans (h.trans (congrFun heq y))
      · intro y
        obtain ⟨x, hx⟩ := hcomp.surjective y
        exact ⟨x, (congrFun heq x).trans hx⟩
    let : HasFiniteBiproducts (SheafOfModules.{max u (t + 1)} R) :=
      Abelian.hasFiniteBiproducts
    obtain ⟨ψ⟩ := (finiteFreeCompletedScalarComparison l E L ι X).1
    let ψ' : N ≅ ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit R := ψ
    let : IsIso F := free_iso_of_global_bijective R (Scheme.ProEt.mk (𝟙 X))
      (Scheme.ProEt.isTerminalMkId X) d N ψ' F hb
    refine ⟨asIso F, ?_, ?_, ?_⟩
    · intro U x
      change (scalarForward l E X L ι d β).val.app U x = _
      exact (scalarForward_apply l E X L ι d β U x).trans (by
        apply Finset.sum_congr rfl
        intro i _
        rw [scalarValue_eq])
    · intro U n i
      exact (integralScalarConstant_existsUnique l L X U (β i)).exists.choose_spec n
    · exact hform

end WeilConjectures
