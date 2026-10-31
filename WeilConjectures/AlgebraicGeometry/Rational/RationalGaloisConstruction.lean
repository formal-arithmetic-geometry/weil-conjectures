/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralGaloisConstruction
import all WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
import WeilConjectures.RepresentationTheory.PoincareDuality.LocalizedActionContinuity
import WeilConjectures.RepresentationTheory.PoincareDuality.LocalizedIntertwining
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Finite
import WeilConjectures.NumberTheory.Padics.ProfiniteStableLattice
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Rational reconstruction from integral Galois modules

Source: Weil II (1.1.1), (1.1.6); Stanford Weil II seminar L19, Proposition 1.1.9.
(blueprint: new-e7-rational-galois-construction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] lisseRationalFiberFunctor

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- Rationalization over one coefficient field, relative to a normalized integral stage.
Source: Weil II (1.1.1) c), (1.1.6); Stanford L19, Proposition 1.1.9, second bullet.
(blueprint: new-e7-rational-galois-construction). -/
structure RationalGaloisConstruction
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (i : IntegralGaloisConstruction y G c P δ l E) where
  eR : LisseRationalSheaf l E Y ≌ galoisCoefficientRepresentations l E P δ
  τR : eR.functor ⋙ ObjectProperty.ι _ ⋙
    forget₂ (Rep.{u + 1} E G) (ModuleCat.{u + 1} E) ≅
    lisseRationalFiberFunctor l E Y y
  /-- Rationalization of each integral model, normalized on every pure tensor. -/
  localization :
    ∀ (F : LisseRationalSheaf l E Y),
      ∃ η : (TensorProduct (Padic.coefficientExtensionIntegers l E) E
          (i.eI.functor.obj F.integral).obj.V) ≃ₗ[E]
            (eR.functor.obj F).obj.V,
        (∀ (g : G) (a : E) (z : (i.eI.functor.obj F.integral).obj.V),
          η (TensorProduct.tmul _ a ((i.eI.functor.obj F.integral).obj.ρ g z)) =
            (eR.functor.obj F).obj.ρ g (η (TensorProduct.tmul _ a z))) ∧
        ∀ (a : E) (z : (i.eI.functor.obj F.integral).obj.V),
          eqToHom (lisseRationalFiberFunctor_obj l E Y y F)
            (τR.hom.app F (η (TensorProduct.tmul _ a z))) =
              TensorProduct.tmul _ a (i.τI.hom.app F.integral z)

variable {Y : Scheme.{u}} [ConnectedSpace Y]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
  [IsFundamentalGroup (FiniteEtale.fiber y) G]
  (c : GaloisLisseFiniteCorrespondence y G)
  (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
  (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (i : IntegralGaloisConstruction y G c P δ l E)

private instance fiber_additive : (lisseIntegralFiberFunctor l E Y y).Additive where
  map_add := integralFiber_map_add l E Y y _ _

private instance fiber_linear :
    (lisseIntegralFiberFunctor l E Y y).Linear (Padic.coefficientExtensionIntegers l E) where
  map_smul f r := integralFiber_map_smul l E Y y r f

private noncomputable def integralRepFunctor :
    LisseIntegralSheaf l E Y ⥤ Rep.{u + 1} (Padic.coefficientExtensionIntegers l E) G :=
  i.eI.functor ⋙ ObjectProperty.ι _

private instance integralRepFunctor_additive :
    (integralRepFunctor y G c P δ l E i).Additive := by
  let T := integralRepFunctor y G c P δ l E i
  let U := forget₂ (Rep.{u + 1} (Padic.coefficientExtensionIntegers l E) G)
    (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
  let : (T ⋙ U).Additive := Functor.additive_of_iso i.τI.symm
  exact Functor.additive_of_comp_faithful T U

private instance integralRepFunctor_linear :
    (integralRepFunctor y G c P δ l E i).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  let R := Padic.coefficientExtensionIntegers l E
  let T := integralRepFunctor y G c P δ l E i
  let U := forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R)
  let : (T ⋙ U).Linear R := Functor.linear_of_iso R i.τI.symm
  refine ⟨fun f r ↦ U.map_injective ?_⟩
  change (T ⋙ U).map (r • f) = U.map (r • T.map f)
  rw [Functor.map_smul, Functor.map_smul]
  rfl

private noncomputable def rationalRepObject (F : LisseRationalSheaf l E Y) :
    Rep.{u + 1} E G :=
  Rep.of (((Module.End.baseChangeHom (Padic.coefficientExtensionIntegers l E) E
    (i.eI.functor.obj F.integral).obj.V).toMonoidHom).comp
      (i.eI.functor.obj F.integral).obj.ρ)

private noncomputable def rationalRepMapLinear (F H : LisseRationalSheaf l E Y) :
    lisseRationalHom l E Y F H →ₗ[E]
      ((rationalRepObject y G c P δ l E i F).V →ₗ[E]
        (rationalRepObject y G c P δ l E i H).V) :=
  let R := Padic.coefficientExtensionIntegers l E
  let T := integralRepFunctor y G c P δ l E i
  let m : (F.integral ⟶ H.integral) →ₗ[R]
      ((T.obj F.integral).V →ₗ[R] (T.obj H.integral).V) :=
    (Representation.IntertwiningMap.toLinearMapl _ _).comp
      ((Rep.homLinearEquiv _ _).toLinearMap.comp (T.mapLinearMap R))
  TensorProduct.AlgebraTensorModule.lift
    { toFun a := a • ((LinearMap.baseChangeHom R E _ _).comp m)
      map_add' a b := by ext; simp [add_smul]
      map_smul' a b := by ext; simp [mul_smul] }

private theorem rationalRepMapLinear_tmul (F H : LisseRationalSheaf l E Y)
    (a : E) (f : F.integral ⟶ H.integral) :
    rationalRepMapLinear y G c P δ l E i F H (a ⊗ₜ f) =
      a • LinearMap.baseChange E
        ((integralRepFunctor y G c P δ l E i).map f).hom.toLinearMap := rfl

set_option maxHeartbeats 1000000 in
-- Tensor induction compares the scalar-extended action and rationalized Hom map.
private theorem rationalRepMapLinear_comm (F H : LisseRationalSheaf l E Y)
    (h : F ⟶ H) (g : G) (z : (rationalRepObject y G c P δ l E i F).V) :
    rationalRepMapLinear y G c P δ l E i F H h
        ((rationalRepObject y G c P δ l E i F).ρ g z) =
      (rationalRepObject y G c P δ l E i H).ρ g
        (rationalRepMapLinear y G c P δ l E i F H h z) := by
  induction h using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
      rw [rationalRepMapLinear_tmul]
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul b x =>
          change (a • LinearMap.baseChange E
            ((integralRepFunctor y G c P δ l E i).map f).hom.toLinearMap)
              (b ⊗ₜ (i.eI.functor.obj F.integral).obj.ρ g x) =
            LinearMap.baseChange E ((i.eI.functor.obj H.integral).obj.ρ g)
              ((a • LinearMap.baseChange E
                ((integralRepFunctor y G c P δ l E i).map f).hom.toLinearMap) (b ⊗ₜ x))
          simp only [LinearMap.smul_apply, LinearMap.baseChange_tmul, map_smul]
          exact congrArg
            (fun z : (i.eI.functor.obj H.integral).obj.V ↦ a • TensorProduct.tmul _ b z)
            (Rep.hom_comm_apply (i.eI.functor.map f).hom g x)
      | add x y hx hy => simp only [map_add, hx, hy]
  | add h k hh hk =>
      simp only [map_add, LinearMap.add_apply, hh, hk]


private theorem rationalRepMapLinear_id (F : LisseRationalSheaf l E Y) :
    rationalRepMapLinear y G c P δ l E i F F (1 ⊗ₜ (𝟙 F.integral)) =
      LinearMap.id := by
  rw [rationalRepMapLinear_tmul]
  rw [(integralRepFunctor y G c P δ l E i).map_id]
  simp

private theorem rationalRepMapLinear_comp (F H K : LisseRationalSheaf l E Y)
    (f : F ⟶ H) (g : H ⟶ K) :
    rationalRepMapLinear y G c P δ l E i F K (f ≫ g) =
      (rationalRepMapLinear y G c P δ l E i H K g).comp
        (rationalRepMapLinear y G c P δ l E i F H f) := by
  change rationalRepMapLinear y G c P δ l E i F K
    ((lisseRationalComposition l E Y).comp F H K f g) = _
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul b g =>
      rw [(lisseRationalComposition l E Y).comp_tmul, rationalRepMapLinear_tmul,
        rationalRepMapLinear_tmul, rationalRepMapLinear_tmul, Functor.map_comp]
      change (a * b) • LinearMap.baseChange E
        ((((integralRepFunctor y G c P δ l E i).map g).hom.toLinearMap).comp
          (((integralRepFunctor y G c P δ l E i).map f).hom.toLinearMap)) = _
      rw [LinearMap.baseChange_comp, LinearMap.smul_comp, LinearMap.comp_smul,
        smul_smul, mul_comm a b]
    | add g h hg hh => simp [hg, hh, LinearMap.add_comp]
  | add f g hf hg => simp [hf, hg, LinearMap.comp_add]

private noncomputable def rationalRepFunctor :
    LisseRationalSheaf l E Y ⥤ Rep.{u + 1} E G where
  obj F := rationalRepObject y G c P δ l E i F
  map {F H} h := Rep.ofHom
    { toLinearMap := rationalRepMapLinear y G c P δ l E i F H h
      isIntertwining' g := LinearMap.ext
        (rationalRepMapLinear_comm y G c P δ l E i F H h g) }
  map_id F := by
    apply Rep.Hom.ext
    apply Representation.IntertwiningMap.ext
    exact rationalRepMapLinear_id y G c P δ l E i F
  map_comp {F H K} f g := by
    apply Rep.Hom.ext
    apply Representation.IntertwiningMap.ext
    exact rationalRepMapLinear_comp y G c P δ l E i F H K f g


open Padic in
private theorem rational_coefficientAdicTopology (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    (coefficientExtensionMaximalIdeal l E).adicTopology =
      TopologicalSpace.induced (fun x : coefficientExtensionIntegers l E ↦ (x : E))
        inferInstance := by
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let O := coefficientExtensionIntegers l E
  let I := coefficientExtensionMaximalIdeal l E
  have hdvr := (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span ({coefficientExtensionUniformizer l E} : Set O) = I :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hideal (n : ℕ) : coefficientExtensionIdeal l E n = I ^ n := by
    change Ideal.span ({coefficientExtensionUniformizer l E} : Set O) ^ n = I ^ n
    rw [hgen]
  apply TopologicalSpace.ext_nhds
  intro x
  apply (I.hasBasis_nhds_adic x).ext (coefficientExtension_integers_coset_basis l E x)
  · intro n _
    refine ⟨n, trivial, ?_⟩
    intro y hy
    have hmem : y - x ∈ I ^ (n + 1) := by
      simpa only [Set.mem_ofPred_eq, Ideal.Quotient.eq, hideal] using hy
    exact ⟨y - x, Ideal.pow_le_pow_right (Nat.le_succ n) hmem, by simp⟩
  · intro n _
    refine ⟨n + 1, trivial, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    change Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1)) (x + z) = _
    rw [Ideal.Quotient.eq, hideal, add_sub_cancel_left]
    exact hz


set_option maxHeartbeats 1000000 in
-- Resolve the coefficient and representation topology instances once for localization.
private theorem rationalRepObject_continuous (F : LisseRationalSheaf l E Y) :
    Representation.IsContinuousCoefficient l E P (rationalRepObject y G c P δ l E i F).V
      ((galoisRepLinearAction E (rationalRepObject y G c P δ l E i F)).comp
        δ.symm.toMonoidHom) := by
  let O := Padic.coefficientExtensionIntegers l E
  let I := Padic.coefficientExtensionMaximalIdeal l E
  let W := (i.eI.functor.obj F.integral).obj
  obtain ⟨hfinite, hcontinuous⟩ := (i.eI.functor.obj F.integral).property
  let : Module.Finite O W.V := hfinite
  have hdvr := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  let : IsFractionRing O E := hdvr.2.2.2.2.2.2.1
  have hfin : FiniteDimensional E (rationalRepObject y G c P δ l E i F).V := by
    change Module.Finite E (TensorProduct O E W.V)
    infer_instance
  refine ⟨hfin, ?_⟩
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : TopologicalSpace (TensorProduct O E W.V) := moduleTopology E (TensorProduct O E W.V)
  have hOE : @Continuous O E I.adicTopology _ (algebraMap O E) := by
    rw [rational_coefficientAdicTopology l E]
    exact continuous_induced_dom
  apply Representation.localized_action_continuous I (nonZeroDivisors O)
    (TensorProduct.mk O E W.V 1)
    (W.ρ.comp δ.symm.toMonoidHom)
    ((rationalRepObject y G c P δ l E i F).ρ.comp δ.symm.toMonoidHom)
  · intro a x
    rfl
  · intro s hz
    apply nonZeroDivisors.ne_zero s.property
    apply IsFractionRing.injective O E
    simpa only [map_zero] using hz
  · exact hOE
  · exact hcontinuous

set_option maxHeartbeats 1000000 in
-- The localization extensionality proof elaborates several scalar restrictions.
private theorem rationalRepMapLinear_injective (F H : LisseRationalSheaf l E Y) :
    Function.Injective (rationalRepMapLinear y G c P δ l E i F H) := by
  let R := Padic.coefficientExtensionIntegers l E
  let S := nonZeroDivisors R
  let T := integralRepFunctor y G c P δ l E i
  let M := (T.obj F.integral).V
  let N := (T.obj H.integral).V
  have hdvr := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  let : IsFractionRing R E := hdvr.2.2.2.2.2.2.1
  let : IsDiscreteValuationRing R := hdvr.2.2.2.2.2.2.2.1
  let : Module.Finite R M := (i.eI.functor.obj F.integral).property.1
  let : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  let m : (F.integral ⟶ H.integral) →ₗ[R] (M →ₗ[R] N) :=
    (Representation.IntertwiningMap.toLinearMapl _ _).comp
      ((Rep.homLinearEquiv _ _).toLinearMap.comp (T.mapLinearMap R))
  let U := forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R)
  let : T.Faithful := inferInstanceAs (i.eI.functor ⋙ ObjectProperty.ι _).Faithful
  have hm : Function.Injective m := by
    intro f g h
    apply (T ⋙ U).map_injective
    apply ModuleCat.hom_ext
    exact h
  let f₀ := TensorProduct.mk R E M 1
  let g₀ := TensorProduct.mk R E N 1
  let k := TensorProduct.mk R E (F.integral ⟶ H.integral) 1
  let θ := IsLocalizedModule.mapExtendScalars S f₀ g₀ E
  have he : (rationalRepMapLinear y G c P δ l E i F H).restrictScalars R =
      IsLocalizedModule.map S k θ m := by
    apply IsLocalizedModule.linearMap_ext S k θ
    apply LinearMap.ext
    intro f
    rw [LinearMap.comp_apply, LinearMap.comp_apply, IsLocalizedModule.map_apply]
    change rationalRepMapLinear y G c P δ l E i F H (1 ⊗ₜ[R] f) = θ (m f)
    rw [rationalRepMapLinear_tmul, one_smul]
    change LinearMap.baseChange E (m f) = θ (m f)
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.linearMap_ext S f₀ g₀
    apply LinearMap.ext
    intro x
    change 1 ⊗ₜ[R] (m f) x = IsLocalizedModule.map S f₀ g₀ (m f) (f₀ x)
    exact (IsLocalizedModule.map_apply S f₀ g₀ (m f) x).symm
  change Function.Injective
    ((rationalRepMapLinear y G c P δ l E i F H).restrictScalars R)
  rw [he]
  exact IsLocalizedModule.map_injective S k θ m hm


private theorem fractionTensor_exists_pure
    {R K N : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup N] [Module R N] (x : TensorProduct R K N) :
    ∃ (a : K) (n : N), a ⊗ₜ[R] n = x := by
  let S := nonZeroDivisors R
  let f := TensorProduct.mk R K N 1
  obtain ⟨⟨n, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  have hs : algebraMap R K s ≠ 0 := by
    intro h
    apply nonZeroDivisors.ne_zero s.property
    apply IsFractionRing.injective R K
    simpa only [map_zero] using h
  have h : IsLocalizedModule.mk' f n s = (algebraMap R K s)⁻¹ • f n := by
    apply (eq_inv_smul_iff₀ hs).mpr
    rw [algebraMap_smul]
    exact IsLocalizedModule.mk'_cancel' f n s
  refine ⟨(algebraMap R K s)⁻¹, n, ?_⟩
  simpa [f, TensorProduct.smul_tmul'] using h.symm


private noncomputable def rationalRepFiberIso (F : LisseRationalSheaf l E Y) :
    (forget₂ (Rep.{u + 1} E G) (ModuleCat.{u + 1} E)).obj
        ((rationalRepFunctor y G c P δ l E i).obj F) ≅
      (lisseRationalFiberFunctor l E Y y).obj F :=
  (LinearEquiv.baseChange (Padic.coefficientExtensionIntegers l E) E _ _
      (i.τI.app F.integral).toLinearEquiv).toModuleIso ≪≫
    (eqToIso (lisseRationalFiberFunctor_obj l E Y y F)).symm

private theorem rationalRepFiberIso_comp (F : LisseRationalSheaf l E Y) :
    (rationalRepFiberIso y G c P δ l E i F).hom ≫
        eqToHom (lisseRationalFiberFunctor_obj l E Y y F) =
      (LinearEquiv.baseChange (Padic.coefficientExtensionIntegers l E) E _ _
      (i.τI.app F.integral).toLinearEquiv).toModuleIso.hom := by
  simp [rationalRepFiberIso]

private theorem rationalRepFiberIso_tmul (F : LisseRationalSheaf l E Y)
    (a : E) (z : (i.eI.functor.obj F.integral).obj.V) :
    eqToHom (lisseRationalFiberFunctor_obj l E Y y F)
      ((rationalRepFiberIso y G c P δ l E i F).hom (a ⊗ₜ z)) =
        a ⊗ₜ (i.τI.hom.app F.integral z) := by
  rw [← ConcreteCategory.comp_apply, rationalRepFiberIso_comp]
  exact LinearEquiv.baseChange_tmul (Padic.coefficientExtensionIntegers l E) E _ _ a z

set_option maxHeartbeats 1000000 in
-- Transport the fixed rational fibre map through both tensor comparisons.
private theorem rationalRepFiberIso_naturality {F H : LisseRationalSheaf l E Y}
    (h : F ⟶ H) :
    (forget₂ (Rep.{u + 1} E G) (ModuleCat.{u + 1} E)).map
        ((rationalRepFunctor y G c P δ l E i).map h) ≫
          (rationalRepFiberIso y G c P δ l E i H).hom =
      (rationalRepFiberIso y G c P δ l E i F).hom ≫
        (lisseRationalFiberFunctor l E Y y).map h := by
  let R := Padic.coefficientExtensionIntegers l E
  have hdvr := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  let : IsFractionRing R E := hdvr.2.2.2.2.2.2.1
  obtain ⟨a, f, rfl⟩ := fractionTensor_exists_pure (R := R) (K := E) h
  apply (cancel_mono (eqToHom (lisseRationalFiberFunctor_obj l E Y y H))).mp
  rw [Category.assoc, rationalRepFiberIso_comp]
  rw [lisseRationalFiberFunctor_map_spec l E Y y F H a f]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [← Category.assoc, rationalRepFiberIso_comp]
  apply ModuleCat.hom_ext
  change
    ((LinearEquiv.baseChange (Padic.coefficientExtensionIntegers l E) E _ _
      (i.τI.app H.integral).toLinearEquiv).toLinearMap).comp
        (a • LinearMap.baseChange E
          ((integralRepFunctor y G c P δ l E i).map f).hom.toLinearMap) =
      (a • LinearMap.baseChange E ((lisseIntegralFiberFunctor l E Y y).map f).hom).comp
        ((LinearEquiv.baseChange (Padic.coefficientExtensionIntegers l E) E _ _
      (i.τI.app F.integral).toLinearEquiv).toLinearMap)
  have hn : ((i.τI.hom.app H.integral).hom).comp
      ((integralRepFunctor y G c P δ l E i).map f).hom.toLinearMap =
      (((lisseIntegralFiberFunctor l E Y y).map f).hom).comp
        ((i.τI.hom.app F.integral).hom) :=
    congrArg ModuleCat.Hom.hom (i.τI.hom.naturality f)
  change (LinearMap.baseChange E (i.τI.hom.app H.integral).hom).comp
      (a • LinearMap.baseChange E
        ((integralRepFunctor y G c P δ l E i).map f).hom.toLinearMap) =
    (a • LinearMap.baseChange E ((lisseIntegralFiberFunctor l E Y y).map f).hom).comp
      (LinearMap.baseChange E (i.τI.hom.app F.integral).hom)
  rw [LinearMap.comp_smul, ← LinearMap.baseChange_comp, hn,
    LinearMap.baseChange_comp, LinearMap.smul_comp]

private noncomputable def rationalRepFiberComparison :
    rationalRepFunctor y G c P δ l E i ⋙
        forget₂ (Rep.{u + 1} E G) (ModuleCat.{u + 1} E) ≅
      lisseRationalFiberFunctor l E Y y :=
  NatIso.ofComponents (rationalRepFiberIso y G c P δ l E i)
    (fun h ↦ rationalRepFiberIso_naturality y G c P δ l E i h)

private def restrictScalarRep
    {R A J V : Type*} [CommRing R] [CommRing A] [Algebra R A] [Monoid J]
    [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]
    (σ : Representation A J V) : Representation R J V where
  toFun a := (σ a).restrictScalars R
  map_one' := by ext x; exact congrArg (fun k : Module.End A V ↦ k x) σ.map_one
  map_mul' a b := by
    ext x
    exact congrArg (fun k : Module.End A V ↦ k x) (σ.map_mul a b)

set_option maxHeartbeats 2000000 in
-- Clear denominators uniformly, then compare maps after localization.
private theorem rationalRepFunctor_full :
    (rationalRepFunctor y G c P δ l E i).Full := by
  classical
  let R := Padic.coefficientExtensionIntegers l E
  let S := nonZeroDivisors R
  let T := integralRepFunctor y G c P δ l E i
  have hdvr := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  let : IsFractionRing R E := hdvr.2.2.2.2.2.2.1
  let : IsDiscreteValuationRing R := hdvr.2.2.2.2.2.2.2.1
  let : T.Full := inferInstanceAs (i.eI.functor ⋙ ObjectProperty.ι _).Full
  refine ⟨fun {F H} ψ ↦ ?_⟩
  let M := (T.obj F.integral).V
  let N := (T.obj H.integral).V
  let : Module.Finite R M := (i.eI.functor.obj F.integral).property.1
  let : Module.Finite R N := (i.eI.functor.obj H.integral).property.1
  let : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  let f₀ := TensorProduct.mk R E M 1
  let g₀ := TensorProduct.mk R E N 1
  let ρF := restrictScalarRep (R := R)
    ((rationalRepFunctor y G c P δ l E i).obj F).ρ
  let ρH := restrictScalarRep (R := R)
    ((rationalRepFunctor y G c P δ l E i).obj H).ρ
  let ψR : ρF.IntertwiningMap ρH :=
    { toLinearMap := ψ.hom.toLinearMap.restrictScalars R
      isIntertwining' a := by
        apply LinearMap.ext
        intro x
        exact Rep.hom_comm_apply ψ a x }
  obtain ⟨s, φ, hφ⟩ := Representation.exists_localized_intertwining_lift S f₀ g₀
    (T.obj F.integral).ρ (T.obj H.integral).ρ ρF ρH
    (by intro a x; rfl) (by intro a x; rfl) ψR
  let f := T.preimage (Rep.ofHom φ)
  have hf : T.map f = Rep.ofHom φ := T.map_preimage (Rep.ofHom φ)
  let a := (algebraMap R E s)⁻¹
  refine ⟨a ⊗ₜ[R] f, ?_⟩
  apply Rep.Hom.ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext S f₀ g₀
  apply LinearMap.ext
  intro x
  change rationalRepMapLinear y G c P δ l E i F H (a ⊗ₜ[R] f) (1 ⊗ₜ[R] x) =
    ψ.hom.toLinearMap (1 ⊗ₜ[R] x)
  rw [rationalRepMapLinear_tmul]
  change a • (LinearMap.baseChange E (T.map f).hom.toLinearMap)
    (1 ⊗ₜ[R] x) = ψ.hom.toLinearMap (1 ⊗ₜ[R] x)
  rw [LinearMap.baseChange_tmul, hf]
  change a • (1 ⊗ₜ[R] φ x) = ψ (1 ⊗ₜ[R] x)
  have hφx : 1 ⊗ₜ[R] φ x = (s : R) • ψ (1 ⊗ₜ[R] x) :=
    LinearMap.congr_fun hφ x
  rw [hφx, ← algebraMap_smul E (s : R), smul_smul]
  have hs : algebraMap R E s ≠ 0 := by
    intro hz
    apply nonZeroDivisors.ne_zero s.property
    apply IsFractionRing.injective R E
    simpa only [map_zero] using hz
  simp [a, hs]
private noncomputable def latticeTensorMap
    {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (Λ : Submodule R V) : TensorProduct R K Λ →ₗ[K] V :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun a := a • Λ.subtype
      map_add' a b := by ext; simp [add_smul]
      map_smul' a b := by ext; simp [mul_smul] }

private noncomputable def latticeTensorEquiv
    {R K V : Type*} [CommRing R] [StrongRankCondition R] [Field K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [FiniteDimensional K V]
    (Λ : Submodule R V) [Module.Free R Λ] [Module.Finite R Λ]
    (hspan : Submodule.span K (Λ : Set V) = ⊤)
    (hrank : Module.finrank R Λ = Module.finrank K V) :
    TensorProduct R K Λ ≃ₗ[K] V := by
  let μ := latticeTensorMap (K := K) Λ
  have hr : Submodule.span K (Λ : Set V) ≤ μ.range := by
    apply Submodule.span_le.mpr
    intro x hx
    exact ⟨1 ⊗ₜ[R] (⟨x, hx⟩ : Λ), by simp [μ, latticeTensorMap]⟩
  have hsurj : Function.Surjective μ := LinearMap.range_eq_top.mp (top_unique (hspan ▸ hr))
  have hdim : Module.finrank K (TensorProduct R K Λ) = Module.finrank K V :=
    (Module.finrank_baseChange (R := K) (S := R) (M' := Λ)).trans hrank
  exact LinearEquiv.ofBijective μ
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

private noncomputable def rationalContinuousFunctor :
    LisseRationalSheaf l E Y ⥤ galoisCoefficientRepresentations l E P δ :=
  ObjectProperty.lift _ (rationalRepFunctor y G c P δ l E i)
    (rationalRepObject_continuous y G c P δ l E i)

set_option maxHeartbeats 3000000 in
-- Transport a stable lattice through the integral equivalence and base change.
private theorem rationalContinuousFunctor_essSurj :
    (rationalContinuousFunctor y G c P δ l E i).EssSurj := by
  classical
  let R := Padic.coefficientExtensionIntegers l E
  let I := Padic.coefficientExtensionMaximalIdeal l E
  refine ⟨fun X ↦ ?_⟩
  obtain ⟨hfd, hcontinuous⟩ := X.property
  let : FiniteDimensional E X.obj.V := hfd
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : TopologicalSpace X.obj.V := moduleTopology E X.obj.V
  let : Module R X.obj.V := Module.compHom X.obj.V R.subtype
  let ρ := (galoisRepLinearAction E X.obj).comp δ.symm.toMonoidHom
  obtain ⟨Λ, hfg, hspan, hfree, hrank, hstable, htop, hact⟩ :=
    Padic.exists_stable_lattice l E P X.obj.V ρ hcontinuous
  let : Module.Finite R Λ := Module.Finite.of_fg hfg
  let : Module.Free R Λ := hfree
  let A : Rep.{u + 1} R G := Rep.of (restrictScalarRep (R := R) X.obj.ρ)
  have hstableG (g : G) : Λ ≤ Λ.comap (A.ρ g) := by
    intro z hz
    have hm : ρ (δ g) z ∈ Λ := by
      change ρ (δ g) z ∈ (Λ : Set X.obj.V)
      rw [← hstable (δ g)]
      exact Set.mem_image_of_mem _ hz
    have he : ρ (δ g) z = X.obj.ρ g z := by
      change X.obj.ρ (δ.symm (δ g)) z = _
      rw [δ.symm_apply_apply]
    rwa [he] at hm
  let Lrep := A.subrepresentation Λ hstableG
  let : TopologicalSpace Λ := I.adicModuleTopology Λ
  obtain ⟨act, hactc, hacteval⟩ := hact
  have hL : Representation.IsContinuousIntegral l E P Lrep.V
      ((galoisRepLinearAction R Lrep).comp δ.symm.toMonoidHom) := by
    refine ⟨inferInstance, ?_⟩
    have he : (fun p : P × Λ ↦
        (galoisRepLinearAction R Lrep) (δ.symm p.1) p.2) = act := by
      funext p
      apply Subtype.ext
      exact (hacteval p).symm
    exact he.symm ▸ hactc
  let L : galoisIntegralRepresentations l E P δ := ⟨Lrep, hL⟩
  let F : LisseRationalSheaf l E Y := ⟨i.eI.inverse.obj L⟩
  let β : (i.eI.functor.obj F.integral).obj ≅ Lrep :=
    (ObjectProperty.ι _).mapIso (i.eI.counitIso.app L)
  let b : (i.eI.functor.obj F.integral).obj.V ≃ₗ[R] Λ :=
    ((forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R)).mapIso β).toLinearEquiv
  let η := (LinearEquiv.baseChange R E _ _ b).trans (latticeTensorEquiv Λ hspan hrank)
  let e : ((rationalRepFunctor y G c P δ l E i).obj F).ρ.Equiv X.obj.ρ :=
    { __ := η
      isIntertwining' g := by
        apply LinearMap.ext
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a z =>
          change η (a ⊗ₜ[R] ((i.eI.functor.obj F.integral).obj.ρ g z)) =
            X.obj.ρ g (η (a ⊗ₜ[R] z))
          change a • (b ((i.eI.functor.obj F.integral).obj.ρ g z) : X.obj.V) =
            X.obj.ρ g (a • (b z : X.obj.V))
          rw [map_smul]
          exact congrArg (fun x : Λ ↦ a • (x : X.obj.V)) (Rep.hom_comm_apply β.hom g z)
        | add x y hx hy => simp only [map_add, hx, hy] }
  exact ⟨F, ⟨ObjectProperty.isoMk _ (Rep.mkIso e)⟩⟩

set_option maxHeartbeats 2000000 in
-- Elaborate the rational Hom injection through the representation category.
private theorem rationalRepFunctor_faithful :
    (rationalRepFunctor y G c P δ l E i).Faithful where
  map_injective {F H} f g h := by
    apply rationalRepMapLinear_injective y G c P δ l E i F H
    exact congrArg (fun k ↦ k.hom.toLinearMap) h

set_option maxHeartbeats 2000000 in
-- Assemble the equivalence with the chosen fibre functor and its normalization.
private noncomputable def rationalConstruction :
    RationalGaloisConstruction y G c P δ l E i := by
  let K := rationalRepFunctor y G c P δ l E i
  let : K.Faithful := rationalRepFunctor_faithful y G c P δ l E i
  let : K.Full := rationalRepFunctor_full y G c P δ l E i
  let T := rationalContinuousFunctor y G c P δ l E i
  let : T.Faithful := inferInstanceAs
    (ObjectProperty.lift _ K (rationalRepObject_continuous y G c P δ l E i)).Faithful
  let : T.Full := inferInstanceAs
    (ObjectProperty.lift _ K (rationalRepObject_continuous y G c P δ l E i)).Full
  let : T.EssSurj := rationalContinuousFunctor_essSurj y G c P δ l E i
  let : T.IsEquivalence := {}
  refine { eR := T.asEquivalence
           τR := rationalRepFiberComparison y G c P δ l E i
           localization := ?_ }
  intro F
  refine ⟨LinearEquiv.refl E _, ?_, ?_⟩
  · intro g a z
    rfl
  · intro a z
    exact rationalRepFiberIso_tmul y G c P δ l E i F a z


/-- Rationalize the normalized integral correspondence, including its fibre comparison.
Source: Weil II (1.1.1) c), (1.1.6); Stanford L19, Proposition 1.1.9, second bullet.
(blueprint: new-e7-rational-galois-construction).

Send an integral model to E tensor its integral representation and send a pure tensor
in a rational Hom module to the corresponding scalar multiple of the base-changed map.
The rational composition laws make this a functor.  For finite O_E-modules M,N, every
E-linear map between their rationalizations has a common denominator: choose finitely
many generators of M and lift their images after multiplication by a uniformizer power.
Finite presentation over the noetherian integer ring lets a further common power kill
all lifted relations. The localized action is continuous: the adic topology on the finite
integral module
is its module topology, as follows from a finite free presentation and an open quotient
map. Thus the localization map is continuous. Each rational vector is an inverse scalar
times an integral vector, so its orbit map is continuous. A finite basis expresses the
joint action as a finite sum of continuous orbit maps times continuous coordinates.
Thus the object lies in
the continuous coefficient category.  If the rationalization of a lifted map is
equivariant, every commutator is torsion in Hom_O_E(M,N).
The torsion in this finite module is killed by a single uniformizer power, independent
of the group element.  Multiplying by this power makes the lift equivariant; integral
full faithfulness now gives a sheaf morphism.  The same torsion criterion proves
injectivity on rational Homs.  A continuous coefficient representation has a stable
lattice, giving essential surjectivity.  Thus the functor is an equivalence eR.  Base
change of i.τI, together with the fixed rational fibre functor's pure-tensor map formula,
gives τR.  The tensor identity comparison gives localization and both normalizations. -/
theorem rational_galois_construction_from_integral
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (i : IntegralGaloisConstruction y G c P δ l E) :
    Nonempty (RationalGaloisConstruction y G c P δ l E i) := by
  exact ⟨rationalConstruction y G c P δ l E i⟩

end AlgebraicGeometry.Scheme
