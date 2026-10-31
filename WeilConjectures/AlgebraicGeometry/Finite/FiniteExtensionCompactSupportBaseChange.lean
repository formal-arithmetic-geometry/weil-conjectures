/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCompactSupportExchange
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.CategoryTheory.ScalarLocalization.PbcRationalTransport
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCompactSupportUniformRestriction
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
import all WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Linear
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedConstructiblePreservation
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.UniformCompleteTriangulated
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Compact-support base change over a finite extension

Source: blueprint main-20261015, `thm-cbc-finite-extension`, order 1991
(blueprint: thm-cbc-finite-extension).

The integral compact-support exchange is transported through the raw scalar
localization.  The source and target are the completed compact-support
composites attached to the chosen compactifications; the displayed naturality
equation is the naturality required for every rational morphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

attribute [local irreducible] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme

/-- Stalkwise invertibility detects invertibility of a global section. -/
private theorem finiteExtension_global_unit (l : ℕ) (T : Scheme.{u})
    (h : ∀ x : T, IsUnit (l : T.presheaf.stalk x)) : IsUnit (l : Γ(T, ⊤)) := by
  apply T.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  simpa only [map_natCast] using h x

/-- The residue characteristic kills the first quotient of the valuation ring. -/
private theorem finiteExtension_residue_char
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (l : Padic.coefficientExtensionIntegers l E ⧸
      (pbcPadicCoefficientDatum l E).ideal) = 0 := by
  have H := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hgen := H.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  change (Ideal.Quotient.mk _ (l : Padic.coefficientExtensionIntegers l E)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change (l : Padic.coefficientExtensionIntegers l E) ∈
    Ideal.span {Padic.coefficientExtensionUniformizer l E}
  change Ideal.span {Padic.coefficientExtensionUniformizer l E} =
    Padic.coefficientExtensionMaximalIdeal l E at hgen
  rw [hgen]
  apply (H.2.1 _).2
  have h := spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])
  rw [map_natCast] at h
  change spectralNorm ℚ_[l] E (l : E) < 1
  rw [h]
  exact Padic.norm_p_lt_one

/-- Pullback preservation is the third clause for the identity proper square. -/
private theorem finiteExtension_pull_mem
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    (hU : ∃ n : ℕ, topologicalKrullDim U ≤ (n : WithBot ℕ∞))
    (hV : ∃ n : ℕ, topologicalKrullDim V ≤ (n : WithBot ℕ∞))
    (hlU : IsUnit (l : Γ(U, ⊤))) (hlV : IsUnit (l : Γ(V, ⊤)))
    (g : U ⟶ V) (K : PbcBoundedConstructibleComplete V (pbcPadicCoefficientDatum l E)) :
    PbcIsBoundedConstructibleComplete U (pbcPadicCoefficientDatum l E)
      (((pbcPadicCoefficientDatum l E).completedPull g).obj K.obj) := by
  let s : IsPullback g (𝟙 U) (𝟙 V) g := .of_vert_isIso ⟨by simp⟩
  let square : ChosenCartesianSquare g (𝟙 U) (𝟙 V) g :=
    { w := by simp
      isoPullback := s.isoPullback
      hom_fst := s.isoPullback_hom_fst
      hom_snd := s.isoPullback_hom_snd }
  have hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ V),
      topologicalKrullDim (pullback (𝟙 V) y : Scheme.{u}) ≤
        ((0 : ℕ) : WithBot ℕ∞) := by
    intro Ω _ _ y
    rw [(Scheme.homeoOfIso (asIso (pullback.snd (𝟙 V) y))).isHomeomorph.topologicalKrullDim_eq]
    change topologicalKrullDim (PrimeSpectrum Ω) ≤ 0
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  exact ((pbcPadicCoefficientDatum l E).constructible_preservation square
    hV hV hU hU l (Fact.out : l.Prime).pos (finiteExtension_residue_char l E)
    hlV hlV hlU hlU 0 hfib K.obj K.property).2.2.1

/-- Transport the uniform-restriction theorem to the published compact-support functor. -/
private theorem finiteExtension_support_mem
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (hY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (hlX : IsUnit (l : Γ(X, ⊤))) (hlY : IsUnit (l : Γ(Y, ⊤)))
    {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f)
    (K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E)) :
    PbcIsBoundedConstructibleComplete Y (pbcPadicCoefficientDatum l E)
      ((cbcSupport (pbcPadicCoefficientDatum l E) c).obj K.obj) := by
  let d := pbcPadicCoefficientDatum l E
  have : IsSeparated f := by rw [c.comm]; infer_instance
  have : LocallyOfFiniteType f := by rw [c.comm]; infer_instance
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have := (pbcUniformComplete_isTriangulated Y l E hY hlY).1
  have hm := (cbcIntegralCompactSupport_uniformRestriction l E hX hY hlX hlY f c).1
    K.obj K.property
  apply ObjectProperty.prop_of_iso (PbcIsBoundedConstructibleComplete Y d) _ hm
  change (cbcIntegralCompactSupport l E c).obj K.obj ≅ (cbcSupport d c).obj K.obj
  unfold cbcIntegralCompactSupport proEtaleRingCompactSupportImage
  dsimp only [Functor.comp_obj]
  rw [coefficientIso_eq c.g d]
  exact (d.push c.g).mapIso ((openExtensionIso c.i d).app K.obj)

-- Name the datum explicitly when synthesizing scalars through the alternate category aliases.
private instance finiteExtension_moduleLinear
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u}) (d : AdicCoefficientDatum A) :
    Linear A (proEtaleRingModules T (d.completedRing T)) := pbcCompletedModulesLinear T d

private instance finiteExtension_reductionModuleLinear
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u}) (d : AdicCoefficientDatum A) :
    Linear A (reductionModules T (completedReductionCoefficient T d)) :=
  pbcCompletedModulesLinear T d

private instance finiteExtension_derivedLinear
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u}) (d : AdicCoefficientDatum A) :
    Linear A (d.derived T) := pbcCompletedDerivedLinear T d

private instance finiteExtension_towerLinear
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u}) (d : AdicCoefficientDatum A) :
    Linear A (d.towers T) :=
  inferInstanceAs (Linear A (ℕᵒᵖ ⥤ proEtaleRingModules T (d.completedRing T)))

private instance finiteExtension_derivedTowerLinear
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u}) (d : AdicCoefficientDatum A) :
    Linear A (DerivedCategory (d.towers T)) :=
  inferInstanceAs (Linear A (DerivedCategory (ℕᵒᵖ ⥤
    proEtaleRingModules T (d.completedRing T))))

attribute [local irreducible] completedReductionTower Functor.mapDerivedCategory

/-- Scalar multiplication descends through a universal left-derived pair. -/
private theorem finiteExtension_kan_linear
    {R : Type*} [CommRing R]
    {C D B : Type*} [Category C] [Category D] [Category B]
    [Preadditive C] [Preadditive D] [Preadditive B]
    [Linear R C] [Linear R D] [Linear R B]
    (Q : C ⥤ D) [Q.Linear R] (F : C ⥤ B) [F.Linear R]
    (L : D ⥤ B) (epsilon : Q ⋙ L ⟶ F) [L.IsRightKanExtension epsilon] :
    L.Linear R := by
  rw [Functor.linear_iff]
  intro X r
  let gamma : L ⟶ L :=
    { app := fun Y ↦ L.map (r • 𝟙 Y)
      naturality := fun Y Z f ↦ by
        simp only [← L.map_comp, Linear.comp_smul, Linear.smul_comp,
          Category.comp_id, Category.id_comp] }
  let delta : L ⟶ L :=
    { app := fun Y ↦ r • 𝟙 (L.obj Y)
      naturality := fun Y Z f ↦ by simp }
  have he : gamma = delta := by
    apply L.hom_ext_of_isRightKanExtension epsilon
    ext Y
    have hn := epsilon.naturality (r • 𝟙 Y)
    change L.map (r • 𝟙 (Q.obj Y)) ≫ epsilon.app Y =
      (r • 𝟙 (L.obj (Q.obj Y))) ≫ epsilon.app Y
    simpa using hn
  exact congrArg (fun t : L ⟶ L ↦ t.app X) he

/-- The strict ordinary reduction tower respects constant scalars. -/
private theorem finiteExtension_reduction_linear
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u}) (d : AdicCoefficientDatum A) :
    (completedReductionModuleTowerFunctor T d).Linear A := by
  constructor
  intro M N f a
  apply NatTrans.ext
  funext n
  let phi := completedReductionProjection T d n.unop
  apply level_hom_ext T phi M ((completedReductionLevel T d n.unop).obj N)
  intro U t x
  change ((reductionChange T phi).map (a • f)).val.app U
      (reductionTensorSection T phi M U t x) =
    phi.hom.app U (pbcCompletedSection T d U a) •
      ((reductionChange T phi).map f).val.app U (reductionTensorSection T phi M U t x)
  rw [reductionTensor_map, reductionTensor_map]
  change reductionTensorSection T phi N U t (pbcCompletedSection T d U a • f.val.app U x) = _
  let eta := reductionUnit T phi N
  have heta := (eta.val.app U).hom.map_smul (pbcCompletedSection T d U a) (f.val.app U x)
  change eta.val.app U (pbcCompletedSection T d U a • f.val.app U x) =
    phi.hom.app U (pbcCompletedSection T d U a) •
      (show ((reductionChange T phi).obj N).val.obj U from eta.val.app U (f.val.app U x))
    at heta
  rw [reductionUnit_apply, reductionUnit_apply] at heta
  have ht (y : N.val.obj U) := tensorSection_smul T phi N U t 1 y
  simp only [mul_one] at ht
  change _ = phi.hom.app U (pbcCompletedSection T d U a) •
    (show ((reductionChange T phi).obj N).val.obj U from
      reductionTensorSection T phi N U t (f.val.app U x))
  calc
    _ = t • reductionTensorSection T phi N U 1
        (pbcCompletedSection T d U a • f.val.app U x) := (ht _).symm
    _ = t • (phi.hom.app U (pbcCompletedSection T d U a) •
        reductionTensorSection T phi N U 1 (f.val.app U x)) := congrArg (t • ·) heta
    _ = phi.hom.app U (pbcCompletedSection T d U a) •
        (t • reductionTensorSection T phi N U 1 (f.val.app U x)) := smul_comm _ _ _
    _ = _ := congrArg (phi.hom.app U (pbcCompletedSection T d U a) • ·) (ht _)

/-- Ambient completed pullback preserves the specified constant-section action. -/
private theorem finiteExtension_completedPull_linear
    {A : Type (u + 1)} [CommRing A] {U V : Scheme.{u}}
    (d : AdicCoefficientDatum A) (f : U ⟶ V) : (d.completedPull f).Linear A := by
  have := finiteExtension_reduction_linear V d
  have : (completedReductionHomotopyFunctor V d).Linear A := by
    unfold completedReductionHomotopyFunctor
    infer_instance
  have := (completedReductionTower_properties V d).1
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension
    (completedReductionTower V d) (coherenceReductionTowerCounit V d)
    (HomotopyCategory.quasiIso _ (.up ℤ))
  have : (completedReductionTower V d).Linear A :=
    finiteExtension_kan_linear DerivedCategory.Qh (completedReductionHomotopyFunctor V d)
      (completedReductionTower V d) (coherenceReductionTowerCounit V d)
  have : (proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)).Linear A := by
    rw [← coefficientIso_eq f d]
    exact completedModulePushLinear f d
  have : (proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)).Linear A :=
    (proEtaleRingModuleAdjunction f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)).left_adjoint_linear
  have : (d.towerModulePull f).Linear A := by
    constructor
    intro M N v a
    apply NatTrans.ext
    funext n
    exact Functor.map_smul
      (proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f)) a (v.app n)
  have : (d.constantTower U).Linear A := by
    constructor
    intro M N v a
    apply NatTrans.ext
    funext n
    rfl
  have : (d.derivedConstantTower U).Linear A := by
    unfold AdicCoefficientDatum.derivedConstantTower
    infer_instance
  have : (completedRlim U (d.completedRing U)).Linear A :=
    (d.constantRlimAdjunction U).right_adjoint_linear
  unfold AdicCoefficientDatum.completedPull
  infer_instance

/-- Open extension and direct image respect constant scalars by their adjunctions. -/
private theorem finiteExtension_open_linear
    {A : Type (u + 1)} [CommRing A] {U T : Scheme.{u}}
    (d : AdicCoefficientDatum A) (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (cbcDerivedOpenShriek d j hj).Linear A := by
  let := hj
  have : (proEtaleRingModuleDirectImage j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)).Linear A := by
    rw [← coefficientIso_eq j d]
    exact completedModulePushLinear j d
  have : (proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)).Linear A :=
    (proEtaleRingModuleAdjunction j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)).left_adjoint_linear
  have := cbcPullToRestriction_isIso d j
  have : (cbcOpenRestriction d j hj).Linear A :=
    Functor.linear_of_iso A (asIso (cbcPullToRestriction d j))
  have : (cbcOpenShriek d j hj).Linear A := (cbcOpenAdjunction d j hj).left_adjoint_linear
  unfold cbcDerivedOpenShriek
  infer_instance

private theorem finiteExtension_push_linear
    {A : Type (u + 1)} [CommRing A] {U V : Scheme.{u}}
    (d : AdicCoefficientDatum A) (f : U ⟶ V) : (d.push f).Linear A := by
  have : (proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)).Linear A := by
    rw [← coefficientIso_eq f d]
    exact completedModulePushLinear f d
  unfold AdicCoefficientDatum.push proEtaleRingDerivedDirectImage
  infer_instance

/-- Additivity interface needed by scalar transport for the completed open operation.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension).
Proof: extension by zero is additive on module sections. Its exact termwise functor
respects sums of chain maps, and the equation descends through the derived localization. -/
@[instance] theorem cbcDerivedOpenShriek_additive
    {A : Type (u + 1)} [CommRing A] {U T : Scheme.{u}}
    (d : AdicCoefficientDatum A) (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (cbcDerivedOpenShriek d j hj).Additive := by
  unfold cbcDerivedOpenShriek
  infer_instance

/-- Additivity interface needed by scalar transport for completed pullback.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension).
Proof: the reduction-tower construction and derived tower pullback respect sums on
representatives; derived inverse limit is additive. Compose these three equations. -/
@[instance] theorem completedPull_additive
    {A : Type (u + 1)} [CommRing A] {U V : Scheme.{u}}
    (d : AdicCoefficientDatum A) (f : U ⟶ V) :
    (d.completedPull f).Additive := by
  obtain ⟨shift, tri⟩ := (completedReductionTower_properties V d).2.1
  let := shift
  have := tri
  have : (completedReductionTower V d).Additive := inferInstance
  unfold AdicCoefficientDatum.completedPull
  infer_instance

/-- The source composite is additive.
Proof: extension by zero, derived direct image, and completed pullback are additive
on representative maps. Composition preserves these addition equations.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportSource_additive
    {A : Type (u + 1)} [CommRing A] {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (g : Y' ⟶ Y) (c : Compactification f) (d : AdicCoefficientDatum A) :
    (cbcDerivedOpenShriek d c.i c.isOpenImmersion ⋙ d.push c.g ⋙ d.completedPull g).Additive := by
  infer_instance

/-- The target composite is additive.
Proof: completed pullback, extension by zero, and derived direct image are additive
on representative maps. Composition preserves these addition equations.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportTarget_additive
    {A : Type (u + 1)} [CommRing A] {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'}
    (g' : X' ⟶ X) (c' : Compactification f') (d : AdicCoefficientDatum A) :
    (d.completedPull g' ⋙ cbcDerivedOpenShriek d c'.i c'.isOpenImmersion ⋙
      d.push c'.g).Additive := by
  have := completedPull_additive d g'
  have := cbcDerivedOpenShriek_additive d c'.i c'.isOpenImmersion
  infer_instance

/-- The source compact-support composite in the chosen compactification.
Source: `def-cbc-completed-exchange-map` (blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportSource
    {A : Type (u + 1)} [CommRing A] {X Y Y' : Scheme.{u}}
    {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum A) :=
  cbcDerivedOpenShriek d c.i c.isOpenImmersion ⋙ d.push c.g ⋙ d.completedPull g

/-- The target compact-support composite in the chosen compactification.
Source: `def-cbc-completed-exchange-map` (blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportTarget
    {A : Type (u + 1)} [CommRing A] {X X' Y' : Scheme.{u}}
    {f' : X' ⟶ Y'} (g' : X' ⟶ X) (c' : Compactification f')
    (d : AdicCoefficientDatum A) :=
  d.completedPull g' ⋙ cbcDerivedOpenShriek d c'.i c'.isOpenImmersion ⋙ d.push c'.g

/-- The source lift whose objects retain the constructibility witness.
Source: the integral category restriction in the proof
(blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportSourceLift
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :
    PbcBoundedConstructibleComplete X d ⥤
      PbcBoundedConstructibleComplete Y' d :=
  by
    letI := cbcCompactSupportSource_additive g c d
    exact ObjectProperty.liftFullSubcategory
      (PbcIsBoundedConstructibleComplete X d) (PbcIsBoundedConstructibleComplete Y' d)
      (cbcCompactSupportSource g c d) (fun K hK ↦ hSource ⟨K, hK⟩)

/-- The target lift whose objects retain the constructibility witness.
Source: the integral category restriction in the proof
(blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportTargetLift
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :
    PbcBoundedConstructibleComplete X d ⥤
      PbcBoundedConstructibleComplete Y' d :=
  by
    letI := cbcCompactSupportTarget_additive g' c' d
    exact ObjectProperty.liftFullSubcategory
      (PbcIsBoundedConstructibleComplete X d) (PbcIsBoundedConstructibleComplete Y' d)
      (cbcCompactSupportTarget g' c' d) (fun K hK ↦ hTarget ⟨K, hK⟩)

/-- The source restriction is additive for the inherited full-subcategory addition.
Proof: the restriction maps each morphism by the ambient composite. Its additivity
equation is the ambient equation viewed through the faithful full inclusion.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportSourceLift_additive
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :
    (cbcCompactSupportSourceLift l E g c d hSource).Additive := by
  have := cbcCompactSupportSource_additive g c d
  constructor
  intro M N f h
  apply ObjectProperty.hom_ext
  exact Functor.map_add (cbcCompactSupportSource g c d)

/-- The target restriction is additive for the inherited full-subcategory addition.
Proof: the restriction maps each morphism by the ambient composite. Its additivity
equation is the ambient equation viewed through the faithful full inclusion.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportTargetLift_additive
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :
    (cbcCompactSupportTargetLift l E g' c' d hTarget).Additive := by
  have := cbcCompactSupportTarget_additive g' c' d
  constructor
  intro M N f h
  apply ObjectProperty.hom_ext
  exact Functor.map_add (cbcCompactSupportTarget g' c' d)

/-- The source restriction respects the actual constant-section scalar action.
Proof: tensor, pullback and direct image commute with scalar multiples of maps on
representatives. These equations survive localization and full-subcategory restriction.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportSourceLift_linear
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :
    (cbcCompactSupportSourceLift l E g c d hSource).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  have := finiteExtension_completedPull_linear d g
  have := finiteExtension_open_linear d c.i c.isOpenImmersion
  have := finiteExtension_push_linear d c.g
  have : (cbcCompactSupportSource g c d).Linear
      (Padic.coefficientExtensionIntegers l E) := by
    unfold cbcCompactSupportSource
    infer_instance
  constructor
  intro M N f a
  apply ObjectProperty.hom_ext
  exact Functor.map_smul (cbcCompactSupportSource g c d) a f.hom

/-- The target restriction respects the actual constant-section scalar action.
Proof: tensor, pullback and direct image commute with scalar multiples of maps on
representatives. These equations survive localization and full-subcategory restriction.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportTargetLift_linear
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :
    (cbcCompactSupportTargetLift l E g' c' d hTarget).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  have := finiteExtension_completedPull_linear d g'
  have := finiteExtension_open_linear d c'.i c'.isOpenImmersion
  have := finiteExtension_push_linear d c'.g
  have : (cbcCompactSupportTarget g' c' d).Linear
      (Padic.coefficientExtensionIntegers l E) := by
    unfold cbcCompactSupportTarget
    infer_instance
  constructor
  intro M N f a
  apply ObjectProperty.hom_ext
  exact Functor.map_smul (cbcCompactSupportTarget g' c' d) a f.hom

/-- The two rational functors obtained by scalar transport of these lifts.
Source: `prop-weil-pbc-rational-transport`
(blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportSourceTransport
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :=
  ScalarLocalization.transport (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E)
    (cbcCompactSupportSourceLift l E g c d hSource)

/-- The target rational functor obtained by scalar transport of the target lift.
Source: `prop-weil-pbc-rational-transport`
(blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportTargetTransport
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :=
  ScalarLocalization.transport (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E)
    (cbcCompactSupportTargetLift l E g' c' d hTarget)

/-- The canonical scalar-localized component for one integral representative.
Source: the completed exchange in the compact-support square
(blueprint: thm-cbc-finite-extension). -/
def finiteExtensionCompactSupportExchangeComponent
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (c : Compactification f)
    (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
    (openSquare : OpenImmersionSquare g' c'.i c.i gbar) [QuasiCompact f]
    (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers l E)
    (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum l E).ideal)
    (hSource : ∀ K : PbcBoundedConstructibleComplete X
      (pbcPadicCoefficientDatum l E),
      PbcIsBoundedConstructibleComplete Y' (pbcPadicCoefficientDatum l E)
      (((pbcPadicCoefficientDatum l E).completedPull g).obj
        (((pbcPadicCoefficientDatum l E).push c.g).obj
          ((cbcDerivedOpenShriek (pbcPadicCoefficientDatum l E) c.i
            c.isOpenImmersion).obj K.obj))))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X
      (pbcPadicCoefficientDatum l E),
      PbcIsBoundedConstructibleComplete Y' (pbcPadicCoefficientDatum l E)
      (((pbcPadicCoefficientDatum l E).push c'.g).obj
        ((cbcDerivedOpenShriek (pbcPadicCoefficientDatum l E) c'.i
          c'.isOpenImmersion).obj
          (((pbcPadicCoefficientDatum l E).completedPull g').obj K.obj))))
    (K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E))
    (hComplete : cbcCompleteProperty (pbcPadicCoefficientDatum l E) X r a ha K.obj) :
    (cbcCompactSupportSourceTransport l E g c
      (pbcPadicCoefficientDatum l E) hSource).obj ⟨K⟩ ⟶
    (cbcCompactSupportTargetTransport l E g' c'
      (pbcPadicCoefficientDatum l E) hTarget).obj ⟨K⟩ :=
  (pbcRationalization Y' (pbcPadicCoefficientDatum l E)
    (Padic.coefficientExtensionUniformizer l E)).map
    (ObjectProperty.homMk
      (completedCompactSupportExchange (pbcPadicCoefficientDatum l E)
        c c' gbar properSquare openSquare r a ha ⟨K.obj, hComplete⟩))

attribute [local irreducible] cbcDerivedOpenShriek
  AdicCoefficientDatum.completedPull cbcOrdinaryExchange cbcCompletedPullbackComparison
  AdicCoefficientDatum.completedExchange cbcDatumCompletedTransport
  Functor.rightDerivedFunctor

/-- A pointwise normalization identifies natural maps on overlapping full domains. -/
private theorem finiteExtension_unique_restriction
    {C D : Type*} [Category C] [Category D]
    (P Q : ObjectProperty C) (F G : C ⥤ D)
    (norm : ∀ X : C, (F.obj X ⟶ G.obj X) → Prop)
    (hu : ∃! t : P.ι ⋙ F ⟶ P.ι ⋙ G, ∀ X : P.FullSubcategory, norm X.obj (t.app X))
    (t : P.ι ⋙ F ⟶ P.ι ⋙ G) (ht : ∀ X : P.FullSubcategory, norm X.obj (t.app X))
    (v : Q.ι ⋙ F ⟶ Q.ι ⋙ G) (hv : ∀ X : Q.FullSubcategory, norm X.obj (v.app X))
    (hPQ : ∀ X, P X → Q X) (X : C) (hX : P X) (hX' : Q X) :
    t.app ⟨X, hX⟩ = v.app ⟨X, hX'⟩ := by
  let w : P.ι ⋙ F ⟶ P.ι ⋙ G :=
    { app := fun M ↦ v.app ⟨M.obj, hPQ M.obj M.property⟩
      naturality := fun M N f ↦ v.naturality
        (ObjectProperty.homMk (X := ⟨M.obj, hPQ M.obj M.property⟩)
          (Y := ⟨N.obj, hPQ N.obj N.property⟩) f.hom) }
  have he : t = w := hu.unique ht (fun M ↦ hv ⟨M.obj, hPQ M.obj M.property⟩)
  exact congrArg (fun z ↦ z.app ⟨X, hX⟩) he

/-- Changing generators changes neither the unit-normalized completed open exchange. -/
private theorem finiteExtension_open_exchange_generators
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U U' T T' : Scheme.{u}} {j : U ⟶ T} {j' : U' ⟶ T'}
    {g : T' ⟶ T} {gU : U' ⟶ U} (sq : OpenImmersionSquare gU j' j g)
    [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (s : ℕ) (b : Fin s → A) (hb : Ideal.span (Set.range b) = d.ideal)
    (K : d.derived U) (hK : cbcCompleteProperty d U r a ha K)
    (hK' : cbcCompleteProperty d U s b hb K) :
    (cbcCompletedExchange d sq r a ha).app ⟨K, hK⟩ =
      (cbcCompletedExchange d sq s b hb).app ⟨K, hK'⟩ := by
  have hs (M : d.derived U) (hM : cbcCompleteProperty d U r a ha M) :
      cbcCompleteProperty d U s b hb M :=
    (d.towerComplete_iff_intrinsic U M).mp
      (cbcTowerComplete_of_property d U r a ha M hM) s b hb _ _
  exact finiteExtension_unique_restriction
    (cbcCompleteProperty d U r a ha) (cbcCompleteProperty d U s b hb)
    (cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ cbcCompletedPullback d g)
    (cbcCompletedPullback d gU ⋙ cbcDerivedOpenShriek d j' sq.isOpenImmersion')
    (fun M v ↦ (cbcCompletedPullbackComparison d g).app
        ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj M) ≫ v =
      (cbcOrdinaryExchange d sq).app M ≫
        (cbcDerivedOpenShriek d j' sq.isOpenImmersion').map
          ((cbcCompletedPullbackComparison d gU).app M))
    (cbcCompletedExchange_exists d sq r a ha)
    (cbcCompletedExchange d sq r a ha)
    (cbcCompletedExchange_exists d sq r a ha).exists.choose_spec
    (cbcCompletedExchange d sq s b hb)
    (cbcCompletedExchange_exists d sq s b hb).exists.choose_spec hs K hK hK'

/-- The ordered compact-support exchange has the same generator independence. -/
private theorem finiteExtension_exchange_generators
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare gb c'.g c.g g) (sj : OpenImmersionSquare g' c'.i c.i gb)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (s : ℕ) (b : Fin s → A) (hb : Ideal.span (Set.range b) = d.ideal)
    (K : d.derived X) (hK : cbcCompleteProperty d X r a ha K)
    (hK' : cbcCompleteProperty d X s b hb K) :
    completedCompactSupportExchange d c c' gb sp sj r a ha ⟨K, hK⟩ =
      completedCompactSupportExchange d c c' gb sp sj s b hb ⟨K, hK'⟩ := by
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have he := finiteExtension_open_exchange_generators d sj r a ha s b hb K hK hK'
  simp only [completedCompactSupportExchange, cbcDatumCompletedExchange,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
    ObjectProperty.ι_obj]
  rw [he]

/-- Scalar localization carries a natural isomorphism to its componentwise image. -/
private theorem finiteExtension_transport_iso
    (R : Type*) [CommRing R] (p : R)
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [Linear R C] [Linear R D] (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.Linear R] [G.Linear R] (e : F ≅ G) :
    ∃ v : ScalarLocalization.transport R p F ≅ ScalarLocalization.transport R p G,
      ∀ X : C, v.hom.app ⟨X⟩ =
        (ScalarLocalization.localization R D p).map (e.hom.app X) := by
  let t := ScalarLocalization.transportNat R p e.hom
  have (X : ScalarLocalization R C p) : IsIso (t.app X) := by
    have h := ((ScalarLocalization.localization R D p).mapIso (e.app X.obj)).isIso_hom
    simpa only [t, ScalarLocalization.transportNat, ScalarLocalization.localization,
      Functor.mapIso_hom, Iso.app_hom] using h
  have : IsIso t := NatIso.isIso_of_isIso_app t
  refine ⟨asIso t, ?_⟩
  intro X
  rfl

attribute [local irreducible] ScalarLocalization.transport

/-- The compact-support exchange over a finite extension is the rational
extension of the completed integral exchange.  It is natural in rational
morphisms and every component is invertible.
Source: blueprint thm-cbc-finite-extension, proof steps 1--6
(blueprint: thm-cbc-finite-extension).
Proof:
1. The integral compact-support uniform-restriction theorem gives exact scalar-linear
restrictions of Rp_* j_! for f and its base change. The valuation ring has a length-one
free resolution of each quotient. A bounded input therefore has one common reduction
interval. Apply preservation-constructible to the proper identity square with N=l and
fibre bound zero to obtain constructible preservation by both completed pullbacks.
2. Each integral object is intrinsically complete and has compatible etale origins.
Apply thm-cbc-complete-proetale to its specified completed compact-support exchange.
The landing predicates of step 1 put both endpoints in the full integral category;
its inverse is consequently a morphism in that full category as well.
3. Rational transport extends these scalar-linear functors and their natural exchange.
On each Hom module the extended map sends u tensor a to F(u) tensor a, so extensions
of composites agree with composites of extensions.
4. Tensor the integral inverse with one. The localization composition formula makes
its two composites the localized identities, proving every rational component invertible.
5. Integral naturality extends from pure tensors to every rational map by additivity.
For a rational isomorphism identifying two representatives, this equation is exactly
independence of lattice under the two induced functorial identifications.
6. Localize the integral identity and pasting diagrams. Localization preserves identities,
composition and whiskering, and the intermediate comparison maps cancel as integrally. -/
theorem finiteExtension_compactSupportBaseChange
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (c : Compactification f)
    (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
    (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (_dimX : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (_dimY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (_dimX' : ∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))
    (_dimY' : ∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))
    (_hlX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (_hlX' : ∀ x' : X', IsUnit (l : X'.presheaf.stalk x'))
    (_hlY' : ∀ y' : Y', IsUnit (l : Y'.presheaf.stalk y')) :
    ∃ (hSource : ∀ K : PbcBoundedConstructibleComplete X
        (pbcPadicCoefficientDatum l E),
      PbcIsBoundedConstructibleComplete Y' (pbcPadicCoefficientDatum l E)
        ((cbcCompactSupportSource g c (pbcPadicCoefficientDatum l E)).obj K.obj)),
      ∃ (hTarget : ∀ K : PbcBoundedConstructibleComplete X
        (pbcPadicCoefficientDatum l E),
      PbcIsBoundedConstructibleComplete Y' (pbcPadicCoefficientDatum l E)
        ((cbcCompactSupportTarget g' c' (pbcPadicCoefficientDatum l E)).obj K.obj)),
      ∃ η : cbcCompactSupportSourceTransport l E g c
          (pbcPadicCoefficientDatum l E) hSource ≅
        cbcCompactSupportTargetTransport l E g' c'
          (pbcPadicCoefficientDatum l E) hTarget,
        ∀ (K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E))
          (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers l E)
          (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum l E).ideal)
          (hComplete : cbcCompleteProperty (pbcPadicCoefficientDatum l E) X r a ha K.obj),
          η.hom.app ⟨K⟩ =
            finiteExtensionCompactSupportExchangeComponent l E c c' gbar
              properSquare openSquare r a ha hSource hTarget K hComplete := by
  classical
  let d := pbcPadicCoefficientDatum l E
  let R := Padic.coefficientExtensionIntegers l E
  let pi := Padic.coefficientExtensionUniformizer l E
  have hlX := finiteExtension_global_unit l X _hlX
  have hlY := finiteExtension_global_unit l Y _hlY
  have hlX' := finiteExtension_global_unit l X' _hlX'
  have hlY' := finiteExtension_global_unit l Y' _hlY'
  have : QuasiCompact f' := cbcBaseChangeQuasiCompact c c' gbar openSquare
  let hSource (K : PbcBoundedConstructibleComplete X d) :=
    finiteExtension_pull_mem l E _dimY' _dimY hlY' hlY g
      ⟨_, finiteExtension_support_mem l E _dimX _dimY hlX hlY c K⟩
  let hTarget (K : PbcBoundedConstructibleComplete X d) :=
    finiteExtension_support_mem l E _dimX' _dimY' hlX' hlY' c'
      ⟨_, finiteExtension_pull_mem l E _dimX' _dimX hlX' hlX g' K⟩
  refine ⟨hSource, hTarget, ?_⟩
  obtain ⟨r₀, a₀, ha₀⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  let F := cbcCompactSupportSourceLift l E g c d hSource
  let G := cbcCompactSupportTargetLift l E g' c' d hTarget
  let e (K : PbcBoundedConstructibleComplete X d) : F.obj K ≅ G.obj K := by
    have := (completeCompactSupportProetale_isIso d c c' gbar properSquare openSquare
      r₀ a₀ ha₀ ⟨K.obj, wfConstructible_complete X d r₀ a₀ ha₀ K⟩ K.property.2.2).1
    exact ObjectProperty.isoMk _ (asIso (completedCompactSupportExchange d c c' gbar
      properSquare openSquare r₀ a₀ ha₀
        ⟨K.obj, wfConstructible_complete X d r₀ a₀ ha₀ K⟩))
  let eta : F ≅ G := NatIso.ofComponents e (by
    intro K H k
    apply ObjectProperty.hom_ext
    exact (completeCompactSupportProetale_isIso d c c' gbar properSquare openSquare
      r₀ a₀ ha₀ ⟨K.obj, wfConstructible_complete X d r₀ a₀ ha₀ K⟩ K.property.2.2).2
        ⟨H.obj, wfConstructible_complete X d r₀ a₀ ha₀ H⟩ k.hom)
  obtain ⟨etaQ, hQ⟩ := finiteExtension_transport_iso R pi F G eta
  refine ⟨etaQ, ?_⟩
  intro K r a ha hComplete
  have hi : eta.hom.app K = ObjectProperty.homMk
      (X := F.obj K) (Y := G.obj K)
      (completedCompactSupportExchange d c c' gbar properSquare openSquare r a ha
        ⟨K.obj, hComplete⟩) := by
    apply ObjectProperty.hom_ext
    exact finiteExtension_exchange_generators d c c' gbar properSquare openSquare
      r₀ a₀ ha₀ r a ha K.obj (wfConstructible_complete X d r₀ a₀ ha₀ K) hComplete
  have hk := hQ K
  rw [hi] at hk
  exact hk

/-- The category-domain hypotheses used by the identity and pasted-square clauses.
This only collects the three geometric conditions from the statement.
Source: blueprint thm-cbc-finite-extension, statement, first paragraph
(blueprint: thm-cbc-finite-extension). -/
def CbcFiniteExtensionDomain (l : ℕ) (T : Scheme.{u}) : Prop :=
  IsNoetherian T ∧ (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞)) ∧
    ∀ x : T, IsUnit (l : T.presheaf.stalk x)

/-- Intrinsic completeness of a selected integral object, for every presentation of I.
Source: blueprint thm-cbc-finite-extension, proof step 2
(blueprint: thm-cbc-finite-extension).
Proof: membership includes invertibility of the intrinsic Koszul completion unit on
some generating tuple and representative. The canonical coefficient comparison transports
that unit, retaining its normalization. Koszul reconstruction identifies it with the
canonical quotient-tower completion map. For any other finite tuple generating the same
ideal and any other representative, reconstruction identifies its unit with that same map,
conjugated by the representative comparison. Its invertibility is therefore unchanged.
Use the specified Q preimage representative to obtain cbcCompleteProperty. This also
covers the empty tuple when it generates the ideal; no completeness hypothesis is added. -/
theorem finiteExtension_cbcComplete
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) (K : PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E))
    (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers l E)
    (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum l E).ideal) :
    cbcCompleteProperty (pbcPadicCoefficientDatum l E) T r a ha K.obj := by
  exact wfConstructible_complete T (pbcPadicCoefficientDatum l E) r a ha K

/-- Localization of an ambient arrow between selected integral objects.
Applied to a path, this is its rational path: the full inclusion and localization preserve
composition and identities. In particular the following equations use the actual canonical
integral comparisons, with no arbitrary endpoint isomorphism.
Source: blueprint thm-cbc-finite-extension, proof steps 3 and 6
(blueprint: thm-cbc-finite-extension). -/
def finiteExtensionRationalArrow
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {T : Scheme.{u}} {M N : (pbcPadicCoefficientDatum l E).derived T}
    (hM : PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E) M)
    (hN : PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E) N)
    (v : M ⟶ N) :
    (pbcRationalization T (pbcPadicCoefficientDatum l E)
      (Padic.coefficientExtensionUniformizer l E)).obj ⟨M, hM⟩ ⟶
    (pbcRationalization T (pbcPadicCoefficientDatum l E)
      (Padic.coefficientExtensionUniformizer l E)).obj ⟨N, hN⟩ :=
  (pbcRationalization T (pbcPadicCoefficientDatum l E)
    (Padic.coefficientExtensionUniformizer l E)).map (ObjectProperty.homMk v)

section Coherence

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Rational identity-base-change coherence, with the unit-normalized completed identity
comparisons. Both paths are localized in the raw rational category of Y.
Source: blueprint thm-cbc-finite-extension, identity clause and proof step 6
(blueprint: thm-cbc-finite-extension).
Proof: apply completeCompactSupportProetale_identity to the complete integral object
with its compatible origins. Integral compact support and completed pullback land in the
selected subcategories by proof step 1. Regard both paths as morphisms of the full integral
subcategory and apply its rationalization functor. This functor preserves compositions and
identities, giving precisely the displayed rational paths. The component formula of the
main theorem identifies their exchange with the rational natural isomorphism. -/
theorem finiteExtension_compactSupportBaseChange_identity
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hX : CbcFiniteExtensionDomain l X) (_hY : CbcFiniteExtensionDomain l Y)
    (c : Compactification f)
    (sp : ChosenCartesianSquare (𝟙 c.Z) c.g c.g (𝟙 Y))
    (sj : OpenImmersionSquare (𝟙 X) c.i c.i (𝟙 c.Z))
    (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers l E)
    (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum l E).ideal)
    (K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E)) :
    ∃ (hK : (pbcPadicCoefficientDatum l E).TowerComplete X K.obj)
      (hF : (pbcPadicCoefficientDatum l E).TowerComplete Y
        ((cbcSupport (pbcPadicCoefficientDatum l E) c).obj K.obj))
      (hS : PbcIsBoundedConstructibleComplete Y (pbcPadicCoefficientDatum l E)
        (((pbcPadicCoefficientDatum l E).completedPull (𝟙 Y)).obj
          ((cbcSupport (pbcPadicCoefficientDatum l E) c).obj K.obj)))
      (hT : PbcIsBoundedConstructibleComplete Y (pbcPadicCoefficientDatum l E)
        ((cbcSupport (pbcPadicCoefficientDatum l E) c).obj K.obj)),
      finiteExtensionRationalArrow l E hS hT
        (cbcExchange (pbcPadicCoefficientDatum l E) c c (𝟙 c.Z) sp sj r a ha
            ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩ ≫
          (cbcSupport (pbcPadicCoefficientDatum l E) c).map
            ((pbcPadicCoefficientDatum l E).completedPullId X K.obj hK).hom) =
      finiteExtensionRationalArrow l E hS hT
        ((pbcPadicCoefficientDatum l E).completedPullId Y
          ((cbcSupport (pbcPadicCoefficientDatum l E) c).obj K.obj) hF).hom := by
  let d := pbcPadicCoefficientDatum l E
  have := _hX.1
  have := _hY.1
  obtain ⟨hK, hF, he⟩ := completeCompactSupportProetale_identity d c sp sj r a ha
    ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩ K.property.2.2
  have hT := finiteExtension_support_mem l E _hX.2.1 _hY.2.1
    (finiteExtension_global_unit l X _hX.2.2) (finiteExtension_global_unit l Y _hY.2.2) c K
  have hS := finiteExtension_pull_mem l E _hY.2.1 _hY.2.1
    (finiteExtension_global_unit l Y _hY.2.2) (finiteExtension_global_unit l Y _hY.2.2)
    (𝟙 Y) ⟨_, hT⟩
  refine ⟨hK, hF, hS, hT, ?_⟩
  exact congrArg (finiteExtensionRationalArrow l E hS hT) he

/-- Rational horizontal-pasting coherence for two arbitrary successive base changes.
The paths retain the canonical completion-unit-normalized pullback compositors.
Source: blueprint thm-cbc-finite-extension, pasted-square clause and proof step 6
(blueprint: thm-cbc-finite-extension).
Proof: proof step 1 gives constructible complete landing for the intermediate pullback
and all endpoints. Apply completeCompactSupportProetale_horizontal, using the input's
intrinsic completeness and compatible etale origins. Localize its two paths in the full
selected category of Y''. Functoriality of localization and the pure-tensor formula for
scalar transport identify these with the two rational pasted paths. The main component
formula identifies every exchange factor with its specified rational component. -/
theorem finiteExtension_compactSupportBaseChange_horizontal
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hX : CbcFiniteExtensionDomain l X) (_hX' : CbcFiniteExtensionDomain l X')
    (_hX'' : CbcFiniteExtensionDomain l X'') (_hY : CbcFiniteExtensionDomain l Y)
    (_hY' : CbcFiniteExtensionDomain l Y') (_hY'' : CbcFiniteExtensionDomain l Y'')
    (c : Compactification f) (c' : Compactification f') (c'' : Compactification f'')
    (gb : c'.Z ⟶ c.Z) (hb : c''.Z ⟶ c'.Z)
    (sp₁ : ChosenCartesianSquare gb c'.g c.g g)
    (sj₁ : OpenImmersionSquare g' c'.i c.i gb)
    (sp₂ : ChosenCartesianSquare hb c''.g c'.g h)
    (sj₂ : OpenImmersionSquare h' c''.i c'.i hb)
    (sp : ChosenCartesianSquare (hb ≫ gb) c''.g c.g (h ≫ g))
    (sj : OpenImmersionSquare (h' ≫ g') c''.i c.i (hb ≫ gb))
    (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers l E)
    (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum l E).ideal)
    (K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E)) :
    ∃ (hK' : cbcCompleteProperty (pbcPadicCoefficientDatum l E) X' r a ha
        (((pbcPadicCoefficientDatum l E).completedPull g').obj K.obj))
      (hS : PbcIsBoundedConstructibleComplete Y'' (pbcPadicCoefficientDatum l E)
        (((pbcPadicCoefficientDatum l E).completedPull (h ≫ g)).obj
          ((cbcSupport (pbcPadicCoefficientDatum l E) c).obj K.obj)))
      (hT : PbcIsBoundedConstructibleComplete Y'' (pbcPadicCoefficientDatum l E)
        ((cbcSupport (pbcPadicCoefficientDatum l E) c'').obj
          (((pbcPadicCoefficientDatum l E).completedPull (h' ≫ g')).obj K.obj))),
      finiteExtensionRationalArrow l E hS hT
        (cbcExchange (pbcPadicCoefficientDatum l E) c c'' (hb ≫ gb) sp sj r a ha
          ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩) =
      finiteExtensionRationalArrow l E hS hT
        (((pbcPadicCoefficientDatum l E).completedPullComp h g).hom.app
            ((cbcSupport (pbcPadicCoefficientDatum l E) c).obj K.obj) ≫
          ((pbcPadicCoefficientDatum l E).completedPull h).map
            (cbcExchange (pbcPadicCoefficientDatum l E) c c' gb sp₁ sj₁ r a ha
              ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩) ≫
          cbcExchange (pbcPadicCoefficientDatum l E)
            (qf := cbcBaseChangeQuasiCompact c c' gb sj₁)
            c' c'' hb sp₂ sj₂ r a ha
            ⟨((pbcPadicCoefficientDatum l E).completedPull g').obj K.obj, hK'⟩ ≫
          (cbcSupport (pbcPadicCoefficientDatum l E) c'').map
            (((pbcPadicCoefficientDatum l E).completedPullComp h' g').inv.app K.obj)) := by
  let d := pbcPadicCoefficientDatum l E
  have := _hX.1
  have := _hX''.1
  have := _hY.1
  have := _hY''.1
  have : QuasiCompact f'' := cbcBaseChangeQuasiCompact c c'' (hb ≫ gb) sj
  obtain ⟨hK', he⟩ := completeCompactSupportProetale_horizontal d c c' c'' gb hb
    sp₁ sj₁ sp₂ sj₂ sp sj r a ha
    ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩ K.property.2.2
  have hF := finiteExtension_support_mem l E _hX.2.1 _hY.2.1
    (finiteExtension_global_unit l X _hX.2.2) (finiteExtension_global_unit l Y _hY.2.2) c K
  have hS := finiteExtension_pull_mem l E _hY''.2.1 _hY.2.1
    (finiteExtension_global_unit l Y'' _hY''.2.2) (finiteExtension_global_unit l Y _hY.2.2)
    (h ≫ g) ⟨_, hF⟩
  have hP := finiteExtension_pull_mem l E _hX''.2.1 _hX.2.1
    (finiteExtension_global_unit l X'' _hX''.2.2) (finiteExtension_global_unit l X _hX.2.2)
    (h' ≫ g') K
  have hT := finiteExtension_support_mem l E _hX''.2.1 _hY''.2.1
    (finiteExtension_global_unit l X'' _hX''.2.2)
    (finiteExtension_global_unit l Y'' _hY''.2.2) c'' ⟨_, hP⟩
  refine ⟨hK', hS, hT, ?_⟩
  exact congrArg (finiteExtensionRationalArrow l E hS hT) he

/-- Rational vertical-pasting coherence, with the canonical proper/open composition
maps for supplied compatible compactification towers. No Cartesian refinement is imposed.
Source: blueprint thm-cbc-finite-extension, pasted-square clause and proof step 6
(blueprint: thm-cbc-finite-extension).
Proof: compact-support preservation in proof step 1 supplies the complete intermediate
image and all constructible endpoints. Apply completeCompactSupportProetale_vertical
with the input's compatible origins. Its comparisons are the specified proper/open mates
and are invertible. Localize its two ordered paths. Preservation of composition and the
scalar-transport formula identify these with rational vertical pasting. The integral
composition/refinement law makes the same equation valid after any common refinement,
so the supplied compatible towers do not restrict the allowed pasted squares. -/
theorem finiteExtension_compactSupportBaseChange_vertical
    {X X' Y Y' Z Z' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {h : Y ⟶ Z} {h' : Y' ⟶ Z'}
    {gx : X' ⟶ X} {gy : Y' ⟶ Y} {gz : Z' ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (_hX : CbcFiniteExtensionDomain l X) (_hX' : CbcFiniteExtensionDomain l X')
    (_hY : CbcFiniteExtensionDomain l Y) (_hY' : CbcFiniteExtensionDomain l Y')
    (_hZ : CbcFiniteExtensionDomain l Z) (_hZ' : CbcFiniteExtensionDomain l Z')
    (cf : Compactification f) (ch : Compactification h)
    (chf : Compactification (f ≫ h))
    (cf' : Compactification f') (ch' : Compactification h')
    (chf' : Compactification (f' ≫ h'))
    (gbf : cf'.Z ⟶ cf.Z) (gbh : ch'.Z ⟶ ch.Z) (gbhf : chf'.Z ⟶ chf.Z)
    (spf : ChosenCartesianSquare gbf cf'.g cf.g gy)
    (sjf : OpenImmersionSquare gx cf'.i cf.i gbf)
    (sph : ChosenCartesianSquare gbh ch'.g ch.g gz)
    (sjh : OpenImmersionSquare gy ch'.i ch.i gbh)
    (sphf : ChosenCartesianSquare gbhf chf'.g chf.g gz)
    (sjhf : OpenImmersionSquare gx chf'.i chf.i gbhf)
    (b : cf.Z ⟶ chf.Z) (p : chf.Z ⟶ ch.Z)
    (b' : cf'.Z ⟶ chf'.Z) (p' : chf'.Z ⟶ ch'.Z)
    [IsProper p] [IsProper p']
    (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
    (hq : p ≫ ch.g = chf.g)
    (hb' : cf'.i ≫ b' = chf'.i) (hp' : b' ≫ p' = cf'.g ≫ ch'.i)
    (hq' : p' ≫ ch'.g = chf'.g)
    (sq : IsPullback b cf.g p ch.i) (sq' : IsPullback b' cf'.g p' ch'.i)
    (_wb : b' ≫ gbhf = gbf ≫ b) (_wp : p' ≫ gbh = gbhf ≫ p)
    (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers l E)
    (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum l E).ideal)
    (K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E)) :
    ∃ (hF : cbcCompleteProperty (pbcPadicCoefficientDatum l E) Y r a ha
        ((cbcSupport (pbcPadicCoefficientDatum l E) cf).obj K.obj))
      (hS : PbcIsBoundedConstructibleComplete Z' (pbcPadicCoefficientDatum l E)
        (((pbcPadicCoefficientDatum l E).completedPull gz).obj
          ((cbcSupport (pbcPadicCoefficientDatum l E) ch).obj
            ((cbcSupport (pbcPadicCoefficientDatum l E) cf).obj K.obj))))
      (hT : PbcIsBoundedConstructibleComplete Z' (pbcPadicCoefficientDatum l E)
        ((cbcSupport (pbcPadicCoefficientDatum l E) chf').obj
          (((pbcPadicCoefficientDatum l E).completedPull gx).obj K.obj))),
      finiteExtensionRationalArrow l E hS hT
        (((pbcPadicCoefficientDatum l E).completedPull gz).map
            (cbcTowerCompositionMap (pbcPadicCoefficientDatum l E)
              cf ch chf b p hb hp hq sq K.obj) ≫
          cbcExchange (pbcPadicCoefficientDatum l E) chf chf' gbhf sphf sjhf r a ha
            ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩) =
      finiteExtensionRationalArrow l E hS hT
        (cbcExchange (pbcPadicCoefficientDatum l E) ch ch' gbh sph sjh r a ha
            ⟨(cbcSupport (pbcPadicCoefficientDatum l E) cf).obj K.obj, hF⟩ ≫
          (cbcSupport (pbcPadicCoefficientDatum l E) ch').map
            (cbcExchange (pbcPadicCoefficientDatum l E) cf cf' gbf spf sjf r a ha
              ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩) ≫
          cbcTowerCompositionMap (pbcPadicCoefficientDatum l E)
            (qh := cbcBaseChangeQuasiCompact ch ch' gbh sjh)
            cf' ch' chf' b' p' hb' hp' hq' sq'
            (((pbcPadicCoefficientDatum l E).completedPull gx).obj K.obj)) := by
  let d := pbcPadicCoefficientDatum l E
  have := _hX.1
  have := _hX'.1
  have := _hY.1
  have := _hZ.1
  have := _hZ'.1
  have : QuasiCompact (f ≫ h) := inferInstance
  have : QuasiCompact (f' ≫ h') := cbcBaseChangeQuasiCompact chf chf' gbhf sjhf
  obtain ⟨_, _, hF, he⟩ := completeCompactSupportProetale_vertical d
    cf ch chf cf' ch' chf' gbf gbh gbhf spf sjf sph sjh sphf sjhf
    b p b' p' hb hp hq hb' hp' hq' sq sq' _wb _wp r a ha
    ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩ K.property.2.2
  have hFK := finiteExtension_support_mem l E _hX.2.1 _hY.2.1
    (finiteExtension_global_unit l X _hX.2.2) (finiteExtension_global_unit l Y _hY.2.2) cf K
  have hHK := finiteExtension_support_mem l E _hY.2.1 _hZ.2.1
    (finiteExtension_global_unit l Y _hY.2.2) (finiteExtension_global_unit l Z _hZ.2.2)
    ch ⟨_, hFK⟩
  have hS := finiteExtension_pull_mem l E _hZ'.2.1 _hZ.2.1
    (finiteExtension_global_unit l Z' _hZ'.2.2) (finiteExtension_global_unit l Z _hZ.2.2)
    gz ⟨_, hHK⟩
  have hP := finiteExtension_pull_mem l E _hX'.2.1 _hX.2.1
    (finiteExtension_global_unit l X' _hX'.2.2) (finiteExtension_global_unit l X _hX.2.2) gx K
  have hT := finiteExtension_support_mem l E _hX'.2.1 _hZ'.2.1
    (finiteExtension_global_unit l X' _hX'.2.2) (finiteExtension_global_unit l Z' _hZ'.2.2)
    chf' ⟨_, hP⟩
  refine ⟨hF, hS, hT, ?_⟩
  exact congrArg (finiteExtensionRationalArrow l E hS hT) he

end Coherence

end AlgebraicGeometry.Scheme
