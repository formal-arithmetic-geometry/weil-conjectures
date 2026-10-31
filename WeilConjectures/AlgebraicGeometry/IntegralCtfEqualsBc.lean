/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.Topology.Instances.ZMod
import WeilConjectures.AlgebraicGeometry.LocalizingClosureCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.CohomologyTorInterval
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import all WeilConjectures.AlgebraicGeometry.ConstantSquareZeroTorExample
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncodingSupplement
import all WeilConjectures.AlgebraicGeometry.PullbackFiniteConstantLocalModel

/-! # Integral and rational constructible complexes have finite Tor amplitude

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-prop-integral-criterion/lem-integral-ctf-equals-bc.md and its proof
(blueprint: lem-integral-ctf-equals-bc).

The categories are ordinary uncompleted internal-module derived categories. The scalar
examples are stated on explicit helper definitions of this module.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj MonoidalCategory ZeroObject

namespace AlgebraicGeometry.ProEtale

/-- Constructible modules have amplitude [-1,0], or [0,0] for field coefficients;
bounded constructible complexes inherit the indicated cohomological interval, enlarged
by one only in the integral case. In particular Dctf and Dbc have identical object
predicates, hence identical full subcategories and ambient morphisms.

Source: latest blueprint lem-integral-ctf-equals-bc, clauses (1), (2) and their consequence
(blueprint: lem-integral-ctf-equals-bc).

Proof:
1. The integral clauses come from det-def-localizing-closure-ctf-equals-bc
(localizingClosure_ctf_equals_bc). Constructible modules have amplitude [-1,0], and bounded
constructible complexes with cohomology in [a,b] have amplitude [a-1,b]. The object predicates
of Dctf and Dbc are equal. That theorem combines lem-sfb-padic-constant-local-model-tor,
lem-sfb-stratified-tor-interval-devissage and lem-sfb-cohomology-tor-interval. Its field
clause gives amplitude [0,0] for constructible modules over E, Q_ell or Qlb.
2. Over a field, let K be in Dbc with cohomology in [a,b]. Each H^q(K) is constructible by
the definition in det-def-sfb-constructible-tor-amplitude, so it has amplitude [0,0] by
step 1. lem-sfb-cohomology-tor-interval with c=d=0 then gives amplitude [a,b]. No
completeness hypothesis is used. -/
theorem integral_ctf_equals_bc (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ :
      Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E)) ∨
        Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X),
      IsConstantModelConstructible Λ.X X M → DerivedCategory.torAmplitudeIn _ (-1) 0
        ((DerivedCategory.singleFunctor _ 0).obj M)) ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
        (a b : ℤ), a ≤ b → constantModelBoundedConstructible Λ.X X K →
      DerivedCategory.homologyConcentratedIn a b K →
      DerivedCategory.torAmplitudeIn _ (a - 1) b K) ∧
    ((Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) →
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X),
        IsConstantModelConstructible Λ.X X M → DerivedCategory.torAmplitudeIn _ 0 0
          ((DerivedCategory.singleFunctor _ 0).obj M)) ∧
      (∀ (K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
          (a b : ℤ), a ≤ b → constantModelBoundedConstructible Λ.X X K →
        DerivedCategory.homologyConcentratedIn a b K →
        DerivedCategory.torAmplitudeIn _ a b K)) ∧
    (constantModelBoundedConstructible Λ.X X ⊓ DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible Λ.X X := by
  obtain ⟨h, hfield⟩ := localizingClosure_ctf_equals_bc ℓ X Λ.X hΛ
  refine ⟨h.1, h.2.1, ?_, h.2.2.1⟩
  intro hΛfield
  have hmod := hfield hΛfield
  refine ⟨hmod, ?_⟩
  intro K a b hab hK hbound
  have htor := torAmplitudeIn_of_cohomology_interval X Λ K a b 0 0 hab le_rfl
    (fun q hq ↦ by
      by_cases hqa : q < a
      · exact (DerivedCategory.isGE_iff K a).1 hbound.1 q hqa
      · exact (DerivedCategory.isLE_iff K b).1 hbound.2 q (by
          simp only [Set.mem_Icc] at hq
          omega))
    (fun q _ ↦ hmod _ (hK.2 q))
  simpa only [add_zero] using htor

/-- The scalar residue `(Z/ell²)/(ell)` of the specific square-zero example.
Source: blueprint latest, integral criterion, lem-integral-ctf-equals-bc, The examples
(blueprint: lem-integral-ctf-equals-bc). -/
abbrev integralCriterionScalarResidue (ℓ : ℕ) : Type :=
  ZMod (ℓ ^ 2) ⧸ Ideal.span ({(ℓ : ZMod (ℓ ^ 2))} : Set (ZMod (ℓ ^ 2)))

/-- The specified scalar complex `[A --ell--> A]` in degrees -1,0, represented by
its mapping cone. Its multiplication map is the actual scalar linear map.
Source: blueprint latest, integral criterion, lem-integral-ctf-equals-bc, The examples
(blueprint: lem-integral-ctf-equals-bc). -/
noncomputable def integralCriterionScalarTwoTerm (ℓ : ℕ) :
    DerivedCategory (ModuleCat.{0} (ZMod (ℓ ^ 2))) :=
  let A := ZMod (ℓ ^ 2)
  let F := CochainComplex.singleFunctor (ModuleCat.{0} A) 0
  let f : F.obj (ModuleCat.of A A) ⟶ F.obj (ModuleCat.of A A) :=
    F.map (ModuleCat.ofHom (LinearMap.mulLeft A (ℓ : A)))
  DerivedCategory.Q.obj (CochainComplex.mappingCone f)

/-- The finiteness, infinite projective dimension, and perfectness assertions for the
specified scalar square-zero example. Perfectness uses the recorded bounded finite
projective complex predicate, with no new perfectness convention.
Source: blueprint latest, integral criterion, lem-integral-ctf-equals-bc, The examples
(blueprint: lem-integral-ctf-equals-bc). -/
def integralCriterionScalarExample (ℓ : ℕ) : Prop :=
  Module.Finite (ZMod (ℓ ^ 2)) (integralCriterionScalarResidue ℓ) ∧
  ¬ ModuleCat.HasFiniteProjectiveDimension
    (ModuleCat.of (ZMod (ℓ ^ 2)) (integralCriterionScalarResidue ℓ)) ∧
  DerivedCategory.IsPerfectRingComplex (integralCriterionScalarTwoTerm ℓ) ∧
  ¬ DerivedCategory.IsPerfectRingComplex
    ((DerivedCategory.singleFunctor (ModuleCat.{0} (ZMod (ℓ ^ 2))) 0).obj
      (ModuleCat.of (ZMod (ℓ ^ 2)) (integralCriterionScalarResidue ℓ)))

private noncomputable def doubleConeHom {A : Type*} [Category A] [Abelian A] {X Y : A} (f : X ⟶ Y) :
    HomologicalComplex.double f (by decide : (ComplexShape.up ℤ).Rel (-1) 0) ⟶
      CochainComplex.mappingCone ((HomologicalComplex.single A (.up ℤ) 0).map f) :=
  HomologicalComplex.mkHomFromDouble (by decide) (by decide)
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv ≫
      (CochainComplex.mappingCone.inl _).v 0 (-1) (by decide))
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).inv ≫
      (CochainComplex.mappingCone.inr _).f 0)
    (by
      rw [Category.assoc, CochainComplex.mappingCone.inl_v_d _ 0 (-1) 1
        (by decide) (by decide)]
      simp [HomologicalComplex.single_map_f_self])
    (by
      intro k hk
      simp)

private noncomputable def doubleConeIso {A : Type*} [Category A] [Abelian A] {X Y : A} (f : X ⟶ Y) :
    HomologicalComplex.double f (by decide : (ComplexShape.up ℤ).Rel (-1) 0) ≅
      CochainComplex.mappingCone ((HomologicalComplex.single A (.up ℤ) 0).map f) := by
  let g := doubleConeHom f
  have hg : ∀ n : ℤ, IsIso (g.f n) := by
    intro n
    by_cases h : n = -1
    · subst n
      let gi := (CochainComplex.mappingCone.fst
        ((HomologicalComplex.single A (.up ℤ) 0).map f)).1.v (-1) 0 (by decide) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom ≫
        (HomologicalComplex.doubleXIso₀ f (by decide : (ComplexShape.up ℤ).Rel (-1) 0)).inv
      refine ⟨⟨gi, ?_, ?_⟩⟩
      · simp [g, gi, doubleConeHom]
      · apply CochainComplex.mappingCone.ext_from _ 0 (-1) (by decide)
        · simp [g, gi, doubleConeHom]
        · apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 Y (-1)
            (by decide)).eq_of_src
    · by_cases h' : n = 0
      · subst n
        let gi := (CochainComplex.mappingCone.snd
          ((HomologicalComplex.single A (.up ℤ) 0).map f)).v 0 0 (by decide) ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom ≫
          (HomologicalComplex.doubleXIso₁ f
            (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide)).inv
        refine ⟨⟨gi, ?_, ?_⟩⟩
        · simp [g, gi, doubleConeHom]
        · apply CochainComplex.mappingCone.ext_from _ 1 0 (by decide)
          · apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X 1
              (by decide)).eq_of_src
          · simp [g, gi, doubleConeHom]
      · exact (HomologicalComplex.isZero_double_X f (by decide) n h h').isIso
          ((CochainComplex.mappingCone.isZero_X_iff _ n).mpr
            ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X (n + 1) (by omega),
              HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 Y n h'⟩) _
  letI := hg
  letI := HomologicalComplex.Hom.isIso_of_components g
  exact asIso g


/-- The scalar square-zero example, including both cohomology modules of the explicit
free two-term complex. The quotient A/(ell) is the residue field F_ell.

Source: latest blueprint lem-integral-ctf-equals-bc, final paragraph
(blueprint: lem-integral-ctf-equals-bc).

Proof: the scalar clause of det-def-localizing-closure-ctf-equals-bc supplies three facts.
The residue is finite with infinite projective dimension and is not perfect (periodic Tor,
lem-sfb-square-zero-periodic-tensor), and the cone of multiplication by ell is perfect.
Reduction ZMod(ell²) -> ZMod ell is surjective with kernel (ell), which gives the residue
ring isomorphism. The cone of ell on single complexes is isomorphic to the two-term complex
[A --ell--> A] in degrees -1,0, via the canonical cone inclusions. That complex is
concentrated in [-1,0], with H^0 = coker(ell) = A/(ell). Since ann(ell) = ell A, the
sequence ell, ell is exact, so H^{-1} = ker(ell) = im(ell) is also isomorphic to coker(ell). -/
theorem integral_ctf_scalar_counterexample (ℓ : ℕ) [Fact ℓ.Prime] :
    integralCriterionScalarExample ℓ ∧
    Nonempty (integralCriterionScalarResidue ℓ ≃+* ZMod ℓ) ∧
    DerivedCategory.homologyConcentratedIn (-1) 0 (integralCriterionScalarTwoTerm ℓ) ∧
    (∀ q : ℤ, q = -1 ∨ q = 0 → Nonempty
      ((DerivedCategory.homologyFunctor (ModuleCat.{0} (ZMod (ℓ ^ 2))) q).obj
        (integralCriterionScalarTwoTerm ℓ) ≅
        ModuleCat.of (ZMod (ℓ ^ 2)) (integralCriterionScalarResidue ℓ))) := by
  classical
  have : NeZero (ℓ ^ 2) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have hexample := (localizingClosure_ctf_equals_bc ℓ (Spec (.of (ZMod ℓ)))
    (Profinite.continuousMapRingObj ℤ_[ℓ]) (Or.inl ⟨Iso.refl _⟩)).1.2.2.2.2.2.1
  refine ⟨hexample, ?_, ?_, ?_⟩
  · let f : ZMod (ℓ ^ 2) →+* ZMod ℓ := ZMod.castHom (dvd_pow_self ℓ (by omega)) _
    have hker : RingHom.ker f = Ideal.span ({(ℓ : ZMod (ℓ ^ 2))} : Set _) := by
      ext a
      simp only [RingHom.mem_ker, Ideal.mem_span_singleton]
      change f a = 0 ↔ (ℓ : ZMod (ℓ ^ 2)) ∣ a
      rw [← ZMod.natCast_zmod_val a]
      simp only [map_natCast, ZMod.natCast_eq_zero_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, by rw [hn, Nat.cast_mul]⟩
      · rintro ⟨n, hn⟩
        have hn' := congrArg f hn
        exact (ZMod.natCast_eq_zero_iff _ _).mp (by
          simpa only [map_mul, map_natCast, ZMod.natCast_self, zero_mul] using hn')
    let e := RingHom.quotientKerEquivOfSurjective
      (show Function.Surjective f from ZMod.castHom_surjective _)
    exact ⟨(Ideal.quotEquivOfEq hker.symm).trans e⟩
  · let f := scalarMulHom (ZMod (ℓ ^ 2)) (ℓ : ZMod (ℓ ^ 2))
    have hg : (CategoryTheory.SquareZeroInternal.twoTerm f).IsStrictlyGE (-1) :=
      CategoryTheory.SquareZeroInternal.twoTerm_ge f
    have hl : (CategoryTheory.SquareZeroInternal.twoTerm f).IsStrictlyLE 0 :=
      CategoryTheory.SquareZeroInternal.twoTerm_le f
    let L : CochainComplex (ModuleCat (ZMod (ℓ ^ 2))) ℤ :=
      HomologicalComplex.double f (by decide : (ComplexShape.up ℤ).Rel (-1) 0)
    have : L.IsStrictlyGE (-1) := hg
    have : L.IsStrictlyLE 0 := hl
    have hge : (DerivedCategory.Q.obj L).IsGE (-1) := inferInstance
    have hle : (DerivedCategory.Q.obj L).IsLE 0 := inferInstance
    let e := DerivedCategory.Q.mapIso (doubleConeIso f)
    exact (DerivedCategory.homologyConcentratedIn (-1) 0).prop_of_iso e ⟨hge, hle⟩
  · intro q hq
    let f := scalarMulHom (ZMod (ℓ ^ 2)) (ℓ : ZMod (ℓ ^ 2))
    let e := DerivedCategory.Q.mapIso (doubleConeIso f)
    have hc : cokernel f ≅ ModuleCat.of (ZMod (ℓ ^ 2)) (integralCriterionScalarResidue ℓ) := by
      exact ModuleCat.cokernelIsoRangeQuotient f ≪≫
        (Submodule.quotEquivOfEq _ _ (by
          ext a
          simp only [LinearMap.mem_range, Ideal.mem_span_singleton]
          change (∃ y, (ℓ : ZMod (ℓ ^ 2)) * y = a) ↔ (ℓ : ZMod (ℓ ^ 2)) ∣ a
          exact exists_congr fun y ↦ eq_comm)).toModuleIso
    rcases hq with rfl | rfl
    · have hs : f ≫ f = 0 := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        change (ℓ : ZMod (ℓ ^ 2)) * ((ℓ : ZMod (ℓ ^ 2)) * a) = 0
        rw [← mul_assoc, ← pow_two, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
      have he : (ShortComplex.mk f f hs).Exact := by
        rw [ShortComplex.moduleCat_exact_iff]
        intro a ha
        have hann := (residue_arithmetic ℓ).2 a
        obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (hann.mp ha)
        exact ⟨b, hb.symm⟩
      exact ⟨(DerivedCategory.homologyFunctor _ (-1)).mapIso e.symm ≪≫
        (DerivedCategory.homologyFunctorFactors _ (-1)).app _ ≪≫
        CategoryTheory.SquareZeroInternal.twoTerm_h₁ f ≪≫
        (kernelIsKernel f).conePointUniqueUpToIso he.isLimitImage' ≪≫
        ((cokernelIsCokernel f).coconePointUniqueUpToIso he.isColimitImage).symm ≪≫ hc⟩
    · exact ⟨(DerivedCategory.homologyFunctor _ 0).mapIso e.symm ≪≫
        (DerivedCategory.homologyFunctorFactors _ 0).app _ ≪≫
        CategoryTheory.SquareZeroInternal.twoTerm_h₀ f ≪≫ hc⟩


/-- For every finite discrete commutative coefficient ring, Dctf is thick.

Source: latest blueprint lem-integral-ctf-equals-bc, final sentence
(blueprint: lem-integral-ctf-equals-bc).

Proof plan (step 6): the finite-ring clause of
det-def-localizing-closure-ctf-equals-bc gives triangulation and closure under retracts.
Constructible bounded cohomology is triangulated by the constructible Serre property,
and retracts preserve cohomology and boundedness. Intersect with the thick finite-Tor
subcategory of det-def-sfb-constructible-tor-amplitude. -/
theorem integral_ctf_finite_ring_thick
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) X ⊓
      DerivedCategory.finiteTorAmplitude _).IsTriangulated ∧
    (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) X ⊓
      DerivedCategory.finiteTorAmplitude _).IsStableUnderRetracts := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (localizingClosure_ctf_equals_bc 2 X
    (Profinite.continuousMapRingObj ℤ_[2]) (Or.inl ⟨Iso.refl _⟩)).1
  exact h.2.2.2.2.1 A X

/-- The constant residue A_X/(ell) on an arbitrary small pro-etale scheme site.
This is a cokernel of multiplication by ell on the coefficient module itself.
The canonical ULift places the finite scalar ring in the scheme universe.
Source: latest blueprint lem-integral-ctf-equals-bc, constant-sheaf examples
(blueprint: lem-integral-ctf-equals-bc). -/
noncomputable def integralCriterionResidue (ℓ : ℕ) (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj (ULift.{u} (ZMod (ℓ ^ 2)))) X) :=
  cokernel (ℓ • (𝟙 (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousCoefficientRingObj (ULift.{u} (ZMod (ℓ ^ 2)))) X)))))

/-- The explicit constant free complex [A_X --ell--> A_X] in degrees [-1,0],
as the derived image of a mapping cone of the corresponding degree-zero map.
Source: latest blueprint lem-integral-ctf-equals-bc, constant-sheaf examples
(blueprint: lem-integral-ctf-equals-bc). -/
noncomputable def integralCriterionTwoTerm (ℓ : ℕ) (X : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj (ULift.{u} (ZMod (ℓ ^ 2)))) X)) :=
  DerivedCategory.Q.obj (CochainComplex.mappingCone
    ((CochainComplex.singleFunctor _ 0).map (ℓ • (𝟙 (𝟙_
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj
          (Profinite.continuousCoefficientRingObj (ULift.{u} (ZMod (ℓ ^ 2)))) X)))))))

namespace IntegralCriterionProof

open Opposite

private theorem proetale_bot_not_cover (X : Scheme.{u}) (U : X.ProEt)
    (hU : Nonempty U.left) : ¬ (⊥ : Sieve U) ∈ Scheme.ProEt.topology X U := by
  let F := Scheme.ProEt.forget X ⋙ Over.forget X
  have hc : CoverPreserving (Scheme.ProEt.topology X) Scheme.proetaleTopology F :=
    CoverPreserving.of_isContinuous F _ _
  have hj : Scheme.proetaleTopology.{u} ≤ Scheme.jointlySurjectiveTopology := by
    rw [Scheme.jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology]
    change Scheme.proetalePrecoverage.toGrothendieck ≤
      Scheme.jointlySurjectivePrecoverage.toPretopology.toGrothendieck
    rw [Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
    exact Precoverage.toGrothendieck_mono (le_trans inf_le_right inf_le_left)
  intro h
  have hb : (⊥ : Sieve U.left) ∈ Scheme.proetaleTopology U.left := by
    simpa only [Sieve.functorPushforward_bot, F, Functor.comp_obj,
      Scheme.ProEt.forget, MorphismProperty.Over.forget, MorphismProperty.Comma.forget,
      Over.forget_obj] using hc.cover_preserve h
  have hs := hj U.left hb
  change (⊥ : Presieve U.left) ∈ Scheme.jointlySurjectivePrecoverage U.left at hs
  rw [Precoverage.mem_comap_iff, Presieve.map_bot,
    Types.mem_jointlySurjectivePrecoverage_iff] at hs
  obtain ⟨x⟩ := hU
  obtain ⟨W, f, hf, _⟩ := hs x
  exact hf

private theorem constant_ab_injective (X : Scheme.{u}) [Nonempty X]
    (B : AddCommGrpCat.{u + 1}) :
    Function.Injective ((toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj B)).app (op (Scheme.ProEt.mk (𝟙 X)))) := by
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
      u + 1, u + 2, u + 1, u + 1, u + 1} _
  intro a b hab
  by_contra hne
  have h := Presheaf.equalizerSieve_mem (Scheme.ProEt.topology X)
    (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj B)) a b hab
  have he : Presheaf.equalizerSieve (F := (Functor.const X.ProEtᵒᵖ).obj B)
      (X := op (Scheme.ProEt.mk (𝟙 X))) a b = ⊥ := by
    ext W f
    simp [Presheaf.equalizerSieve, hne]
  rw [he] at h
  exact proetale_bot_not_cover X (Scheme.ProEt.mk (𝟙 X))
    (show Nonempty (Scheme.ProEt.mk (𝟙 X)).left from inferInstanceAs (Nonempty X)) h

private theorem residue_fp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] (n : ℕ) :
    Mod.IsFinitelyPresented Λ
      (cokernel (n • (𝟙 (𝟙_ (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ))))) := by
  let e : Mod.finiteFree Λ 1 ≅
      𝟙_ (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :=
    biproductUniqueIso _
  refine ⟨1, 1, e.hom ≫ (n • 𝟙 _) ≫ e.inv, ⟨?_⟩⟩
  exact cokernel.mapIso _ _ e.symm e.symm (by simp)

private theorem point_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (hP : Mod.IsFinitelyPresented Λ P) :
    HasFiniteConstantLocalModel Λ X (((upperStarFromPoint X).mapMod Λ).obj P) := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
  exact ⟨P, hP, ⟨(pullback_point_iso Λ (𝟙 X)).app P⟩⟩

private theorem local_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ X M) : IsConstantModelConstructible Λ X M := by
  classical
  have strat (Y : Scheme.{u})
      (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (hN : HasFiniteConstantLocalModel Λ Y N) : IsFiniteConstantStratified Λ Y N :=
    ⟨Scheme.Stratification.trivial Y, fun _ ↦
      pullback_finiteConstantLocalModel Λ (𝟙 Y) N hN⟩
  unfold IsConstantModelConstructible
  split_ifs
  · exact strat X M hM
  · intro U _
    exact strat _ _ (pullback_finiteConstantLocalModel Λ U.ι M hM)

private theorem constructible_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X) e hM

private theorem zero_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsZero M) : IsConstantModelConstructible Λ X M := by
  have : pointUpperStar.{u}.IsLeftAdjoint :=
    pointUpperStarLowerStarAdjunction.isLeftAdjoint
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have : (upperStarFromPoint X).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  let F := (upperStarFromPoint X).mapMod Λ
  have hP : Mod.IsFinitelyPresented Λ 0 :=
    ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  exact constructible_iso Λ X ((F.map_isZero (isZero_zero _)).iso hM)
    (local_constructible Λ X _ (point_model Λ X 0 hP))

private noncomputable def residue_pullback_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (n : ℕ) :
    ((upperStarFromPoint X).mapMod Λ).obj
        (cokernel (n • (𝟙 (𝟙_ (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ))))) ≅
      cokernel (n • (𝟙 (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))))) := by
  have : pointUpperStar.{u}.IsLeftAdjoint :=
    pointUpperStarLowerStarAdjunction.isLeftAdjoint
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have : (upperStarFromPoint X).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  let F := (upperStarFromPoint X).mapMod Λ
  let e : 𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ≅
      F.obj (𝟙_ (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)) :=
    Mod.isoMk (Iso.refl _) (by simp)
  exact PreservesCokernel.iso F _ ≪≫
    cokernel.mapIso _ _ e.symm e.symm (by simp only [Functor.map_nsmul, F.map_id,
      Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp, Category.comp_id])


private theorem coefficient_data (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [Nonempty X] :
    let Λ := Profinite.continuousCoefficientRingObj (ULift.{u} (ZMod (ℓ ^ 2)))
    let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
    ∃ hsq : (ℓ • (𝟙 (𝟙_ C))) ≫ (ℓ • (𝟙 (𝟙_ C))) = 0,
      (ShortComplex.mk (ℓ • (𝟙 (𝟙_ C))) (ℓ • (𝟙 (𝟙_ C))) hsq).Exact ∧
      ¬ IsZero (𝟙_ C) := by
  dsimp only
  have hp := (Fact.out : ℓ.Prime)
  have : NeZero (ℓ ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : Fact (1 < ℓ ^ 2) := ⟨by have := hp.two_le; nlinarith⟩
  let A := ULift.{u} (ZMod (ℓ ^ 2))
  let Λ := Profinite.continuousCoefficientRingObj A
  let B : Ab.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} A)
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let F := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let U : C ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
    Mod.forget (condensedRingObj Λ X)
  have := FiniteDiscreteOrdinary.canonicalAbelianMap_isIso A X
  let e : F.obj B ≅ U.obj (𝟙_ C) :=
    asIso (FiniteDiscreteOrdinary.canonicalAbelianMap A X)
  have hsqB : (ℓ • (𝟙 B)) ≫ (ℓ • (𝟙 B)) = 0 := by
    ext x
    change ℓ • (ℓ • x.down.down) = (0 : ZMod (ℓ ^ 2))
    simp only [nsmul_eq_mul]
    rw [← mul_assoc, ← pow_two, (residue_arithmetic ℓ).1, zero_mul]
  have hB : (ShortComplex.mk (ℓ • (𝟙 B)) (ℓ • (𝟙 B)) hsqB).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro x hx
    change ℓ • x = (0 : ULift.{u + 1} A) at hx
    have hx₀ : ℓ • x.down.down = (0 : ZMod (ℓ ^ 2)) :=
      congrArg (fun a ↦ a.down.down) hx
    have hx' : (ℓ : ZMod (ℓ ^ 2)) * x.down.down = 0 := by
      simpa only [nsmul_eq_mul] using hx₀
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ((residue_arithmetic ℓ).2 x.down.down |>.mp hx')
    refine ⟨ULift.up (ULift.up b), ?_⟩
    apply ULift.ext
    apply ULift.ext
    change ℓ • b = x.down.down
    simpa only [nsmul_eq_mul] using hb.symm
  have hsqU : (ℓ • (𝟙 (U.obj (𝟙_ C)))) ≫ (ℓ • (𝟙 (U.obj (𝟙_ C)))) = 0 := by
    apply (cancel_epi e.hom).1
    have h := congrArg (fun f ↦ F.map f ≫ e.hom) hsqB
    simpa only [Functor.map_comp, Functor.map_nsmul, Functor.map_id, Functor.map_zero, F.map_id B,
      Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
      Category.comp_id, zero_comp, comp_zero] using h
  have hsq : (ℓ • (𝟙 (𝟙_ C))) ≫ (ℓ • (𝟙 (𝟙_ C))) = 0 := by
    apply U.map_injective
    simpa only [Functor.map_comp, Functor.map_nsmul, U.map_id, Functor.map_zero]
      using hsqU
  refine ⟨hsq, ?_, ?_⟩
  · apply ((ShortComplex.mk _ _ hsq).exact_map_iff_of_faithful U).1
    let i : (ShortComplex.mk _ _ hsqB).map F ≅ (ShortComplex.mk _ _ hsq).map U :=
      ShortComplex.isoMk e e e
        (by
          change e.hom ≫ U.map (ℓ • 𝟙 _) = F.map (ℓ • 𝟙 _) ≫ e.hom
          simp only [Functor.map_nsmul, U.map_id, F.map_id,
            Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
            Category.comp_id])
        (by
          change e.hom ≫ U.map (ℓ • 𝟙 _) = F.map (ℓ • 𝟙 _) ≫ e.hom
          simp only [Functor.map_nsmul, U.map_id, F.map_id,
            Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
            Category.comp_id])
    exact (ShortComplex.exact_iff_of_iso i).mp (hB.map F)
  · intro hz
    have hzB := (U.map_isZero hz).of_iso e
    have hid : 𝟙 (F.obj B) = 0 := hzB.eq_of_src _ _
    let η := (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj B)).app (op (Scheme.ProEt.mk (𝟙 X)))
    have he : η (1 : ULift.{u + 1} A) = η 0 := by
      have h := congrArg (fun f : F.obj B ⟶ F.obj B ↦
        f.hom.app (op (Scheme.ProEt.mk (𝟙 X))) (η (1 : ULift.{u + 1} A))) hid
      change η (1 : ULift.{u + 1} A) = 0 at h
      simpa only [map_zero] using h
    exact (one_ne_zero : (1 : ULift.{u + 1} A) ≠ 0) (constant_ab_injective X B he)


end IntegralCriterionProof

/-- The constant square-zero examples on every separably closed point, including the
explicit free two-term complex, its cohomology and its failure under upper truncation.

Source: latest blueprint lem-integral-ctf-equals-bc, final paragraph
(blueprint: lem-integral-ctf-equals-bc).

Proof: repeat lem-sfb-constant-square-zero-tor-example in universe u, using ULift ZMod(ell²).
By the normalized finite-discrete comparison (lem-sf-finite-discrete-normalized-encoding),
the module unit is the constant sheaf with value ZMod(ell²). On it ell is square zero and
the sequence ell, ell is exact. The unit is nonzero because Spec k is nonempty, and the
constant sections over the identity pro-etale object inject. The periodic resolution
argument of that module then shows that the residue coker(ell) has no finite Tor amplitude.
The residue is the pullback from the point of the scalar module coker(ell), which is
finitely presented with one generator and one relation. So it has a finite constant local
model, and it is constructible by the trivial stratification and
new-unbounded-pullback-finite-constant-local-model. The two-term complex has the flat unit
as its terms, so DerivedCategory.torAmplitudeIn_Q_obj_of_flat gives amplitude [-1,0]. Its
cohomology is the residue in degrees -1 and 0 and zero elsewhere, so it lies in Dbc. Its
truncation at zero is the residue in degree 0, which has no finite Tor amplitude. All
assertions are transported along the double-to-cone isomorphism. -/
theorem integral_ctf_constant_counterexample (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [IsSepClosed k] :
    IsConstantModelConstructible
      (Profinite.continuousCoefficientRingObj (ULift.{u} (ZMod (ℓ ^ 2))))
      (Spec (.of k))
      (integralCriterionResidue ℓ (Spec (.of k))) ∧
    ¬ DerivedCategory.finiteTorAmplitude _
      ((DerivedCategory.singleFunctor _ 0).obj (integralCriterionResidue ℓ (Spec (.of k)))) ∧
    constantModelBoundedConstructible
      (Profinite.continuousCoefficientRingObj (ULift.{u} (ZMod (ℓ ^ 2))))
      (Spec (.of k))
      (integralCriterionTwoTerm ℓ (Spec (.of k))) ∧
    DerivedCategory.torAmplitudeIn _ (-1) 0 (integralCriterionTwoTerm ℓ (Spec (.of k))) ∧
    (∀ q : ℤ, q = -1 ∨ q = 0 → Nonempty
      ((DerivedCategory.homologyFunctor (Mod (Sheaf (Scheme.ProEt.topology
      (Spec (.of k))) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousCoefficientRingObj (ULift.{u} (ZMod (ℓ ^ 2))))
      (Spec (.of k)))) q).obj
        (integralCriterionTwoTerm ℓ (Spec (.of k))) ≅ integralCriterionResidue ℓ (Spec (.of k)))) ∧
    ¬ DerivedCategory.finiteTorAmplitude _
      ((DerivedCategory.TStructure.t.truncGE 0).obj (integralCriterionTwoTerm ℓ
      (Spec (.of k)))) := by
  classical
  let X : Scheme.{u} := Spec (.of k)
  let Λ := Profinite.continuousCoefficientRingObj (ULift.{u} (ZMod (ℓ ^ 2)))
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let f : 𝟙_ C ⟶ 𝟙_ C := ℓ • 𝟙 _
  let L := CategoryTheory.SquareZeroInternal.twoTerm f
  let K := DerivedCategory.Q.obj L
  let e : K ≅ integralCriterionTwoTerm ℓ X := DerivedCategory.Q.mapIso (doubleConeIso f)
  have : Nonempty X := inferInstanceAs (Nonempty (PrimeSpectrum k))
  obtain ⟨hsq, hex, hnz⟩ := IntegralCriterionProof.coefficient_data ℓ X
  have hnot : ¬ DerivedCategory.finiteTorAmplitude C
      ((DerivedCategory.singleFunctor C 0).obj (cokernel f)) :=
    CategoryTheory.SquareZeroInternal.not_finite_tor ℓ hsq hex
      (CategoryTheory.SquareZeroInternal.residue_nonzero ℓ hsq hnz)
  let P := cokernel (ℓ • (𝟙 (𝟙_ (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ))))
  let F := ((upperStarFromPoint X).mapMod Λ)
  let er : F.obj P ≅ cokernel f := IntegralCriterionProof.residue_pullback_iso Λ X ℓ
  have hres : IsConstantModelConstructible Λ X (cokernel f) :=
    IntegralCriterionProof.constructible_iso Λ X er
      (IntegralCriterionProof.local_constructible Λ X _
        (IntegralCriterionProof.point_model Λ X P (IntegralCriterionProof.residue_fp Λ ℓ)))
  have hg : L.IsStrictlyGE (-1) := CategoryTheory.SquareZeroInternal.twoTerm_ge f
  have hl : L.IsStrictlyLE 0 := CategoryTheory.SquareZeroInternal.twoTerm_le f
  have hcoh : DerivedCategory.homologyConcentratedIn (-1) 0 K :=
    ⟨inferInstance, inferInstance⟩
  have hhom (q : ℤ) (hq : q = -1 ∨ q = 0) :
      Nonempty ((DerivedCategory.homologyFunctor C q).obj K ≅ cokernel f) := by
    rcases hq with rfl | rfl
    · exact ⟨(DerivedCategory.homologyFunctorFactors C (-1)).app L ≪≫
        CategoryTheory.SquareZeroInternal.twoTerm_h₁ f ≪≫
        CategoryTheory.SquareZeroInternal.residue_kernel_iso ℓ hsq hex⟩
    · exact ⟨(DerivedCategory.homologyFunctorFactors C 0).app L ≪≫
        CategoryTheory.SquareZeroInternal.twoTerm_h₀ f⟩
  have hb : constantModelBoundedConstructible Λ X K := by
    refine ⟨(DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).mp
      ⟨-1, 0, hcoh⟩, ?_⟩
    intro q
    by_cases hq : q = -1 ∨ q = 0
    · obtain ⟨eh⟩ := hhom q hq
      exact IntegralCriterionProof.constructible_iso Λ X eh.symm hres
    · apply IntegralCriterionProof.zero_constructible Λ X
      by_cases hqa : q < -1
      · exact (DerivedCategory.isGE_iff K (-1)).mp hcoh.1 q hqa
      · exact (DerivedCategory.isLE_iff K 0).mp hcoh.2 q (by omega)
  have ht : DerivedCategory.torAmplitudeIn C (-1) 0 K := by
    apply DerivedCategory.torAmplitudeIn_Q_obj_of_flat L (-1) 0
    intro i
    by_cases hi : i = -1
    · subst i
      exact ObjectProperty.prop_of_iso _
        (HomologicalComplex.doubleXIso₀ f
          (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)).symm
        (ObjectProperty.flat_of_tensorIso (λ_ (𝟙_ C)))
    · by_cases hi' : i = 0
      · subst i
        exact ObjectProperty.prop_of_iso _
          (HomologicalComplex.doubleXIso₁ f
            (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) (by omega)).symm
          (ObjectProperty.flat_of_tensorIso (λ_ (𝟙_ C)))
      · exact ObjectProperty.flat_of_isZero
          (HomologicalComplex.isZero_double_X _ _ i hi hi')
  refine ⟨hres, hnot, ?_, ?_, ?_, ?_⟩
  · have := (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1
    exact (constantModelBoundedConstructible Λ X).prop_of_iso e hb
  · exact (DerivedCategory.torAmplitudeIn C (-1) 0).prop_of_iso e ht
  · intro q hq
    obtain ⟨eh⟩ := hhom q hq
    exact ⟨(DerivedCategory.homologyFunctor C q).mapIso e.symm ≪≫ eh⟩
  · intro h
    apply hnot
    exact (DerivedCategory.finiteTorAmplitude C).prop_of_iso
      (((DerivedCategory.TStructure.t.truncGE 0).mapIso e).symm ≪≫
        CategoryTheory.SquareZeroInternal.twoTerm_trunc f) h


end AlgebraicGeometry.ProEtale
