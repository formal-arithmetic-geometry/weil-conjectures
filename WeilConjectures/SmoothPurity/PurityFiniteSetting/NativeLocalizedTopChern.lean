/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Admissible.AdmissibleDivisorClass
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.CharP.Algebra
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleCondensedCoefficientFamily
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
public import WeilConjectures.AlgebraicGeometry.ProEtaleKummerLimitBoundary
public import WeilConjectures.AlgebraicGeometry.PurityRegularSection
public import WeilConjectures.AlgebraicGeometry.PurityVectorBundle.PurityVectorBundleZeroSection
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.LocalizedTopChernStatement
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenClosedTriangleAllStages
public import WeilConjectures.AlgebraicGeometry.NativeProjectiveBundle.NativeProjectiveBundleFormula
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalGeometry
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.VectorProjectiveCompletion.VectorProjectiveDehomogenization
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RankOneDivisorClassIntegral
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementComparisonIsomorphism
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenInterchangeCoherence
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.Open.OpenSectionClopen
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationCoherence
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenProjectionMate
public import WeilConjectures.AlgebraicGeometry.Proper.ProperExceptionalOpenBaseChange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicOpenUnit
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenPasting
public import WeilConjectures.AlgebraicGeometry.CompactCompositionProjection.CompositionProjectionMate
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.AlgebraicGeometry.Picard.FiniteOpenProduct.FiniteOpenProductOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.KrullDimension.Regular
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionFullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerStarFullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExchangeMono
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionFrame
import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections
import WeilConjectures.AlgebraicGeometry.Modules.DualLocalEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Localization.Ideal
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Localized top Chern classes over a purity base field, at every coefficient

Source: latest blueprint, sec-smooth-purity/sk-prop-an/thm-pur-localized-top-chern.md,
(L1)--(L4) and the final local-frame display, and its proof, paragraphs "The universal case"
and "The general case" (blueprint: thm-pur-localized-top-chern).

Coefficients: a presentation `c : PurityTransport.Coefficient P.coefficients.l` with no further
hypothesis (every finite commutative ell-primary ring, Z_ell, Q_ell, O_E, E, Qbar_ell). Where a bare
condensed ring needs admissibility, `nativeChernAdmissible P c` (D8) supplies it. The classes live
in the supported Hom model `NativeSupportedCup.H`, the twist lines are `c.line`.

Route (blueprint). Supported classes do not glue on an arbitrary T. They glue only on the total
space E of F, along its zero section. There the local cohomology vanishes below degree 2r.
* The universal case: for a vector bundle `V` over a `K`-scheme `B`, `nativeUniversalClass` is
  the unique class on `V.E` supported on the zero section whose restriction to `p⁻¹(U)`, for every
  trivialisation of `V` over an affine open `U`, is the frame class of the linear coordinates
  (`NativeUniversalSpec`, `nativeUniversalClass_existsUnique`).
* The general case: `nativeLocalizedTopChern` is the supported pullback `σ_s^* u_F` of the
  universal class of `E(F) = regularSectionBundleOver` along the section `σ_s`. The square is the
  Cartesian square defining Z(s). No gluing on T.
* The local frame formula on trivialising opens of T is a theorem
  (`nativeLocalizedTopChern_frame`, specification `NativeFrameSpec`).

Base field: everything is stated over `K : PurityBaseField P.coefficients.l` (argument right
after `P`). The case `K = P.geometricBase` connects to the iface record of this node,
`Sheaf.Paper.LocalizedTopChernStatement` (NG): `nativeZeroProjection_geometric`,
`nativeRegularSection_geometric`, and `nativeLocalizedTopChern_geometric`. The last one derives the
conclusion of the iface `localized_top_chern_statement` from the native classes at `K = k`.

## Main definitions

* `nativeFrameProduct`: the ordered frame class `∂κ(f_1) ∪ ... ∪ ∂κ(f_r)`.
* `NativeUniversalSpec`, `nativeUniversalClass`: the universal class u_F on E.
* `nativeLocalizedTopChern`: c_r(F, s) = σ_s^* u_F.
* `nativeLocalizedTopChern_frame` (final display), `_line` (L1), `_baseChange` (L2),
  `_directSum` (L3), `_forgetSupport` (L4).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry.ProEtale.CondensedRing.Admissible

/-! ### Coefficient comparisons -/

/-! ### The frame class -/

/-- The empty frame: the unit class on the empty zero locus, the unique class whose
precomposition with the unit restriction is the identity of the unit.
Source: def-pur-frame-class, empty frame (blueprint: thm-pur-localized-top-chern).
Proof: the zero locus of the empty family is all of U and its inclusion is an
isomorphism, so the unit restriction is an isomorphism (unit of the adjunction for
an isomorphism); compose its inverse with the shift-zero comparison. The target
`c.line U 0` is the tensor unit `𝟙_`, which is the degree-zero source of the unit. -/
theorem nativeFrameUnit_existsUnique (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) (U : Scheme.{u})
    (f : Fin 0 → Γ(U, ⊤)) :
    ∃! κ : NativeSupportedCup.H P.coefficients.l c (U.zeroLocusSubschemeι (Set.range f))
        (2 * ((0 : ℕ) : ℤ)) 0,
      (DerivedCategory.singleFunctor _ 0).map
          (unitRestriction (NativeSupportedCup.ring.{u} P.coefficients.l c)
            (U.zeroLocusSubschemeι (Set.range f))) ≫ κ =
        (shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).inv.app _ := by
  let i := U.zeroLocusSubschemeι (Set.range f)
  let j := Scheme.Hom.liftZeroLocusSubscheme (𝟙 U) (s := Set.range f) (by
    rintro t ⟨k, rfl⟩
    exact Fin.elim0 k)
  have hj : j ≫ i = 𝟙 U :=
    Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι _ _
  let : IsIso i := ⟨⟨j, by
    apply (cancel_mono i).mp
    simp only [Category.assoc, hj, Category.comp_id, Category.id_comp], hj⟩⟩
  let : IsIso (unitRestriction (NativeSupportedCup.ring.{u} P.coefficients.l c) i) := by
    unfold unitRestriction
    infer_instance
  let ρ := (DerivedCategory.singleFunctor _ 0).map
    (unitRestriction (NativeSupportedCup.ring.{u} P.coefficients.l c) i)
  refine ⟨inv ρ ≫ (shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).inv.app _, ?_, ?_⟩
  · exact IsIso.hom_inv_id_assoc ρ _
  · intro κ hκ
    apply (cancel_epi ρ).mp
    exact hκ.trans (IsIso.hom_inv_id_assoc ρ _).symm

/-! ### The universal case: the class u on the total space -/

/-! ### The general case: c_r(F, s) = σ_s^* u_F -/

/-! ### (L1)--(L4) -/

/-- Unfolding evaluation of the bidual section gives application to the original section.
Source: def-pur-regular-section, definition of evaluation
(blueprint: thm-pur-localized-top-chern). -/
private theorem nativeEvaluation_apply {T : Scheme.{u}} (F : T.Modules) (s : F.sections)
    (U : T.Opens) (l : (Scheme.Modules.dual F).val.obj (op U)) :
    (regularSectionEvaluation F s).val.app (op U) l =
      l.app (op (Over.mk (𝟙 U))) (s.val (op U)) := by
  change (((PresheafOfModules.bidual F.val).app (op U) (s.val (op U))).app
    (op (Over.mk (𝟙 U)))) l = _
  rw [PresheafOfModules.bidual_app_app_apply]
  change l.app (op (Over.mk (𝟙 U))) (F.val.map (𝟙 (op U)) (s.val (op U))) = _
  rw [F.val.map_id]
  rfl

/-- In a line-bundle frame, the evaluation ideal is generated by the single component.
Source: the rank-one clause of def-pur-regular-section and the affine dual-frame calculation
(blueprint: thm-pur-localized-top-chern). -/
private theorem rankOneEvaluation {T : Scheme.{u}} (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank 1] (s : F.sections) (U : T.affineOpens)
    (b : Module.Basis (Fin 1) (T.presheaf.obj (op U.1)) (F.val.obj (op U.1)))
    (a : T.presheaf.obj (op U.1)) :
    (∃ l : (Scheme.Modules.dual F).val.obj (op U.1),
      (regularSectionEvaluation F s).val.app (op U.1) l = a) ↔
    a ∈ Ideal.span {b.repr (s.val (op U.1)) 0} := by
  have : SheafOfModules.IsInvertible.{u, u, u} F :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one F).2 inferInstance
  have : Scheme.Modules.IsInvertible F := Scheme.Modules.IsInvertible.of_sheafOfModules F
  have hb (m : F.val.obj (op U.1)) : b.repr m 0 • b 0 = m := by
    simpa only [Fin.sum_univ_one] using b.sum_repr m
  have hgen : Scheme.Modules.IsFreeGenerator (M := F) (b 0) :=
    Scheme.Modules.isFreeGenerator_of_bijective_smul F U.2 ⟨by
      intro r t h
      have h' := congrArg (fun m ↦ b.repr m 0) h
      simpa using h', fun m ↦ ⟨b.repr m 0, hb m⟩⟩
  let e := hgen.overIso ≪≫ (SheafOfModules.freeUniqueIso (ULift.{u} (Fin 1))).symm
  obtain ⟨c, hc⟩ := Scheme.Modules.dual_local_evaluation_equiv T F U.1
    (ULift.{u} (Fin 1)) e U.1 (𝟙 U.1)
  constructor
  · rintro ⟨l, rfl⟩
    have he := (c l).map_smul (b.repr (s.val (op U.1)) 0) (b 0)
    rw [hb] at he
    rw [nativeEvaluation_apply, ← hc l, he]
    exact Ideal.mul_mem_right _ (Ideal.span {b.repr (s.val (op U.1)) 0})
      (Ideal.subset_span (Set.mem_singleton _))
  · intro ha
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨c.symm (q • b.coord 0), ?_⟩
    rw [nativeEvaluation_apply, ← hc, LinearEquiv.apply_symm_apply]
    exact hq

/-- A regular singleton frame gives a Cartier ideal, including away from its zero scheme.
Source: the rank-one clause of def-pur-regular-section; Stacks Tags 067M and 0AG8
(blueprint: thm-pur-localized-top-chern). -/
private theorem rankOneZeroIdeal {T Z : Scheme.{u}} [IsLocallyNoetherian T]
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank 1] (s : F.sections)
    (i : Z ⟶ T) [IsClosedImmersion i]
    (hI : ∀ (U : T.affineOpens) (a : T.presheaf.obj (op U.1)),
      a ∈ i.ker.ideal U ↔ ∃ l : (Scheme.Modules.dual F).val.obj (op U.1),
        (regularSectionEvaluation F s).val.app (op U.1) l = a)
    (hs : ∀ z : Z, ∃ (U : T.affineOpens) (hx : i z ∈ U.1)
      (b : Module.Basis (Fin 1) (T.presheaf.obj (op U.1)) (F.val.obj (op U.1))),
      RingTheory.Sequence.IsRegular (T.presheaf.stalk (i z))
        (List.ofFn (fun j : Fin 1 ↦ T.presheaf.germ U.1 (i z) hx
          (b.repr (s.val (op U.1)) j)))) : i.ker.IsInvertible := by
  classical
  apply isInvertible_ker_of_stalk_nonzerodivisor i
  intro x
  by_cases hx : x ∈ Set.range i
  · obtain ⟨z, rfl⟩ := hx
    obtain ⟨U, hxU, b, hb⟩ := hs z
    refine ⟨U, hxU, T.presheaf.germ U.1 (i z) hxU
      (b.repr (s.val (op U.1)) 0), ?_, ?_⟩
    · have he : i.ker.ideal U = Ideal.span {b.repr (s.val (op U.1)) 0} := by
        ext a
        exact (hI U a).trans (rankOneEvaluation F s U b a)
      rw [he, Ideal.map_span, Set.image_singleton]
    · have hb' : RingTheory.Sequence.IsRegular (T.presheaf.stalk (i z))
          [T.presheaf.germ U.1 (i z) hxU (b.repr (s.val (op U.1)) 0)] := by
        simpa only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one] using hb
      exact ((RingTheory.Sequence.isRegular_cons_iff _ _ _).mp hb').1
  · have hxopen : x ∈ i.openComplement := hx
    obtain ⟨U, hU, hxU, hUi⟩ := exists_isAffineOpen_mem_and_subset hxopen
    have hdis : Disjoint (U : Set T) (i.ker.support : Set T) := by
      rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
      exact Set.disjoint_left.mpr fun y hy hyi ↦ hUi hy hyi
    refine ⟨⟨U, hU⟩, hxU, 1, ?_, ?_⟩
    · rw [i.ker.ideal_eq_top_of_disjoint_support hdis, Ideal.map_top,
        Ideal.span_singleton_one]
    · intro z w h
      simpa only [one_mul] using h

/-! ### The case `K = k`: the iface record `Sheaf.Paper.LocalizedTopChernStatement` -/

end WeilConjectures.PurityFiniteSetting
