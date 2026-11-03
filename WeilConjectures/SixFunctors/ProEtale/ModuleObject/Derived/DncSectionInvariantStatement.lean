/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionInvariant
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.ZetaWeil.PodCtfAdjunctionData.PodCtfAdjunctions
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.NormalConeMap
public import WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedDncFamily
public import WeilConjectures.SmoothPurity.PurityConventions.PurityConventions
public import WeilConjectures.AlgebraicGeometry.SectionReesNoetherianGeometry.SectionReesNoetherianGeometry
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCtfSixFunctorStability

/-!
# Condensed deformation-to-the-normal-cone section invariant

This module states the condensed interface for `sk-thm-dnc`.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`
(blueprint: sk-thm-dnc).

Main declarations: `dncSectionBaseChangeMap` constructs the native mate;
`dncCanonicalTheta` and `dncCanonicalEta` specialize it to the two fibres;
`DncNormalizedComparison` and `dncSectionInvariant_condensed_statement` give the full statement.
The theorem proof is postponed and follows the twelve proof steps in its docstring.
The fibre maps below are expressed using the derived pullback functors and the
normal-cone pullback square, so that the statement does not replace the geometric
objects by arbitrary isomorphic objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing


/-- Finite-type schemes over a field are Noetherian; used only for unit membership.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
proof step 1 (blueprint: sk-thm-dnc). -/
local instance dncBaseNoetherian {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom

section
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  (hcd : BaseFieldFiniteCD ell k) (ha : IsLocalizingAdmissibleCoefficient ell Λ)
  {B V B' V' : Over (Spec (.of k))}
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  (g : V ⟶ B) [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
  (g' : V' ⟶ B') [IsSeparated g'.left] [LocallyOfFiniteType g'.left]
  [QuasiCompact g'.left] (b : B' ⟶ B) (v : V' ⟶ V)
  (sq : IsPullback v.left g'.left g.left b.left)

end

/-- The geometric finite-field datum has prime characteristic.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
fixed purity conventions (blueprint: sk-thm-dnc). -/
local instance dncPrimeCharacteristic (D : WeilConjectures.FiniteFieldDatum.{u}) :
    Fact (ringChar D.k).Prime := by
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩

/-- Compact-support exchange with the chosen compactifications. The first factor is
proper exchange followed by inverse open exchange. The second is the uniquely normalized
dense-refinement comparison from the pulled compactification to the chosen one.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
proof step 3 (blueprint: sk-thm-dnc). -/
def dncCompactSupportExchange (K : ConstantModelConstructibleFiniteTor Λ V.left) :
    (moduleObjectDerivedPullback Λ b.left).obj
      ((ctfLowerShriek Λ ell k hcd g ha).obj K).obj ⟶
    (rightDerivedLowerShriekOfCompactification Λ (compactificationOverField g')).obj
      ((moduleObjectDerivedPullback Λ v.left).obj K.obj) := by
  let c := compactificationOverField g
  let cp := c.ofIsPullback sq
  let c' := compactificationOverField g'
  let K' : ConstantModelConstructibleFiniteTor Λ V'.left :=
    ⟨(moduleObjectDerivedPullback Λ v.left).obj K.obj,
      (condensedCtfSixFunctorStability Λ ell k hcd v ha).1 K⟩
  letI : V'.left.Over (Spec (.of k)) := ⟨V'.hom⟩
  letI : B'.left.Over (Spec (.of k)) := ⟨B'.hom⟩
  let L : (localizingClosureProEtale Λ V'.left).FullSubcategory :=
    ⟨K'.obj, (sixOperationsLocalizingAdjunction Λ ell k hcd g' ha).source_mem
      K'.obj K'.property⟩
  let bc := ((compactSupportCondensedFormalism Λ).shriekBaseChange c cp
    (pullback.fst c.g b.left) (c.isPullback_i_ofIsPullback sq)
    (c.isPullback_g_ofIsPullback sq).flip).natTrans.app K.obj
  let qc : QuasiCompact cp.i := (Compactification.quasiCompact_openImmersion_iff cp).mpr
    inferInstance
  let qc' : QuasiCompact c'.i := (Compactification.quasiCompact_openImmersion_iff c').mpr
    inferInstance
  letI : LocallyOfFiniteType (V'.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType V'.hom
    infer_instance
  letI : QuasiCompact (V'.left ↘ Spec (.of k)) := by
    change QuasiCompact V'.hom
    infer_instance
  letI : IsSeparated (V'.left ↘ Spec (.of k)) := by
    change IsSeparated V'.hom
    infer_instance
  letI : LocallyOfFiniteType (B'.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType B'.hom)
  letI : QuasiCompact (B'.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact B'.hom)
  letI : IsSeparated (B'.left ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated B'.hom)
  letI : g'.left.IsOver (Spec (.of k)) := ⟨g'.w⟩
  let φ := (compactification_coherence_cocycle Λ ell ha k g'.left).choose
  dsimp only [compactSupportCondensedFormalism, CompactSupportFormalism.shriek,
    ExchangeFormalism.shriek, detSfDerivedPullback, CondensedOpenProper.J,
    CondensedOpenProper.D, Functor.comp_obj] at bc
  exact bc ≫ (φ ⟨⟨cp, qc⟩⟩ ⟨⟨c', qc'⟩⟩).hom.app L

/-- The coefficient prime differs from the geometric base characteristic.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
fixed purity conventions (blueprint: sk-thm-dnc).
Proof: the cardinality of D.k₀ gives characteristic D.p; its injective algebra map
into the algebraic closure gives CharP D.k D.p. Hence ringChar D.k = D.p, and
hell.symm is the required inequality. Only this proposition-only typing fact is
postponed, with no chosen object or morphism. -/
theorem dncCharacteristicNe (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) (hell : ell ≠ D.p) : Fact (ringChar D.k ≠ ell) := by
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact ⟨by rw [ringChar.eq D.k D.p]; exact Ne.symm hell⟩

/-- Finite native compact-support exchange is invertible on Dctf.
Proof: transport the specified proper/open mate to the finite etale-origin formalism;
finite proper base change and exact open extension make it invertible. Transport back
and use dense-refinement normalization for the chosen compactification. The coefficient
is the single positive quotient, not an adic coefficient.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
proof steps 3 and 12 (blueprint: sk-thm-dnc). -/
theorem dncCompactSupportExchange_isIso :
    letI := dncCharacteristicNe D ell hell
    let hcd := WeilConjectures.exceptionalCurrentFieldCD ell D.k
      (Or.inr (IsAlgClosure.isAlgClosed D.k₀))
    let ha := sectionInvariant_admissible D ell hell
      (DiagonalCoefficients.bottomField ell) n hn Λ (Or.inl hcoeff)
    ∀ K : ConstantModelConstructibleFiniteTor Λ V.left,
      IsIso (dncCompactSupportExchange Λ ell D.k hcd ha g g' b v sq K) := by
  sorry

/-- The smooth dualizing base-change mate. This is the transpose, under the pulled
pair's exceptional adjunction, of inverse compact-support exchange followed by the
pullback of the original counit and the canonical pullback-unit comparison.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
proof step 3, using thm-pur-cohomological-smoothness (3) (blueprint: sk-thm-dnc). -/
def dncDualizingBaseChangeMap :
    letI := dncCharacteristicNe D ell hell
    let hcd := WeilConjectures.exceptionalCurrentFieldCD ell D.k
      (Or.inr (IsAlgClosure.isAlgClosed D.k₀))
    let ha := sectionInvariant_admissible D ell hell
      (DiagonalCoefficients.bottomField ell) n hn Λ (Or.inl hcoeff)
    let U : ConstantModelConstructibleFiniteTor Λ B.left :=
      ⟨𝟙_ _, condensedCoefficientUnit_mem Λ B.left⟩
    let U' : ConstantModelConstructibleFiniteTor Λ B'.left :=
      ⟨𝟙_ _, condensedCoefficientUnit_mem Λ B'.left⟩
    (moduleObjectDerivedPullback Λ v.left).obj
      ((ctfExceptionalInverseImage Λ ell D.k hcd g ha).obj U).obj ⟶
      ((ctfExceptionalInverseImage Λ ell D.k hcd g' ha).obj U').obj := by
  letI := dncCharacteristicNe D ell hell
  let hcd := WeilConjectures.exceptionalCurrentFieldCD ell D.k
    (Or.inr (IsAlgClosure.isAlgClosed D.k₀))
  let ha := sectionInvariant_admissible D ell hell
    (DiagonalCoefficients.bottomField ell) n hn Λ (Or.inl hcoeff)
  let U : ConstantModelConstructibleFiniteTor Λ B.left :=
    ⟨𝟙_ _, condensedCoefficientUnit_mem Λ B.left⟩
  let U' : ConstantModelConstructibleFiniteTor Λ B'.left :=
    ⟨𝟙_ _, condensedCoefficientUnit_mem Λ B'.left⟩
  let K := (ctfExceptionalInverseImage Λ ell D.k hcd g ha).obj U
  let K' : ConstantModelConstructibleFiniteTor Λ V'.left :=
    ⟨(moduleObjectDerivedPullback Λ v.left).obj K.obj,
      (condensedCtfSixFunctorStability Λ ell D.k hcd v ha).1 K⟩
  let bc := dncCompactSupportExchange Λ ell D.k hcd ha g g' b v sq K
  letI : IsIso bc := dncCompactSupportExchange_isIso D ell hell n hn Λ hcoeff
    g g' b v sq K
  let ε := (ctfExceptionalAdjunction Λ ell D.k hcd g ha).counit.app U
  let e : (ctfLowerShriek Λ ell D.k hcd g' ha).obj K' ⟶ U' :=
    ObjectProperty.homMk (inv bc ≫
      (moduleObjectDerivedPullback Λ b.left).map ε.hom ≫
      (leftDerivedUpperStarUnitIso Λ b.left).hom)
  exact ((ctfExceptionalAdjunction Λ ell D.k hcd g' ha).homEquiv K' U' e).hom

/-- Base change of a section invariant, with literal pullback composition. Its first
two factors identify `Lb* Ls*` with `Ls'* Lv*` using the equation of sections;
the last is `Ls'*` applied to the specified dualizing mate.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
proof steps 3 and 12, using sk-lem-geometry (1) (blueprint: sk-thm-dnc). -/
def dncSectionBaseChangeMap
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (s' : B' ⟶ V') [IsClosedImmersion s'.left] (hs' : s' ≫ g' = 𝟙 B')
    (w : b.left ≫ s.left = s'.left ≫ v.left) :
    (moduleObjectDerivedPullback Λ b.left).obj
      (sectionInvariant D ell hell (DiagonalCoefficients.bottomField ell)
        n hn Λ (Or.inl hcoeff) B V g s hs) ⟶
      sectionInvariant D ell hell (DiagonalCoefficients.bottomField ell)
        n hn Λ (Or.inl hcoeff) B' V' g' s' hs' := by
  letI := dncCharacteristicNe D ell hell
  let hcd := WeilConjectures.exceptionalCurrentFieldCD ell D.k
    (Or.inr (IsAlgClosure.isAlgClosed D.k₀))
  let ha := sectionInvariant_admissible D ell hell
    (DiagonalCoefficients.bottomField ell) n hn Λ (Or.inl hcoeff)
  let U : ConstantModelConstructibleFiniteTor Λ B.left :=
    ⟨𝟙_ _, condensedCoefficientUnit_mem Λ B.left⟩
  let K := ((ctfExceptionalInverseImage Λ ell D.k hcd g ha).obj U).obj
  exact ((leftDerivedUpperStarComp Λ b.left s.left).app K).inv ≫
    (eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj K) w)).hom ≫
    ((leftDerivedUpperStarComp Λ s'.left v.left).app K).hom ≫
    (moduleObjectDerivedPullback Λ s'.left).map
      (dncDualizingBaseChangeMap D ell hell n hn Λ hcoeff g g'
        (b := b) (v := v) (sq := sq))

section
variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (n : ℕ) (hn : 1 ≤ n)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
    (Padic.coefficientExtensionRing ell (DiagonalCoefficients.bottomField ell).1 n))))
  {B V B' V' : Over (Spec (.of D.k))}
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  (g : V ⟶ B) [Smooth g.left] [IsSeparated g.left]
  [LocallyOfFiniteType g.left] [QuasiCompact g.left]
  (g' : V' ⟶ B') [Smooth g'.left] [IsSeparated g'.left]
  [LocallyOfFiniteType g'.left] [QuasiCompact g'.left]
  (b : B' ⟶ B) (v : V' ⟶ V)
  (sq : IsPullback v.left g'.left g.left b.left)

end

/-- The normal-cone object used by the zero-fibre clause.
(blueprint: sk-thm-dnc).
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md. -/
noncomputable def dncNormalOver
    (D : WeilConjectures.FiniteFieldDatum.{u}) {B V : Over (Spec (.of D.k))}
    (g : V ⟶ B) (s : B ⟶ V) : Over (Spec (.of D.k)) :=
  Over.mk (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)

/-- The actual normal-cone zero section, as a morphism over the finite field.
(blueprint: sk-thm-dnc).
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md. -/
noncomputable def dncNormalSection
    (D : WeilConjectures.FiniteFieldDatum.{u}) {B V : Over (Spec (.of D.k))}
    (g : V ⟶ B) (s : B ⟶ V) (hs : s ≫ g = 𝟙 B) :
    B ⟶ dncNormalOver D g s :=
  Over.homMk (Scheme.Hom.normalConeZeroSection s.left) (by
    change Scheme.Hom.normalConeZeroSection s.left ≫
      (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom) = B.hom
    rw [← Category.assoc,
      Scheme.Hom.normalConeZeroSection_normalConeProj (congrArg (fun f => f.left) hs),
      Category.id_comp])

/-- The actual normal-cone projection, as a morphism over the finite field.
(blueprint: sk-thm-dnc).
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md. -/
noncomputable def dncNormalProjection
    (D : WeilConjectures.FiniteFieldDatum.{u}) {B V : Over (Spec (.of D.k))}
    (g : V ⟶ B) (s : B ⟶ V) : dncNormalOver D g s ⟶ B :=
  Over.homMk (Scheme.Hom.normalConeProj g.left s.left) (by rfl)

/-- The affine-line base map induced by a morphism of bases.
(blueprint: sk-thm-dnc).
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md. -/
noncomputable def dncBaseChangeMap
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {B B' : Over (Spec (.of D.k))} (b : B' ⟶ B) :
    condensedDncBase D B' ⟶ condensedDncBase D B :=
  Over.homMk (AffineSpace.map (ULift.{u} (Fin 1)) b.left) (by
    change AffineSpace.map (ULift.{u} (Fin 1)) b.left ≫
      ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom) =
      (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left) ≫ B'.hom
    rw [← Category.assoc, AffineSpace.map_over]
    rw [Category.assoc, b.w])

/-- The geometric facts used to type the condensed normal-cone invariant.

Proof: apply smooth base-change stability to the normal-cone pullback square; inherit
separatedness, finite type, and quasi-compactness from the original pair, and use the
normal-cone relative-dimension calculation.  The section equation `hs` identifies the
zero section with the pullback centre.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`.
(blueprint: sk-thm-dnc). -/
theorem dncNormalGeometryFacts
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {B V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g.left s.left) ∧
    IsSeparated (Scheme.Hom.normalConeProj g.left s.left) ∧
    LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left) ∧
    QuasiCompact (Scheme.Hom.normalConeProj g.left s.left) := by
  have hsg : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f ↦ f.left) hs
  letI := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g.left s.left hsg
  letI := SmoothOfRelativeDimension.smooth d
    (Scheme.Hom.deformationSpaceProj g.left s.left)
  have sq := Scheme.Hom.isPullback_normalConeToDeformationSpace g.left s.left
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  exact ⟨MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) sq inferInstance,
    MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance,
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance,
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance⟩

/-- The condensed module on the normal cone obtained from the actual normal-cone
projection and zero section. This is the normal-cone object in the statement.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md.
(blueprint: sk-thm-dnc). -/
noncomputable def dncNormalSectionInvariant
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
        (Padic.coefficientExtensionRing ell E n))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj Λ B.left)) := by
  letI : IsNoetherian B.left := isNoetherian_of_locallyOfFiniteType B.hom
  have hsg : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f => f.left) hs
  have hf := dncNormalGeometryFacts D d g s hs
  letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g.left s.left) := hf.1
  letI : Smooth (Scheme.Hom.normalConeProj g.left s.left) :=
    SmoothOfRelativeDimension.smooth d _
  letI : IsSeparated (Scheme.Hom.normalConeProj g.left s.left) := hf.2.1
  letI : LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left) := hf.2.2.1
  letI : QuasiCompact (Scheme.Hom.normalConeProj g.left s.left) := hf.2.2.2
  letI : IsSeparated ((dncNormalOver D g s).hom) := by
    change IsSeparated (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : LocallyOfFiniteType ((dncNormalOver D g s).hom) := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : QuasiCompact ((dncNormalOver D g s).hom) := by
    change QuasiCompact (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : IsClosedImmersion (dncNormalSection D g s hs).left := by
    change IsClosedImmersion (Scheme.Hom.normalConeZeroSection s.left)
    infer_instance
  letI : Smooth (dncNormalProjection D g s).left := by
    change Smooth (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : IsSeparated (dncNormalProjection D g s).left := by
    change IsSeparated (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : LocallyOfFiniteType (dncNormalProjection D g s).left := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : QuasiCompact (dncNormalProjection D g s).left := by
    change QuasiCompact (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  exact sectionInvariant D ell hell E n hn Λ hcoeff B (dncNormalOver D g s)
    (dncNormalProjection D g s) (dncNormalSection D g s hs) (by
      apply Over.OverMorphism.ext
      exact Scheme.Hom.normalConeZeroSection_normalConeProj hsg)


/-- Canonical base-change identification at `t=1`, built from the condensed
upper-star composition and identity isomorphisms.
(blueprint: sk-thm-dnc).
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md. -/
noncomputable def dncOneBaseIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {k : Type u} [Field k] {B : Over (Spec (.of k))}
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj Λ B.left))) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)).obj
      ((moduleObjectDerivedPullback Λ
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).obj C) ≅ C := by
  let c := (leftDerivedUpperStarComp Λ (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)
    (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).app C
  let i := (leftDerivedUpperStarId Λ B.left).app C
  exact c.symm ≪≫ eqToIso (by rw [AffineSpace.oneSection_comp_over]) ≪≫ i

/-- Canonical base-change identification at `t=0`.
(blueprint: sk-thm-dnc).
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md. -/
noncomputable def dncZeroBaseIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {k : Type u} [Field k] {B : Over (Spec (.of k))}
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj Λ B.left))) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left)).obj
      ((moduleObjectDerivedPullback Λ
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).obj C) ≅ C := by
  let c := (leftDerivedUpperStarComp Λ (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left)
    (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).app C
  let i := (leftDerivedUpperStarId Λ B.left).app C
  exact c.symm ≪≫ eqToIso (by rw [AffineSpace.zeroSection_comp_over]) ≪≫ i

/-- The canonical one-fibre composite.  Its source and target are the actual
condensed exceptional objects.  The composite is obtained by transporting the
`leftDerivedUpperStarComp` map through the Cartesian square at `i₁`, followed by
the smooth dualizing base-change mate.  Thus the data are the displayed pasted
map; only its invertibility is postponed below.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 3 (blueprint: sk-thm-dnc). -/
noncomputable def dncCanonicalThetaComposite
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)).obj
      (condensedDncFamily D B V g s ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) d hs) ⟶
      sectionInvariant D ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) B V g s hs := by
  let H := condensedDncDomain D B V g s hs
  letI := H.1
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.2.1
  let sq := Scheme.Hom.isPullback_deformationSpaceOneFibre g.left s.left
  let b : B ⟶ condensedDncBase D B := Over.homMk
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left) (by
      change AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left ≫
        ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom) = B.hom
      rw [← Category.assoc, AffineSpace.oneSection_comp_over, Category.id_comp])
  let v : V ⟶ condensedDncSource D B V g s := Over.homMk
    (Scheme.Hom.deformationSpaceOneFibre g.left s.left) (by
      change Scheme.Hom.deformationSpaceOneFibre g.left s.left ≫
        (Scheme.Hom.deformationSpaceProj g.left s.left ≫
          ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)) = V.hom
      calc
        _ = g.left ≫ ((AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left ≫
            (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)) ≫ B.hom) := by
          rw [← Category.assoc, sq.w]
          simp only [Category.assoc]
        _ = V.hom := by
          rw [AffineSpace.oneSection_comp_over, Category.id_comp, g.w])
  exact dncSectionBaseChangeMap D ell hell n hn Λ hcoeff
    (condensedDncMap D B V g s) g b v sq
    (condensedDncSection D B V g s hs) H.2.2.2.2.2.2.2.2.2.2.2 s hs
    (Scheme.Hom.comp_deformationSpaceOneFibre
      (congrArg (fun f ↦ f.left) hs)).symm

/-- The underlying one-fibre composite.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 3 (blueprint: sk-thm-dnc). -/
noncomputable def dncCanonicalThetaMap
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)).obj
      (condensedDncFamily D B V g s ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) d hs) ⟶
      sectionInvariant D ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) B V g s hs :=
  dncCanonicalThetaComposite D ell hell n hn Λ hcoeff B V d g s hs

/-- The canonical composite is invertible by the cohomological-smoothness
base-change theorem.  This is the only postponed assertion about its data.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 3 (blueprint: sk-thm-dnc).
Proof: identify the one-fibre square with the Cartesian square of the original pair.
The smooth dualizing base-change mate is an isomorphism by
thm-pur-cohomological-smoothness (3). Pull it back along the section; the remaining
factors are the pullback composition isomorphisms. Their composite is invertible. -/
theorem dncCanonicalThetaMap_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    IsIso (dncCanonicalThetaMap D ell hell n hn Λ hcoeff B V d g s hs) := by
  sorry

/-- The named canonical one-fibre isomorphism.  It is `asIso` of the pasted
map `dncCanonicalThetaMap`; the local `IsIso` proof is the postponed theorem
that the Cartesian fibre comparison is invertible. (blueprint: sk-thm-dnc).
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md. -/
noncomputable def dncCanonicalTheta
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)).obj
      (condensedDncFamily D B V g s ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) d hs) ≅
      sectionInvariant D ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) B V g s hs := by
  letI : IsIso (dncCanonicalThetaMap D ell hell n hn Λ hcoeff B V d g s hs) :=
    dncCanonicalThetaMap_isIso D ell hell n hn Λ hcoeff B V d g s hs
  exact asIso (dncCanonicalThetaMap D ell hell n hn Λ hcoeff B V d g s hs)

/-- The canonical zero-fibre composite.  It is the paste of
`leftDerivedUpperStarComp` through the Cartesian normal-cone square
`isPullback_normalConeToDeformationSpace`, followed by the smooth dualizing
base-change mate.  The displayed map uses the actual normal-cone invariant;
only its invertibility is postponed below.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 3 (blueprint: sk-thm-dnc). -/
noncomputable def dncCanonicalEtaComposite
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left)).obj
      (condensedDncFamily D B V g s ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) d hs) ⟶
      dncNormalSectionInvariant D ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) B V d g s hs := by
  letI : IsNoetherian B.left := isNoetherian_of_locallyOfFiniteType B.hom
  have hsg : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f => f.left) hs
  have hf := dncNormalGeometryFacts D d g s hs
  letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g.left s.left) := hf.1
  letI : Smooth (Scheme.Hom.normalConeProj g.left s.left) :=
    SmoothOfRelativeDimension.smooth d _
  letI : IsSeparated (Scheme.Hom.normalConeProj g.left s.left) := hf.2.1
  letI : LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left) := hf.2.2.1
  letI : QuasiCompact (Scheme.Hom.normalConeProj g.left s.left) := hf.2.2.2
  letI : IsSeparated ((dncNormalOver D g s).hom) := by
    change IsSeparated (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : LocallyOfFiniteType ((dncNormalOver D g s).hom) := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : QuasiCompact ((dncNormalOver D g s).hom) := by
    change QuasiCompact (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : IsClosedImmersion (dncNormalSection D g s hs).left := by
    change IsClosedImmersion (Scheme.Hom.normalConeZeroSection s.left)
    infer_instance
  letI : Smooth (dncNormalProjection D g s).left := by
    change Smooth (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : IsSeparated (dncNormalProjection D g s).left := by
    change IsSeparated (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : LocallyOfFiniteType (dncNormalProjection D g s).left := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : QuasiCompact (dncNormalProjection D g s).left := by
    change QuasiCompact (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  let H := condensedDncDomain D B V g s hs
  letI := H.1
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.2.1
  let sq := Scheme.Hom.isPullback_normalConeToDeformationSpace g.left s.left
  let b : B ⟶ condensedDncBase D B := Over.homMk
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left) (by
      change AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left ≫
        ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom) = B.hom
      rw [← Category.assoc, AffineSpace.zeroSection_comp_over, Category.id_comp])
  let v : dncNormalOver D g s ⟶ condensedDncSource D B V g s := Over.homMk
    s.left.ker.normalConeToDeformationSpace (by
      change s.left.ker.normalConeToDeformationSpace ≫
        (Scheme.Hom.deformationSpaceProj g.left s.left ≫
          ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)) =
        Scheme.Hom.normalConeProj g.left s.left ≫ B.hom
      calc
        _ = Scheme.Hom.normalConeProj g.left s.left ≫
            ((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left ≫
              (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)) ≫ B.hom) := by
          rw [← Category.assoc, sq.w]
          simp only [Category.assoc]
        _ = _ := by rw [AffineSpace.zeroSection_comp_over, Category.id_comp])
  exact dncSectionBaseChangeMap D ell hell n hn Λ hcoeff
    (condensedDncMap D B V g s) (dncNormalProjection D g s) b v sq
    (condensedDncSection D B V g s hs) H.2.2.2.2.2.2.2.2.2.2.2
    (dncNormalSection D g s hs) (by
      apply Over.OverMorphism.ext
      exact Scheme.Hom.normalConeZeroSection_normalConeProj hsg)
    (Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace (s := s.left)).symm

/-- The underlying zero-fibre composite.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 3 (blueprint: sk-thm-dnc). -/
noncomputable def dncCanonicalEtaMap
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left)).obj
      (condensedDncFamily D B V g s ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) d hs) ⟶
      dncNormalSectionInvariant D ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) B V d g s hs :=
  dncCanonicalEtaComposite D ell hell n hn Λ hcoeff B V d g s hs

/-- The canonical normal-cone composite is invertible by the corresponding
cohomological-smoothness theorem.  Source:
  `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 3 (blueprint: sk-thm-dnc).
Proof: the associated-graded quotient gives the Cartesian zero-fibre square
isPullback_normalConeToDeformationSpace. Apply smooth dualizing base change to
that square and pull back along its zero section. The section equation identifies
the two pullback composites, so every displayed factor is invertible. -/
theorem dncCanonicalEtaMap_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    IsIso (dncCanonicalEtaMap D ell hell n hn Λ hcoeff B V d g s hs) := by
  sorry

/-- The named canonical zero-fibre isomorphism, obtained from the pasted
`dncCanonicalEtaMap` and its postponed invertibility proof. (blueprint: sk-thm-dnc).
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md. -/
noncomputable def dncCanonicalEta
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left)).obj
      (condensedDncFamily D B V g s ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) d hs) ≅
      dncNormalSectionInvariant D ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) B V d g s hs := by
  letI : IsIso (dncCanonicalEtaMap D ell hell n hn Λ hcoeff B V d g s hs) :=
    dncCanonicalEtaMap_isIso D ell hell n hn Λ hcoeff B V d g s hs
  exact asIso (dncCanonicalEtaMap D ell hell n hn Λ hcoeff B V d g s hs)

/-- A pulled section pair over the fibre product V times_B B'.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 1 (blueprint: sk-thm-dnc). -/
structure DncPulledPair
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {B B' V : Over (Spec (.of D.k))}
    (g : V ⟶ B) (s : B ⟶ V) (b : B' ⟶ B) where
  V' : Over (Spec (.of D.k))
  g' : V' ⟶ B'
  s' : B' ⟶ V'

/-- The canonical lift of the pulled-back section through the fibre product.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 1 (blueprint: sk-thm-dnc). -/
noncomputable def dncPullbackLift
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {B B' V : Over (Spec (.of D.k))}
    (g : V ⟶ B) (s : B ⟶ V) (b : B' ⟶ B)
    (hs : s ≫ g = 𝟙 B) : B'.left ⟶ pullback g.left b.left :=
  pullback.lift (b.left ≫ s.left) (𝟙 B'.left) (by
    calc
      (b.left ≫ s.left) ≫ g.left = b.left ≫ (s.left ≫ g.left) := Category.assoc _ _ _
      _ = b.left ≫ 𝟙 B.left := congrArg (fun f => b.left ≫ f) (congrArg (fun f => f.left) hs)
      _ = 𝟙 B'.left ≫ b.left := by simp)

/-- The actual pullback pair used for arbitrary base change.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 1 (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPair
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {B B' V : Over (Spec (.of D.k))}
    (g : V ⟶ B) (s : B ⟶ V) (b : B' ⟶ B)
    (hs : s ≫ g = 𝟙 B) : DncPulledPair D g s b where
  V' := Over.mk (pullback.fst g.left b.left ≫ V.hom)
  g' := Over.homMk (pullback.snd g.left b.left) (by
    change pullback.snd g.left b.left ≫ B'.hom =
      pullback.fst g.left b.left ≫ V.hom
    rw [← g.w, ← Category.assoc, pullback.condition, Category.assoc, b.w])
  s' := Over.homMk (dncPullbackLift D g s b hs) (by
    change dncPullbackLift D g s b hs ≫
      (pullback.fst g.left b.left ≫ V.hom) = B'.hom
    rw [dncPullbackLift, ← Category.assoc, pullback.lift_fst, Category.assoc, s.w, b.w])

/-- The pulled section is a section of the pulled morphism.

Proof: expand `dncPulledPair` and `dncPullbackLift`; use `pullback.lift_snd`,
`pullback.lift_fst`, the original equation `hs`, and extensionality in `Over` to
obtain the displayed retraction.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`.
(blueprint: sk-thm-dnc). -/
theorem dncPulledPair_section_retraction
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {B B' V : Over (Spec (.of D.k))}
    (g : V ⟶ B) (s : B ⟶ V) (b : B' ⟶ B)
    (hs : s ≫ g = 𝟙 B) :
    (dncPulledPair D g s b hs).s' ≫ (dncPulledPair D g s b hs).g' = 𝟙 B' := by
  apply Over.OverMorphism.ext
  change dncPullbackLift D g s b hs ≫ pullback.snd g.left b.left = 𝟙 B'.left
  exact pullback.lift_snd _ _ _

/-- The canonical pullback pair inherits the geometric hypotheses needed by the
recorded DNC and section-invariant definitions.  The conclusion refers to the
actual `dncPulledPair`, so no arbitrary record can provide these instances.

Proof: apply smooth and closed-immersion base change to the displayed fibre
product and use `dncPulledPair_section_retraction`.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 1 (blueprint: sk-thm-dnc). -/
theorem dncPulledPairGeometryFacts
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    SmoothOfRelativeDimension d (dncPulledPair D g s b hs).g'.left ∧
    IsSeparated (dncPulledPair D g s b hs).g'.left ∧
    LocallyOfFiniteType (dncPulledPair D g s b hs).g'.left ∧
    QuasiCompact (dncPulledPair D g s b hs).g'.left ∧
    IsSeparated (dncPulledPair D g s b hs).V'.hom ∧
    LocallyOfFiniteType (dncPulledPair D g s b hs).V'.hom ∧
    QuasiCompact (dncPulledPair D g s b hs).V'.hom ∧
    IsClosedImmersion (dncPulledPair D g s b hs).s'.left := by
  change SmoothOfRelativeDimension d (pullback.snd g.left b.left) ∧
    IsSeparated (pullback.snd g.left b.left) ∧
    LocallyOfFiniteType (pullback.snd g.left b.left) ∧
    QuasiCompact (pullback.snd g.left b.left) ∧
    IsSeparated (pullback.fst g.left b.left ≫ V.hom) ∧
    LocallyOfFiniteType (pullback.fst g.left b.left ≫ V.hom) ∧
    QuasiCompact (pullback.fst g.left b.left ≫ V.hom) ∧
    IsClosedImmersion (dncPullbackLift D g s b hs)
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have hdim : SmoothOfRelativeDimension d (pullback.snd g.left b.left) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
      (IsPullback.of_hasPullback g.left b.left) inferInstance
  have w : pullback.fst g.left b.left ≫ V.hom =
      pullback.snd g.left b.left ≫ B'.hom := by
    rw [← g.w, ← Category.assoc, pullback.condition, Category.assoc, b.w]
  have hsec : IsClosedImmersion
      (dncPullbackLift D g s b hs ≫ pullback.snd g.left b.left) := by
    rw [dncPullbackLift, pullback.lift_snd]
    infer_instance
  refine ⟨hdim, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_,
    IsClosedImmersion.of_comp _ (pullback.snd g.left b.left)⟩
  all_goals rw [w]; infer_instance

/-- The actual DNC family attached to the canonical pulled pair, using its own
Rees construction and section invariant.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
def-pur-dnc-section-family (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairFamily
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    let pair := dncPulledPair D g s b hs
    let H := dncPulledPairGeometryFacts D d g s hs b
    letI := H.1
    letI := SmoothOfRelativeDimension.smooth d pair.g'.left
    letI := H.2.1
    letI := H.2.2.1
    letI := H.2.2.2.1
    letI := H.2.2.2.2.1
    letI := H.2.2.2.2.2.1
    letI := H.2.2.2.2.2.2.1
    letI := H.2.2.2.2.2.2.2
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (condensedDncBase D B').left) Ab.{u + 1})
      (condensedRingObj Λ (condensedDncBase D B').left)) := by
  let pair := dncPulledPair D g s b hs
  let hpair := dncPulledPair_section_retraction D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  exact condensedDncFamily D B' pair.V' pair.g' pair.s' ell hell
    (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
    (Or.inl hcoeff) d hpair

/-- The section invariant of the pulled pair, with the actual pulled section.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
def-pur-section-invariant (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairSectionInvariant
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B'.left) Ab.{u + 1})
      (condensedRingObj Λ B'.left)) := by
  let pair := dncPulledPair D g s b hs
  let hpair := dncPulledPair_section_retraction D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  exact sectionInvariant D ell hell
    (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
    (Or.inl hcoeff) B' pair.V' pair.g' pair.s' hpair

/-- The actual normal-cone invariant for the pulled pair.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
def-pur-normal-bundle (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairNormalInvariant
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B'.left) Ab.{u + 1})
      (condensedRingObj Λ B'.left)) := by
  let pair := dncPulledPair D g s b hs
  let hpair := dncPulledPair_section_retraction D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  exact dncNormalSectionInvariant D ell hell
    (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
    (Or.inl hcoeff) B' pair.V' d pair.g' pair.s' hpair

/-- The named one-fibre comparison of the actual pulled pair.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
def-pur-section-invariant (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairTheta
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B'.left)).obj
      (dncPulledPairFamily D ell hell n hn Λ hcoeff d g s hs b) ≅
      dncPulledPairSectionInvariant D ell hell n hn Λ hcoeff d g s hs b := by
  let pair := dncPulledPair D g s b hs
  let hpair := dncPulledPair_section_retraction D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  exact dncCanonicalTheta D ell hell n hn Λ hcoeff B' pair.V' d pair.g' pair.s' hpair

/-- The named zero-fibre comparison of the actual pulled pair.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
def-pur-section-invariant (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairEta
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B'.left)).obj
      (dncPulledPairFamily D ell hell n hn Λ hcoeff d g s hs b) ⟶
      dncPulledPairNormalInvariant D ell hell n hn Λ hcoeff d g s hs b := by
  let pair := dncPulledPair D g s b hs
  let hpair := dncPulledPair_section_retraction D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  exact dncCanonicalEtaMap D ell hell n hn Λ hcoeff B' pair.V' d pair.g' pair.s' hpair

/-- The isomorphism underlying the pulled pair's zero-fibre comparison.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
def-pur-section-invariant (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairEtaIso
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B'.left)).obj
      (dncPulledPairFamily D ell hell n hn Λ hcoeff d g s hs b) ≅
      dncPulledPairNormalInvariant D ell hell n hn Λ hcoeff d g s hs b := by
  let pair := dncPulledPair D g s b hs
  let hpair := dncPulledPair_section_retraction D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  letI : LocallyOfFiniteType pair.V'.hom := H.2.2.2.2.2.1
  letI : QuasiCompact pair.V'.hom := H.2.2.2.2.2.2.1
  letI : IsSeparated pair.V'.hom := H.2.2.2.2.1
  letI : IsIso (dncPulledPairEta D ell hell n hn Λ hcoeff d g s hs b) := by
    change IsIso (dncCanonicalEtaMap D ell hell n hn Λ hcoeff B' pair.V' d pair.g' pair.s' hpair)
    exact dncCanonicalEtaMap_isIso D ell hell n hn Λ hcoeff B' pair.V' d pair.g' pair.s' hpair
  exact asIso (dncPulledPairEta D ell hell n hn Λ hcoeff d g s hs b)

/-- The functorial associated-graded map of normal cones, induced coefficientwise
by the map of section ideals, with the same ideal-containment proof as the Rees map.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 12 (blueprint: sk-thm-dnc). -/
def dncNormalPairMap {S S' X X' : Scheme.{u}} (s : S ⟶ X) (s' : S' ⟶ X')
    [IsClosedImmersion s] [IsClosedImmersion s'] (v : X' ⟶ X) (b : S' ⟶ S)
    (w : s' ≫ v = b ≫ s) : s'.ker.normalCone ⟶ s.ker.normalCone :=
  Scheme.IdealSheafData.normalConeMap v s.ker s'.ker fun {U' U} hU ↦
    (s.ker.ideal_map_appLE_le_ideal_comap v ⟨U.1, U.2⟩ ⟨U'.1, U'.2⟩ hU).trans
      (Scheme.IdealSheafData.le_def.mp
        (Scheme.Modules.closedImmersion_conormal_functorial s' s v b w).1 ⟨U'.1, U'.2⟩)

/-- The fixed Rees and associated-graded maps form Cartesian squares and respect
the augmentation and zero sections. Proof: use the coefficientwise Rees base-change
calculation in centred smooth coordinates and pass to the quotient by t at zero;
the augmentation kills each degree-one coordinate. No map is selected by this theorem.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 12 (blueprint: sk-thm-dnc). -/
theorem dncPulledPairSquares
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
  let pair := dncPulledPair D g s b hs
  let hpair := dncPulledPair_section_retraction D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  let φ := SectionReesBaseChange.pairMap s.left pair.s'.left (pullback.fst g.left b.left) b.left (by
    change dncPullbackLift D g s b hs ≫ pullback.fst g.left b.left = _
    simp only [dncPullbackLift, pullback.lift_fst])
  let ν := dncNormalPairMap s.left pair.s'.left (pullback.fst g.left b.left) b.left (by
    change dncPullbackLift D g s b hs ≫ pullback.fst g.left b.left = _
    simp only [dncPullbackLift, pullback.lift_fst])
  IsPullback φ (Scheme.Hom.deformationSpaceProj pair.g'.left pair.s'.left)
    (Scheme.Hom.deformationSpaceProj g.left s.left) (dncBaseChangeMap D b).left ∧
  pair.s'.left.deformationSpaceSection ≫ φ =
    (dncBaseChangeMap D b).left ≫ s.left.deformationSpaceSection ∧
  IsPullback ν (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left)
    (Scheme.Hom.normalConeProj g.left s.left) b.left ∧
  Scheme.Hom.normalConeZeroSection pair.s'.left ≫ ν =
    b.left ≫ Scheme.Hom.normalConeZeroSection s.left := by
  let pair := dncPulledPair D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  have hsg : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f ↦ f.left) hs
  have w : pair.s'.left ≫ pullback.fst g.left b.left = b.left ≫ s.left :=
    pullback.lift_fst _ _ _
  let φ := SectionReesBaseChange.pairMap s.left pair.s'.left
    (pullback.fst g.left b.left) b.left w
  let ν := dncNormalPairMap s.left pair.s'.left (pullback.fst g.left b.left) b.left w
  change IsPullback φ (Scheme.Hom.deformationSpaceProj pair.g'.left pair.s'.left)
      (Scheme.Hom.deformationSpaceProj g.left s.left) (dncBaseChangeMap D b).left ∧
    pair.s'.left.deformationSpaceSection ≫ φ =
      (dncBaseChangeMap D b).left ≫ s.left.deformationSpaceSection ∧
    IsPullback ν (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left)
      (Scheme.Hom.normalConeProj g.left s.left) b.left ∧
    Scheme.Hom.normalConeZeroSection pair.s'.left ≫ ν =
      b.left ≫ Scheme.Hom.normalConeZeroSection s.left
  obtain ⟨s', hc, w', he, hp, hcompat, _, ν', hν', hpν⟩ :=
    SectionReesBaseChange.base_change d g.left s.left hsg b.left
  have he' : s' = pair.s'.left := he
  clear he
  subst s'
  have htotal : IsPullback φ
      (Scheme.Hom.deformationSpaceProj pair.g'.left pair.s'.left ≫
        (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left))
      (Scheme.Hom.deformationSpaceProj g.left s.left ≫
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)) b.left := by
    simpa only [φ, pair, dncPulledPair, Over.homMk_left,
      Scheme.Hom.deformationSpaceProj,
      Scheme.IdealSheafData.deformationSpaceProj_over',
      Scheme.IdealSheafData.deformationSpaceProj] using hp
  have hq := IsPullback.of_bot htotal hcompat.1 (AffineSpace.isPullback_map b.left)
  letI : IsClosedImmersion s.left.ker.normalConeToDeformationSpace :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g.left s.left).flip inferInstance
  have hν : ν' = ν := by
    apply (cancel_mono s.left.ker.normalConeToDeformationSpace).mp
    exact hν'.trans
      (Scheme.IdealSheafData.normalConeMap_normalConeToDeformationSpace _ _ _ _).symm
  rw [hν] at hpν
  obtain ⟨μ, _, _, hμ, _, hzero, _⟩ := hcompat.2.2.2
  have hμν : μ = ν := by
    apply (cancel_mono s.left.ker.normalConeToDeformationSpace).mp
    exact hμ.trans
      (Scheme.IdealSheafData.normalConeMap_normalConeToDeformationSpace _ _ _ _).symm
  exact ⟨hq, hcompat.2.1, hpν, hμν ▸ hzero⟩

/-- The native section-invariant base-change map for the canonical fibre-product
pair, constructed by the compact-support mate and the pullback compositor.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 12 (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledSectionMap
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    (moduleObjectDerivedPullback Λ b.left).obj (sectionInvariant D ell hell
      (DiagonalCoefficients.bottomField ell) n hn Λ (Or.inl hcoeff) B V g s hs) ⟶
      dncPulledPairSectionInvariant D ell hell n hn Λ hcoeff d g s hs b := by
  let pair := dncPulledPair D g s b hs
  let hpair := dncPulledPair_section_retraction D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  let v : pair.V' ⟶ V := Over.homMk (pullback.fst g.left b.left) rfl
  exact dncSectionBaseChangeMap D ell hell n hn Λ hcoeff g pair.g' b v
    (IsPullback.of_hasPullback g.left b.left) s hs pair.s' hpair
    (by
      change b.left ≫ s.left =
        dncPullbackLift D g s b hs ≫ pullback.fst g.left b.left
      simp only [dncPullbackLift, pullback.lift_fst])

/-- The family base-change map: use the actual coefficientwise Rees map between
the two deformations and apply native section base change to their augmented sections.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 12 (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledFamilyMap
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    (moduleObjectDerivedPullback Λ (dncBaseChangeMap D b).left).obj (condensedDncFamily D B V g s
      ell hell (DiagonalCoefficients.bottomField ell) n hn Λ (Or.inl hcoeff) d hs) ⟶
      dncPulledPairFamily D ell hell n hn Λ hcoeff d g s hs b := by
  let pair := dncPulledPair D g s b hs
  let hpair := dncPulledPair_section_retraction D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  let H := condensedDncDomain D B V g s hs
  letI := H.1
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.2.1
  let Hp := condensedDncDomain D B' pair.V' pair.g' pair.s' hpair
  letI := Hp.1
  letI := Hp.2.1
  letI := Hp.2.2.1
  letI := Hp.2.2.2.1
  letI := Hp.2.2.2.2.1
  letI := Hp.2.2.2.2.2.1
  letI := Hp.2.2.2.2.2.2.1
  letI := Hp.2.2.2.2.2.2.2.1
  letI := Hp.2.2.2.2.2.2.2.2.1
  letI := Hp.2.2.2.2.2.2.2.2.2.1
  letI := Hp.2.2.2.2.2.2.2.2.2.2.1
  let φ := SectionReesBaseChange.pairMap s.left pair.s'.left (pullback.fst g.left b.left) b.left (by
    change dncPullbackLift D g s b hs ≫ pullback.fst g.left b.left = _
    simp only [dncPullbackLift, pullback.lift_fst])
  let Q := dncPulledPairSquares D ell hell n hn Λ hcoeff d g s hs b
  let v : condensedDncSource D B' pair.V' pair.g' pair.s' ⟶
      condensedDncSource D B V g s := Over.homMk φ (by
    change φ ≫ (Scheme.Hom.deformationSpaceProj g.left s.left ≫
      (condensedDncBase D B).hom) = _
    rw [← Category.assoc, Q.1.w, Category.assoc, (dncBaseChangeMap D b).w]
    rfl)
  exact dncSectionBaseChangeMap D ell hell n hn Λ hcoeff
    (condensedDncMap D B V g s) (condensedDncMap D B' pair.V' pair.g' pair.s')
    (dncBaseChangeMap D b) v Q.1
    (condensedDncSection D B V g s hs) H.2.2.2.2.2.2.2.2.2.2.2
    (condensedDncSection D B' pair.V' pair.g' pair.s' hpair)
    Hp.2.2.2.2.2.2.2.2.2.2.2 Q.2.1.symm

/-- The normal-invariant base-change map: the associated-graded map, the normal
projection Cartesian square and the native exceptional-adjunction mate determine it.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 12 (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledNormalMap
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    (moduleObjectDerivedPullback Λ b.left).obj (dncNormalSectionInvariant D ell hell
      (DiagonalCoefficients.bottomField ell) n hn Λ (Or.inl hcoeff) B V d g s hs) ⟶
      dncPulledPairNormalInvariant D ell hell n hn Λ hcoeff d g s hs b := by
  let pair := dncPulledPair D g s b hs
  let hpair := dncPulledPair_section_retraction D g s b hs
  let H := dncPulledPairGeometryFacts D d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  letI : IsNoetherian B.left := isNoetherian_of_locallyOfFiniteType B.hom
  have hsg : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f => f.left) hs
  have hf := dncNormalGeometryFacts D d g s hs
  letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g.left s.left) := hf.1
  letI : Smooth (Scheme.Hom.normalConeProj g.left s.left) :=
    SmoothOfRelativeDimension.smooth d _
  letI : IsSeparated (Scheme.Hom.normalConeProj g.left s.left) := hf.2.1
  letI : LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left) := hf.2.2.1
  letI : QuasiCompact (Scheme.Hom.normalConeProj g.left s.left) := hf.2.2.2
  letI : IsSeparated ((dncNormalOver D g s).hom) := by
    change IsSeparated (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : LocallyOfFiniteType ((dncNormalOver D g s).hom) := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : QuasiCompact ((dncNormalOver D g s).hom) := by
    change QuasiCompact (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : IsClosedImmersion (dncNormalSection D g s hs).left := by
    change IsClosedImmersion (Scheme.Hom.normalConeZeroSection s.left)
    infer_instance
  letI : Smooth (dncNormalProjection D g s).left := by
    change Smooth (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : IsSeparated (dncNormalProjection D g s).left := by
    change IsSeparated (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : LocallyOfFiniteType (dncNormalProjection D g s).left := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : QuasiCompact (dncNormalProjection D g s).left := by
    change QuasiCompact (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : IsNoetherian B'.left := isNoetherian_of_locallyOfFiniteType B'.hom
  have hsgp : pair.s'.left ≫ pair.g'.left = 𝟙 B'.left := congrArg (fun f => f.left) hpair
  have hfp := dncNormalGeometryFacts D d pair.g' pair.s' hpair
  letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left) := hfp.1
  letI : Smooth (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left) :=
    SmoothOfRelativeDimension.smooth d _
  letI : IsSeparated (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left) := hfp.2.1
  letI : LocallyOfFiniteType (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left) := hfp.2.2.1
  letI : QuasiCompact (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left) := hfp.2.2.2
  letI : IsSeparated ((dncNormalOver D pair.g' pair.s').hom) := by
    change IsSeparated (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left ≫ B'.hom)
    infer_instance
  letI : LocallyOfFiniteType ((dncNormalOver D pair.g' pair.s').hom) := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left ≫ B'.hom)
    infer_instance
  letI : QuasiCompact ((dncNormalOver D pair.g' pair.s').hom) := by
    change QuasiCompact (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left ≫ B'.hom)
    infer_instance
  letI : IsClosedImmersion (dncNormalSection D pair.g' pair.s' hpair).left := by
    change IsClosedImmersion (Scheme.Hom.normalConeZeroSection pair.s'.left)
    infer_instance
  letI : Smooth (dncNormalProjection D pair.g' pair.s').left := by
    change Smooth (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left)
    infer_instance
  letI : IsSeparated (dncNormalProjection D pair.g' pair.s').left := by
    change IsSeparated (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left)
    infer_instance
  letI : LocallyOfFiniteType (dncNormalProjection D pair.g' pair.s').left := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left)
    infer_instance
  letI : QuasiCompact (dncNormalProjection D pair.g' pair.s').left := by
    change QuasiCompact (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left)
    infer_instance
  let ν := dncNormalPairMap s.left pair.s'.left (pullback.fst g.left b.left) b.left (by
    change dncPullbackLift D g s b hs ≫ pullback.fst g.left b.left = _
    simp only [dncPullbackLift, pullback.lift_fst])
  let Q := dncPulledPairSquares D ell hell n hn Λ hcoeff d g s hs b
  let v : dncNormalOver D pair.g' pair.s' ⟶ dncNormalOver D g s :=
    Over.homMk ν (by
      change ν ≫ (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom) = _
      rw [← Category.assoc, Q.2.2.1.w, Category.assoc, b.w]
      rfl)
  exact dncSectionBaseChangeMap D ell hell n hn Λ hcoeff
    (dncNormalProjection D g s) (dncNormalProjection D pair.g' pair.s') b v Q.2.2.1
    (dncNormalSection D g s hs) (by
      apply Over.OverMorphism.ext
      exact Scheme.Hom.normalConeZeroSection_normalConeProj hsg)
    (dncNormalSection D pair.g' pair.s' hpair) (by
      apply Over.OverMorphism.ext
      exact Scheme.Hom.normalConeZeroSection_normalConeProj hsgp) Q.2.2.2.symm

/-- Pullback along the affine-line square, from the two composition isomorphisms
and the actual equation AffineSpace.map_over.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 12 (blueprint: sk-thm-dnc). -/
noncomputable def dncLinePullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {k : Type u} [Field k] {B B' : Over (Spec (.of k))} (b : B' ⟶ B)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj Λ B.left))) :
    (moduleObjectDerivedPullback Λ (AffineSpace.map (ULift.{u} (Fin 1)) b.left)).obj
      ((moduleObjectDerivedPullback Λ
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).obj C) ≅
    (moduleObjectDerivedPullback Λ
      (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left)).obj
      ((moduleObjectDerivedPullback Λ b.left).obj C) :=
  ((leftDerivedUpperStarComp Λ (AffineSpace.map (ULift.{u} (Fin 1)) b.left)
    (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).app C).symm ≪≫
  eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj C)
    (AffineSpace.map_over (n := ULift.{u} (Fin 1)) b.left)) ≪≫
  (leftDerivedUpperStarComp Λ
    (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left) b.left).app C

/-- The pulled pair has its own normalized comparison, its uniqueness and its own
zero-fibre formula. The two final equations compare these maps to pullbacks of
the original maps via the fixed, geometrically constructed section comparisons.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 12 (blueprint: sk-thm-dnc). -/
structure DncPulledNormalizedComparison
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p) (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    {B B' V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B)
    (kappa : condensedDncFamily D B V g s ell hell
      (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
      (Or.inl hcoeff) d hs ≅
      (moduleObjectDerivedPullback Λ
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).obj
        (sectionInvariant D ell hell
          (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
          (Or.inl hcoeff) B V g s hs))
    (zero_map : sectionInvariant D ell hell
      (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
      (Or.inl hcoeff) B V g s hs ≅
      dncNormalSectionInvariant D ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) B V d g s hs) where
  kappa' : dncPulledPairFamily D ell hell n hn Λ hcoeff d g s hs b ≅
    (moduleObjectDerivedPullback Λ
      (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left)).obj (dncPulledPairSectionInvariant D
        ell hell n hn Λ hcoeff d g s hs b)
  normalized' :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B'.left)).mapIso kappa' ≪≫
      dncOneBaseIso Λ (dncPulledPairSectionInvariant D ell hell n hn Λ hcoeff d g s hs b) =
      dncPulledPairTheta D ell hell n hn Λ hcoeff d g s hs b
  unique' : ∀ κ' : dncPulledPairFamily D ell hell n hn Λ hcoeff d g s hs b ≅
      (moduleObjectDerivedPullback Λ
        (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left)).obj (dncPulledPairSectionInvariant D
          ell hell n hn Λ hcoeff d g s hs b),
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B'.left)).mapIso κ' ≪≫
        dncOneBaseIso Λ (dncPulledPairSectionInvariant D ell hell n hn Λ hcoeff d g s hs b) =
        dncPulledPairTheta D ell hell n hn Λ hcoeff d g s hs b → κ' = kappa'
  zero_map' : dncPulledPairSectionInvariant D ell hell n hn Λ hcoeff d g s hs b ≅
    dncPulledPairNormalInvariant D ell hell n hn Λ hcoeff d g s hs b
  zero_formula' : zero_map' = (dncZeroBaseIso Λ (dncPulledPairSectionInvariant D ell hell n hn Λ
    hcoeff d g s hs b)).symm ≪≫
    ((moduleObjectDerivedPullback Λ
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B'.left)).mapIso kappa').symm ≪≫
    dncPulledPairEtaIso D ell hell n hn Λ hcoeff d g s hs b
  family_base_change_isIso :
    IsIso (dncPulledFamilyMap D ell hell n hn Λ hcoeff d g s hs b)
  section_base_change_isIso :
    IsIso (dncPulledSectionMap D ell hell n hn Λ hcoeff d g s hs b)
  normal_base_change_isIso :
    IsIso (dncPulledNormalMap D ell hell n hn Λ hcoeff d g s hs b)
  kappa_base_change :
    dncPulledFamilyMap D ell hell n hn Λ hcoeff d g s hs b ≫ kappa'.hom =
    (moduleObjectDerivedPullback Λ (dncBaseChangeMap D b).left).map kappa.hom ≫
      (dncLinePullbackIso Λ b (sectionInvariant D ell hell
        (DiagonalCoefficients.bottomField ell) n hn Λ (Or.inl hcoeff) B V g s hs)).hom ≫
      (moduleObjectDerivedPullback Λ
        (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left)).map
        (dncPulledSectionMap D ell hell n hn Λ hcoeff d g s hs b)
  zero_base_change :
    dncPulledSectionMap D ell hell n hn Λ hcoeff d g s hs b ≫ zero_map'.hom =
    (moduleObjectDerivedPullback Λ b.left).map zero_map.hom ≫
      dncPulledNormalMap D ell hell n hn Λ hcoeff d g s hs b

/-- A native coefficient-module sheaf is a finite locally constant line if its
underlying additive sheaf is that of a locally constant sheaf with regular rank-one
models over the fixed ring `Z/ell^n`. For this finite quotient, every additive map
is automatically linear: multiplication by a scalar is integer multiplication.
The underlying-sheaf isomorphism below ties the locally constant sheaf to `M`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 7 (blueprint: sk-thm-dnc). -/
noncomputable def dncLisseRankOneModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ell n : ℕ) (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  let A := ZMod (ell ^ n)
  ∃ L : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
            (CommRingCat.of (ULift.{u + 1, 0} A)))),
    IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses X A
      (fun P ↦ Nonempty (P ≅ ModuleCat.of (ULift.{u + 1, 0} A)
        (ULift.{u + 1, 0} A))) L ∧
    Nonempty ((Mod.forget (condensedRingObj Λ X)).obj M ≅
      (SheafOfModules.toSheaf _).obj L)

/-- The full condensed interface for the DNC section invariant. The fibre maps
are named canonical declarations, the zero-fibre object is the actual
normal-cone invariant, and base change uses the actual pulled pair.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc). -/
structure DncNormalizedComparison
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) where
  regular : WeilConjectures.PurityConventions.IsRegularOfPureCodimension s.left d
  family_pic : (constantModelBoundedConstructible Λ (condensedDncBase D B).left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _)
      (condensedDncFamily D B V g s ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) d hs)
  section_pic : (constantModelBoundedConstructible Λ B.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _)
      (sectionInvariant D ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) B V g s hs)
  kappa : condensedDncFamily D B V g s ell hell
      (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
      (Or.inl hcoeff) d hs ≅
    (moduleObjectDerivedPullback Λ
      (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).obj
      (sectionInvariant D ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) B V g s hs)
  kappa_normalized :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)).mapIso kappa ≪≫
      dncOneBaseIso Λ (sectionInvariant D ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) B V g s hs) =
      dncCanonicalTheta D ell hell n hn Λ hcoeff B V d g s hs
  kappa_unique : ∀ (κ' : condensedDncFamily D B V g s ell hell
      (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
      (Or.inl hcoeff) d hs ≅
    (moduleObjectDerivedPullback Λ
      (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).obj
      (sectionInvariant D ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) B V g s hs)),
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)).mapIso κ' ≪≫
      dncOneBaseIso Λ (sectionInvariant D ell hell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
        (Or.inl hcoeff) B V g s hs) =
      dncCanonicalTheta D ell hell n hn Λ hcoeff B V d g s hs → κ' = kappa
  zero_map : sectionInvariant D ell hell
      (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
      (Or.inl hcoeff) B V g s hs ≅
    dncNormalSectionInvariant D ell hell
      (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
      (Or.inl hcoeff) B V d g s hs
  zero_map_formula : zero_map =
    (dncZeroBaseIso Λ (sectionInvariant D ell hell
      (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
      (Or.inl hcoeff) B V g s hs)).symm ≪≫
      ((moduleObjectDerivedPullback Λ
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left)).mapIso kappa).symm ≪≫
      dncCanonicalEta D ell hell n hn Λ hcoeff B V d g s hs
  deformation_relative_dimension : SmoothOfRelativeDimension d
    (Scheme.Hom.deformationSpaceProj g.left s.left)
  one_geometry : IsPullback (Scheme.Hom.deformationSpaceOneFibre g.left s.left)
    g.left (Scheme.Hom.deformationSpaceProj g.left s.left)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)
  normal_geometry : IsPullback
    (Scheme.Hom.ker s.left).normalConeToDeformationSpace
    (Scheme.Hom.normalConeProj g.left s.left)
    (Scheme.Hom.deformationSpaceProj g.left s.left)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left)
  normal_section_projection :
    dncNormalSection D g s hs ≫ dncNormalProjection D g s = 𝟙 B
  M_F : Mod (Sheaf (Scheme.ProEt.topology (condensedDncBase D B).left) Ab.{u + 1})
    (condensedRingObj Λ (condensedDncBase D B).left)
  M_C : Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
    (condensedRingObj Λ B.left)
  F_shift : condensedDncFamily D B V g s ell hell
      (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
      (Or.inl hcoeff) d hs ≅
    (CategoryTheory.shiftFunctor _ (2 * (d : ℤ))).obj
      ((DerivedCategory.singleFunctor _ 0).obj M_F)
  C_shift : sectionInvariant D ell hell
      (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell) n hn Λ
      (Or.inl hcoeff) B V g s hs ≅
    (CategoryTheory.shiftFunctor _ (2 * (d : ℤ))).obj
      ((DerivedCategory.singleFunctor _ 0).obj M_C)
  M_F_rank_one : dncLisseRankOneModel Λ ell n (condensedDncBase D B).left M_F
  M_C_rank_one : dncLisseRankOneModel Λ ell n B.left M_C
  etale_local : ∀ (B' : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    (b : B' ⟶ B) [Etale b.left],
    DncPulledNormalizedComparison D ell hell n hn Λ hcoeff
      (B := B) (B' := B') (V := V) d g s hs b kappa zero_map
  arbitrary_base_change : ∀ (B' : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    (b : B' ⟶ B),
    DncPulledNormalizedComparison D ell hell n hn Λ hcoeff
      (B := B) (B' := B') (V := V) d g s hs b kappa zero_map

/-- Full statement of `sk-thm-dnc`.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
with the twelve-step proof sk-thm-dnc/sk-thm-dnc.proof.md (blueprint: sk-thm-dnc).

Proof (postponed, following the node step by step):
1. Since $k$ is a field, $S$ and $V$ are Noetherian by
[lem-weil-pbc-finite-type-over-noetherian]. The morphism $g$ is separated: $V\times_SV\to
V\times_kV$ is the base change of the closed diagonal of $S$ over $k$, hence a closed immersion
and a monomorphism by [lem-weil-pbc-proper-fp-permanence](b), and the diagonal of $V$ over $S$
is the base change of the closed diagonal of $V$ over $k$ along it, hence closed by the same
clause. Thus the pair $(g,s)$ satisfies the hypotheses of
[lem-trf-section-rees-noetherian-geometry]. Its deformation $D_sV$ is the blowup minus the
strict transform of the statement, because both are glued from the same affine charts
$\operatorname{Spec}R[t,I/t]$ of [def-pur-dnc-section-family]. That lemma gives: $D_sV$ is
Noetherian, $\widetilde g$ is smooth, separated, of finite type and of pure relative dimension
$d$, $\widetilde s$ is closed, $\widetilde g$ and $\pi$ are compactifiable, and there are the
two fibre identifications and the punctured trivialization. The projection $\mathbf A^1_S\to S$
is separated of finite type. By [lem-weil-pbc-proper-fp-permanence](d),(e), finite type and
separatedness compose (over Noetherian schemes finite type is finite presentation). Hence
$D_sV$, $N_s$ and $\mathbf A^1_S$ are separated finite-type $k$-schemes, and $\widetilde
g,\widetilde s,\pi,z,a,i_0,i_1$ are separated finite-type morphisms between them. So every
exceptional inverse image below is in the domain of [def-weil-exceptional-inverse-image].

2. Before invoking the normal bundle, the centred étale-coordinate lemma gives affine charts
with Cartesian zero fibre and a regular sequence of d coordinates, including the empty sequence
for d=0. Its associated-graded conclusion identifies the actual normal cone with the rank-d
vector bundle used by [def-pur-normal-bundle].

3. The actual blowup-minus-strict-transform and its augmented section are the objects of
[def-pur-dnc-section-family]. The fibre and base-change identifications, the equation x_i=t u_i,
and the closedness of the deformed section are supplied by [sk-lem-geometry] together with the
separated-section conclusion in [lem-trf-section-rees-noetherian-geometry]. Put
$\theta:Li_1^*F\simeq C$ and $\eta:Li_0^*F\simeq Lz^*\omega_\pi$ for the two fibre
identifications of [sk-lem-geometry](1); they are used in Steps 8-12.

4. Take the Zariski cover $\{S_i=\operatorname{Spec}R\}$ and the centred affine charts of Step
2: $P=R[X_1,\ldots,X_d]\to T$ étale with $I=(X_1,\ldots,X_d)T$ the section ideal and $T/I=R$.
Flatness of $T$ over $P$ and [lem-weil-pbc-flat-tensor-exact] identify each $I^m/I^{m+1}$ with
the corresponding polynomial quotient tensored with $T$. By
[lem-trf-section-rees-noetherian-geometry], the open of the deformation over
$\operatorname{Spec}T$ has algebra $T[t,I/t]\cong T\otimes_{R[X]}R[t,u_1,\ldots,u_d]$ with
$X_j\mapsto t u_j$. Its map to $\operatorname{Spec}R[t,u_1,\ldots,u_d]=\mathbf A^d_{\mathbf
A^1_{S_i}}$, the standard deformation chart, is the base change of the étale map
$\operatorname{Spec}T\to\operatorname{Spec}P$, hence étale by
[lem-weil-pbc-etale-scheme-base-change]. The augmentation sends every $u_j$ to $0$ and $T$ to
$T/I=R$, with $t$ unchanged, so this chart contains the whole deformed section over $S_i$. By
[lem-trf-section-rees-base-change-etale], the deformation of the base-changed pair over $S_i$ is
the base change of $D_sV$, compatibly with sections, fibres and these chart algebras.

5. Write $a_i:\mathbf A^1_{S_i}\to S_i$, and $F_i$, $C_i$ for the restrictions of $F$ to
$\mathbf A^1_{S_i}$ and of $C$ to $S_i$. By [lem-pur-co-smooth-etale-locality], every étale map
$e$ is cohomologically smooth with $\omega_e\simeq\Lambda$. A standard affine-space projection
$p$ is cohomologically smooth, since clauses (1)-(3) of [thm-pur-cohomological-smoothness] are
the three conditions of [def-pur-co-smoothness]. Thus [lem-pur-co-smooth-composition] gives
$\omega_{pe}\simeq Le^*\omega_p$, for the source chart $U_i\to\mathbf A^d_{S_i}\to S_i$ and for
the deformation chart of Step 4 over $\mathbf A^1_{S_i}$. The same formula for the open chart
inclusions, through which the sections factor, computes $C_i$ and $F_i$ from these charts. The
projections are trivial rank-$d$ vector bundles. So [cor-pur-vector-bundle-purity] at
$K=\Lambda$, pulled back along the zero sections as in the standard pair of
[sk-lem-geometry](4), gives isomorphisms $\alpha_i:F_i\simeq\Lambda_{\mathbf A^1_{S_i}}(d)[2d]$
and $\beta_i:C_i\simeq\Lambda_{S_i}(d)[2d]$. Its base-change compatibility identifies
$La_i^*\Lambda_{S_i}(d)[2d]$ with $\Lambda_{\mathbf A^1_{S_i}}(d)[2d]$. Arbitrary base change of
dualizing objects, [thm-pur-cohomological-smoothness](3), identifies all restrictions used here.
These are comparisons on neighbourhoods of the sections, not an assertion that the whole source
is affine space.

6. Affine principal restrictions of the source and deformation charts preserve the Rees algebra
and all exceptional maps. The finite-type, separated, Noetherian and compactifiability
conditions for these chart maps follow from the cited permanence statements, so every comparison
in the preceding step is defined in the stated category.

7. The finite-coefficient assertion of [prop-weil-twist-preserves] says that $\Lambda(d)$ is a
finite locally constant rank-one sheaf. Thus the local models in Step 5 are sheaves in the
common degree $r=-2d$. Apply [lem-pur-concentrated-complex-shift](2) to $F$ on the surjective
etale cover $\coprod_i\mathbf A^1_{S_i}\to\mathbf A^1_S$, and to $C$ on $\coprod_i S_i\to S$.
This lemma does not require the disjoint union to be of finite type. It gives concentration in
degree $-2d$ and finite local constancy of $M_F=\mathcal H^{-2d}F$ and $M_C=\mathcal H^{-2d}C$.
They have rank one, as checked on the cover in Step 5. Part (1) of the same lemma gives $F\simeq
M_F[2d]$ and $C\simeq M_C[2d]$. Constant-coefficient inverse image is exact and is computed
termwise by [def-weil-derived-pullback-tensor-hom], so these identifications also hold after
every pullback below. By [lem-weil-pbc-derived-single-fully-faithful], removing the common shift
identifies morphisms between these objects with ordinary module-sheaf morphisms, preserving
equality and composition. Consequently the gluing below is gluing of morphisms of fixed sheaves.

8. Using the twist-pullback comparison of Step 5, set
$\lambda_i=(La_i^*\beta_i)^{-1}\circ\alpha_i:F_i\simeq La_i^*C_i$. Let $\theta_i:Li_1^*F_i\simeq
C_i$ be Step 3's fibre identification, put $h_i=(Li_1^*\lambda_i)\circ\theta_i^{-1}$, and define
$\kappa_i=La_i^*(h_i^{-1})\circ\lambda_i$. Then $Li_1^*\kappa_i=h_i^{-1}\circ
h_i\circ\theta_i=\theta_i$ since $a_i i_1=\operatorname{id}$. Every factor is invertible. This
normalizes the comparison on every component, without choosing a scalar or a trivialization of
$C_i$.

9. Let $j:\mathbf G_{m,S}\hookrightarrow\mathbf A^1_S$. The punctured product of
[lem-pur-dnc-section-geometry](3) gives $\kappa^\circ:j^*F\simeq j^*La^*C$. At $t=1$ it is
$\theta$, because the product and fibre identifications are those of the same pair $(V,s)$. On
$\mathbf G_{m,S_i}$, the maps $j^*\kappa_i$ and $\kappa^\circ$ agree at $1$ by Step 8. By Step 7
they are maps of finite locally constant sheaves with a common shift. The second assertion of
[lem-pur-lisse-uniqueness] makes them equal on $\mathbf G_{m,S_i}$. On an overlap $S_{ij}$ the
two normalized local comparisons therefore agree on its punctured line. The first assertion of
[lem-pur-lisse-uniqueness] makes them agree on all of $\mathbf A^1_{S_{ij}}$. This is exactly
the punctured-comparison and rigidity argument in the unit; it does not use descent of arbitrary
local systems along the affine line.

10. For the etale cover of the base, its base-changed affine-line cover is a cover in the small
pro-etale site [def-weil-pbc-proetale-site]. By
[lem-weil-proetale-weakly-etale-localization](1)-(3), the module sheaves on these cover members,
with their constant coefficient rings, are precisely restrictions to the localized sites. Regard
the maps of Step 9 as module-sheaf morphisms using Step 7. On the pro-etale covering $\{\mathbf
A^1_{S_i}\to\mathbf A^1_S\}$, [lem-pur-sheaf-hom-cover-gluing] glues them uniquely; it also
glues their inverses since inverse maps agree wherever the original maps agree. The two
composites are the identity, by the uniqueness part of that same sheaf-gluing statement applied
to the local identities. Restore the common shift using
[lem-weil-pbc-derived-single-fully-faithful] to obtain an isomorphism $\kappa:F\simeq La^*C$,
with $Li_1^*\kappa=\theta$. For any other normalized isomorphism, compare it with $\kappa$ on
the punctured line: [lem-pur-lisse-uniqueness], second assertion, makes them equal there, and
the first assertion makes them equal on the whole line. Thus the isomorphism is unique and
independent of the charts and of $\alpha_i,\beta_i$.

11. Pull back $\kappa$ along $i_0$. With the isomorphism $\eta$ from Step 3 and
$Li_0^*La^*C\simeq C$, this gives $q=(Li_0^*\kappa)\circ\eta^{-1}:Lz^*\omega_\pi\simeq C$.
Define the asserted map to be $q^{-1}$. Its direction is therefore $Ls^*\omega_g\to
Lz^*\omega_\pi$, as required. In the standard coordinates, $F$ is $La^*C$ by the standard-pair
assertion of [lem-pur-dnc-section-geometry](4), and the identity is normalized at $1$. Step 10
forces $\kappa$ to be that identity, so the fibre map is also the identity on the standard
section invariant.

12. Let $b:S'\to S$ be any $k$-morphism with $S'$ separated finite type, and let $\bar b:\mathbf
A^1_{S'}\to\mathbf A^1_S$ be its base change. By [lem-pur-dnc-section-geometry](5) the
pulled-back actual deformation, section and normal bundle are those of the pulled-back pair; by
[thm-pur-cohomological-smoothness](3) its two dualizing objects are the pullbacks of the
original ones. Constant-coefficient pullback is a functor computed termwise by
[def-weil-derived-pullback-tensor-hom], so $L\bar b^*\kappa$ is an isomorphism $F'\to La'^*C'$
whose restriction at $1$ is the pulled-back fibre identification $\theta'$. Step 10 over $S'$
says there is only one such normalized map. Hence $L\bar b^*\kappa=\kappa'$. Pulling this
equality back along $i'_0$ and inverting shows that the fibre isomorphisms also agree. The same
argument applies to etale localization. The geometry and dualizing statements used here allow
arbitrary base change, so no flatness hypothesis on $b$ is introduced.
-/
theorem dncSectionInvariant_condensed_statement
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell
        (AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomField ell).1 n))))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    WeilConjectures.PurityConventions.IsRegularOfPureCodimension s.left d ∧
    Nonempty (DncNormalizedComparison D ell hell n hn Λ hcoeff B V d g s hs) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
