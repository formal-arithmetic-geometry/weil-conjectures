/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedLisseEvaluationModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.DimensionExtension
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.SfIntrinsicCompactSupport
import WeilConjectures.AlgebraicGeometry.CompactificationCoherence
import WeilConjectures.AlgebraicGeometry.OpenExtensionFiniteTor
import WeilConjectures.SixFunctors.CtfStabilityDirectImages
import WeilConjectures.SixFunctors.ScalarSixCtf
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.CondensedPointCoefficients
import WeilConjectures.SixFunctors.LocallyPerfectScalarModel
import WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealizationExactSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingSummand
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientDescentTwoColimit
import WeilConjectures.AlgebraicGeometry.PerfectScalarChangeModel
import WeilConjectures.Algebra.Homology.RingedSiteStrictPerfectHom
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedFiniteTorPerfect
import Mathlib.Algebra.Module.Projective
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.SixFunctors.ScalarSixDirectImage
import WeilConjectures.SixFunctors.ScalarSixCompactSupport
import Mathlib.LinearAlgebra.Contraction
import WeilConjectures.AlgebraicGeometry.ProperCompactCoincidence

/-! # Point perfectness of global sections

Source: latest blueprint, thm-pod-point-perfectness, clauses 1--3 and proper comparison
(blueprint: thm-pod-point-perfectness).

The coefficient objects are pulled-back condensed rings and all categories are ordinary,
uncompleted derived categories. RΓ and RΓc are the condensed coefficient complexes
recorded for def-weil-ordinary-compact-cohomology, complexes of modules over the scalar
ring Λ(*) = Γ Λ. No properness or smoothness is assumed except in the final, conditional
comparison clause.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- D(X,Λ), the ordinary unbounded derived category over the pulled-back condensed ring.
Source: def-sf-setting (blueprint: def-sf-setting). -/
abbrev sfCondensedDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-- The condensed finite extension field, with its canonical spectral topology.
Source: def-sf-setting (blueprint: def-sf-setting). -/
abbrev sfRationalCoefficient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.continuousCoefficientRingObj E

/-- Rational condensed coefficients are pointwise commutative.
Source: def-sf-setting (blueprint: def-sf-setting). -/
noncomputable instance sfRationalCoefficientComm (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    IsCommMonObj (sfRationalCoefficient l E) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.isCommMonObj_continuousCoefficientRingObj _

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The algebraic derived dual RHom_{Λ(*)}(C,Λ(*)) of a complex of Λ(*)-modules, where
Λ(*) = Γ Λ is the scalar ring of the coefficient complexes of
def-weil-ordinary-compact-cohomology.
Source: thm-pod-point-perfectness, dual convention, and def-pur-derived-internal-hom
(blueprint: def-weil-ordinary-compact-cohomology). -/
def cohomologyPointDual (C : DerivedCategory (ModuleCat.{u + 1} (MonObj.Γ Λ))) :=
  (ordinaryModuleDerivedInternalHom (MonObj.Γ Λ)).obj
    (op C, (DerivedCategory.singleFunctor _ 0).obj
      (ModuleCat.of (MonObj.Γ Λ) (MonObj.Γ Λ)))

/-- The four coefficient complexes RΓ, RΓc and their duals, indexed by compact support and
algebraic duality. RΓ and RΓc are the recorded condensed coefficient complexes
`condensedRingOrdinaryCoefficientComplex` and `condensedRingCompactCoefficientComplex`.
Source: def-weil-ordinary-compact-cohomology and thm-pod-point-perfectness, displayed list
(blueprint: def-weil-ordinary-compact-cohomology). -/
def condensedFourCohomology {X s : Scheme.{u}} {a : X ⟶ s} (c : Compactification a)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (compact dual : Bool) :
    DerivedCategory (ModuleCat.{u + 1} (MonObj.Γ Λ)) :=
  let C := if compact then (condensedRingCompactCoefficientComplex Λ c).obj K
    else (condensedRingOrdinaryCoefficientComplex Λ a).obj K
  if dual then cohomologyPointDual Λ C else C

set_option maxHeartbeats 800000 in
-- The canonical mate elaborates several derived adjunctions in one declaration.
set_option synthInstance.maxHeartbeats 400000 in
/-- The canonical compact-to-ordinary comparison. It is the mate under La^* ⊣ Ra_*
of the proper-pushforward counit followed by the inverse of the open-extension unit,
followed by the recorded point sections. Thus it is specified without choosing an
arbitrary map or isomorphism.
Source: def-weil-ordinary-compact-cohomology, proper comparison
(blueprint: def-weil-ordinary-compact-cohomology). -/
def condensedCompactComparison {X s : Scheme.{u}} {a : X ⟶ s}
    (c : Compactification a)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (condensedRingCompactCoefficientComplex Λ c).obj K ⟶
      (condensedRingOrdinaryCoefficientComplex Λ a).obj K :=
  let J := (openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K
  let P := (lowerStar Λ c.g).rightDerivedFunctor.obj J
  let e := eqToIso (congrArg (fun f ↦ (upperStar Λ f).leftDerivedFunctor) c.comm) ≪≫
    leftDerivedUpperStarComp Λ c.i c.g
  let ε := e.hom.app P ≫
    (upperStar Λ c.i).leftDerivedFunctor.map
      ((derivedUpperStarLowerStarAdjunction Λ c.g).counit.app J) ≫
    inv ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ c.i).unit.app K)
  (condensedRingCoefficientSections Λ s).rightDerivedFunctor.map
    ((derivedUpperStarLowerStarAdjunction Λ a).homEquiv P K ε)

variable {Λ}
  {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ']

/-- Ordinary derived scalar extension along the scalar map Γ φ : Λ(*) → Λ'(*).
Source: def-weil-ordinary-compact-cohomology and sk-def-sfb-coefficient-change,
coefficient convention (blueprint: def-weil-ordinary-compact-cohomology). -/
def cohomologyPointScalarChange (φ : Λ ⟶ Λ') [IsMonHom φ] :=
  ModuleCat.ordinaryDerivedExtendScalars (MonObj.Γ.map φ)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- Finite-level perfectness, finiteness, Tor bounds and free representatives.
Source: latest blueprint thm-pod-point-perfectness
(blueprint: thm-pod-point-perfectness).

Proof plan:
1. Base change preserves separated finite type. Choose a dense compactification, of the
same dimension. Finite direct-image bounds give [a,b+2d] for ordinary sections; exact
extension by zero and proper direct image give the same interval for compact support.
2. Direct-image stability puts both point objects in Dctf. Finite scalar local models
and split covers of the algebraically closed point give perfect scalar models; shifts,
cones and summands preserve them. Exact point sections recover these scalar models.
3. Finite-projective duals reverse the interval. Over the integral DVR the cohomology
is finitely generated; over fields it is finite dimensional. Descend algebraic-closure
objects to a finite extension using the condensed two-colimit theorem.
4. Scalar-six comparisons identify integral reductions with the finite-level images.
Finite-projective tensor-Hom gives the same comparison for duals. A single bounded
projective model and its dual give intervals independent of the positive level n.
5. For proper X₀ the base-changed structure map is proper. The canonical mate comparison
between compact and ordinary image is an isomorphism; point evaluation preserves it.
The cited DAG plan is cor-sf-direct-image-ctf-proetale, det-thm-sf-ctf-stability-direct-images,
det-prop-scalar-six-ctf, lem-weil-point-proetale-sections-exact,
lem-sfb-perfect-scalar-change-model, lem-weil-bounded-finite-tor-perfect,
sk-thm-sfb-qlbar-two-colimit and prop-weil-proper-compact-coincidence. -/
theorem condensed_point_perfectness_finite (hl : l ≠ D.p) (n : ℕ) (hn : 1 ≤ n)
    (c : Compactification (D.geometricFiber X₀).hom)
    (K : sfCondensedDerived (DerivedNakayama.quotientRing l E n) (D.geometricFiber X₀).left)
    (hK : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E n) (D.geometricFiber
        X₀).left K ∧
      DerivedCategory.finiteTorAmplitude _ K)
    (d : ℕ) (hd : topologicalKrullDim (D.geometricFiber X₀).left ≤ (d : WithBot ℕ∞)) :
    (∀ compact dual : Bool,
      DerivedCategory.IsPerfectRingComplex (condensedFourCohomology (DerivedNakayama.quotientRing l
          E n) c K compact dual) ∧
      DerivedCategory.TStructure.t.bounded (condensedFourCohomology (DerivedNakayama.quotientRing l
          E n) c K compact dual) ∧
      (∀ i : ℤ, Module.Finite (MonObj.Γ (DerivedNakayama.quotientRing l E n))
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (MonObj.Γ (DerivedNakayama.quotientRing l E n))) i).obj
            (condensedFourCohomology (DerivedNakayama.quotientRing l E n) c K compact dual)))) ∧
    ∀ a b : ℤ, DerivedCategory.torAmplitudeIn _ a b K →
      ∀ compact dual : Bool,
        DerivedCategory.torAmplitudeIn _
          (if dual then -b - 2 * (d : ℤ) else a)
          (if dual then -a else b + 2 * (d : ℤ))
          (condensedFourCohomology (DerivedNakayama.quotientRing l E n) c K compact dual) ∧
        ∃ P : CochainComplex
            (ModuleCat.{u + 1} (MonObj.Γ (DerivedNakayama.quotientRing l E n))) ℤ,
          P.IsStrictlyGE (if dual then -b - 2 * (d : ℤ) else a) ∧
          P.IsStrictlyLE (if dual then -a else b + 2 * (d : ℤ)) ∧
          (∀ i : ℤ, Module.Free (MonObj.Γ (DerivedNakayama.quotientRing l E n)) (P.X i) ∧
            Module.Finite (MonObj.Γ (DerivedNakayama.quotientRing l E n)) (P.X i)) ∧
          Nonempty ((condensedFourCohomology (DerivedNakayama.quotientRing l E n) c K compact dual)
              ≅ DerivedCategory.Q.obj P) := by
  sorry

set_option synthInstance.maxHeartbeats 400000 in
-- Integral scalar change expands the fourfold graded tensor instance.
/-- Integral perfectness and the four reduction comparisons, with a uniform amplitude.
Source: latest blueprint thm-pod-point-perfectness
(blueprint: thm-pod-point-perfectness).

Proof plan:
1. Base change preserves separated finite type. Choose a dense compactification, of the
same dimension. Finite direct-image bounds give [a,b+2d] for ordinary sections; exact
extension by zero and proper direct image give the same interval for compact support.
2. Direct-image stability puts both point objects in Dctf. Finite scalar local models
and split covers of the algebraically closed point give perfect scalar models; shifts,
cones and summands preserve them. Exact point sections recover these scalar models.
3. Finite-projective duals reverse the interval. Over the integral DVR the cohomology
is finitely generated; over fields it is finite dimensional. Descend algebraic-closure
objects to a finite extension using the condensed two-colimit theorem.
4. Scalar-six comparisons identify integral reductions with the finite-level images.
Finite-projective tensor-Hom gives the same comparison for duals. A single bounded
projective model and its dual give intervals independent of the positive level n.
5. For proper X₀ the base-changed structure map is proper. The canonical mate comparison
between compact and ordinary image is an isomorphism; point evaluation preserves it.
The cited DAG plan is cor-sf-direct-image-ctf-proetale, det-thm-sf-ctf-stability-direct-images,
det-prop-scalar-six-ctf, lem-weil-point-proetale-sections-exact,
lem-sfb-perfect-scalar-change-model, lem-weil-bounded-finite-tor-perfect,
sk-thm-sfb-qlbar-two-colimit and prop-weil-proper-compact-coincidence. -/
theorem condensed_point_perfectness_integral (hl : l ≠ D.p)
    (c : Compactification (D.geometricFiber X₀).hom)
    (K : sfCondensedDerived (DerivedNakayama.integerRing l E) (D.geometricFiber X₀).left)
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) (D.geometricFiber
        X₀).left K ∧
      DerivedCategory.finiteTorAmplitude _ K) :
    (∀ compact dual : Bool,
      DerivedCategory.IsPerfectRingComplex (condensedFourCohomology (DerivedNakayama.integerRing l
          E) c K compact dual) ∧
      DerivedCategory.TStructure.t.bounded (condensedFourCohomology (DerivedNakayama.integerRing l
          E) c K compact dual) ∧
      (∀ i : ℤ, Module.Finite (MonObj.Γ (DerivedNakayama.integerRing l E))
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (MonObj.Γ (DerivedNakayama.integerRing l E))) i).obj
            (condensedFourCohomology (DerivedNakayama.integerRing l E) c K compact dual)))) ∧
    ∃ a b : ℤ, ∀ (n : ℕ) (hn : 1 ≤ n) (compact dual : Bool),
      Nonempty ((cohomologyPointScalarChange (DerivedNakayama.reductionRing l E n)).obj
          (condensedFourCohomology (DerivedNakayama.integerRing l E) c K compact dual) ≅
        condensedFourCohomology (DerivedNakayama.quotientRing l E n) c
          ((Mod.extendScalars (coefficientMap (DerivedNakayama.reductionRing l E n)
            (D.geometricFiber X₀).left)).leftDerivedFunctor.obj K) compact dual) ∧
      DerivedCategory.IsPerfectRingComplex
        (condensedFourCohomology (DerivedNakayama.quotientRing l E n) c
          ((Mod.extendScalars (coefficientMap (DerivedNakayama.reductionRing l E n)
            (D.geometricFiber X₀).left)).leftDerivedFunctor.obj K) compact dual) ∧
      DerivedCategory.torAmplitudeIn _ (if dual then -b else a) (if dual then -a else b)
        (condensedFourCohomology (DerivedNakayama.quotientRing l E n) c
          ((Mod.extendScalars (coefficientMap (DerivedNakayama.reductionRing l E n)
            (D.geometricFiber X₀).left)).leftDerivedFunctor.obj K) compact dual) := by
  sorry

/-- Field-coefficient perfectness: bounded finite-dimensional cohomology of all four complexes.
Source: latest blueprint thm-pod-point-perfectness
(blueprint: thm-pod-point-perfectness).

Proof plan:
1. Base change preserves separated finite type. Choose a dense compactification, of the
same dimension. Finite direct-image bounds give [a,b+2d] for ordinary sections; exact
extension by zero and proper direct image give the same interval for compact support.
2. Direct-image stability puts both point objects in Dctf. Finite scalar local models
and split covers of the algebraically closed point give perfect scalar models; shifts,
cones and summands preserve them. Exact point sections recover these scalar models.
3. Finite-projective duals reverse the interval. Over the integral DVR the cohomology
is finitely generated; over fields it is finite dimensional. Descend algebraic-closure
objects to a finite extension using the condensed two-colimit theorem.
4. Scalar-six comparisons identify integral reductions with the finite-level images.
Finite-projective tensor-Hom gives the same comparison for duals. A single bounded
projective model and its dual give intervals independent of the positive level n.
5. For proper X₀ the base-changed structure map is proper. The canonical mate comparison
between compact and ordinary image is an isomorphism; point evaluation preserves it.
The cited DAG plan is cor-sf-direct-image-ctf-proetale, det-thm-sf-ctf-stability-direct-images,
det-prop-scalar-six-ctf, lem-weil-point-proetale-sections-exact,
lem-sfb-perfect-scalar-change-model, lem-weil-bounded-finite-tor-perfect,
sk-thm-sfb-qlbar-two-colimit and prop-weil-proper-compact-coincidence. -/
theorem condensed_point_perfectness_rational (hl : l ≠ D.p)
    (c : Compactification (D.geometricFiber X₀).hom)
    (K : sfCondensedDerived (sfRationalCoefficient l E) (D.geometricFiber X₀).left)
    (hK : constantModelBoundedConstructible (sfRationalCoefficient l E) (D.geometricFiber X₀).left K
        ∧
      DerivedCategory.finiteTorAmplitude _ K) :
    (∀ compact dual : Bool,
      DerivedCategory.IsPerfectRingComplex (condensedFourCohomology (sfRationalCoefficient l E) c K
          compact dual) ∧
      DerivedCategory.TStructure.t.bounded (condensedFourCohomology (sfRationalCoefficient l E) c K
          compact dual) ∧
      (∀ i : ℤ, Module.Finite (MonObj.Γ (sfRationalCoefficient l E))
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (MonObj.Γ (sfRationalCoefficient l E)))
              i).obj (condensedFourCohomology (sfRationalCoefficient l
            E) c K compact dual)))) := by
  sorry

/-- Field-coefficient perfectness: bounded finite-dimensional cohomology of all four complexes.
Source: latest blueprint thm-pod-point-perfectness
(blueprint: thm-pod-point-perfectness).

Proof plan:
1. Base change preserves separated finite type. Choose a dense compactification, of the
same dimension. Finite direct-image bounds give [a,b+2d] for ordinary sections; exact
extension by zero and proper direct image give the same interval for compact support.
2. Direct-image stability puts both point objects in Dctf. Finite scalar local models
and split covers of the algebraically closed point give perfect scalar models; shifts,
cones and summands preserve them. Exact point sections recover these scalar models.
3. Finite-projective duals reverse the interval. Over the integral DVR the cohomology
is finitely generated; over fields it is finite dimensional. Descend algebraic-closure
objects to a finite extension using the condensed two-colimit theorem.
4. Scalar-six comparisons identify integral reductions with the finite-level images.
Finite-projective tensor-Hom gives the same comparison for duals. A single bounded
projective model and its dual give intervals independent of the positive level n.
5. For proper X₀ the base-changed structure map is proper. The canonical mate comparison
between compact and ordinary image is an isomorphism; point evaluation preserves it.
The cited DAG plan is cor-sf-direct-image-ctf-proetale, det-thm-sf-ctf-stability-direct-images,
det-prop-scalar-six-ctf, lem-weil-point-proetale-sections-exact,
lem-sfb-perfect-scalar-change-model, lem-weil-bounded-finite-tor-perfect,
sk-thm-sfb-qlbar-two-colimit and prop-weil-proper-compact-coincidence. -/
theorem condensed_point_perfectness_qbar (hl : l ≠ D.p)
    (c : Compactification (D.geometricFiber X₀).hom)
    (K : sfCondensedDerived (Profinite.padicAlgClRingObj.{u} l) (D.geometricFiber X₀).left)
    (hK : constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} l) (D.geometricFiber
        X₀).left K ∧
      DerivedCategory.finiteTorAmplitude _ K) :
    (∀ compact dual : Bool,
      DerivedCategory.IsPerfectRingComplex (condensedFourCohomology (Profinite.padicAlgClRingObj.{u}
          l) c K compact dual) ∧
      DerivedCategory.TStructure.t.bounded (condensedFourCohomology (Profinite.padicAlgClRingObj.{u}
          l) c K compact dual) ∧
      (∀ i : ℤ, Module.Finite (MonObj.Γ (Profinite.padicAlgClRingObj.{u} l))
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (MonObj.Γ (Profinite.padicAlgClRingObj.{u} l))) i).obj
            (condensedFourCohomology (Profinite.padicAlgClRingObj.{u} l) c K compact dual)))) := by
  sorry

/-- The canonical compact-to-ordinary comparison identifies the proper cases.
Source: latest blueprint thm-pod-point-perfectness
(blueprint: thm-pod-point-perfectness).

Proof plan:
1. Base change preserves separated finite type. Choose a dense compactification, of the
same dimension. Finite direct-image bounds give [a,b+2d] for ordinary sections; exact
extension by zero and proper direct image give the same interval for compact support.
2. Direct-image stability puts both point objects in Dctf. Finite scalar local models
and split covers of the algebraically closed point give perfect scalar models; shifts,
cones and summands preserve them. Exact point sections recover these scalar models.
3. Finite-projective duals reverse the interval. Over the integral DVR the cohomology
is finitely generated; over fields it is finite dimensional. Descend algebraic-closure
objects to a finite extension using the condensed two-colimit theorem.
4. Scalar-six comparisons identify integral reductions with the finite-level images.
Finite-projective tensor-Hom gives the same comparison for duals. A single bounded
projective model and its dual give intervals independent of the positive level n.
5. For proper X₀ the base-changed structure map is proper. The canonical mate comparison
between compact and ordinary image is an isomorphism; point evaluation preserves it.
The cited DAG plan is cor-sf-direct-image-ctf-proetale, det-thm-sf-ctf-stability-direct-images,
det-prop-scalar-six-ctf, lem-weil-point-proetale-sections-exact,
lem-sfb-perfect-scalar-change-model, lem-weil-bounded-finite-tor-perfect,
sk-thm-sfb-qlbar-two-colimit and prop-weil-proper-compact-coincidence. -/
theorem condensed_point_perfectness_proper_finite (hl : l ≠ D.p) (n : ℕ) (hn : 1 ≤ n)
    (hproper : IsProper X₀.hom)
    (c : Compactification (D.geometricFiber X₀).hom)
    (K : sfCondensedDerived (DerivedNakayama.quotientRing l E n) (D.geometricFiber X₀).left)
    (hK : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E n) (D.geometricFiber
        X₀).left K ∧
      DerivedCategory.finiteTorAmplitude _ K) :
    IsIso (condensedCompactComparison (DerivedNakayama.quotientRing l E n) c K) := by
  sorry

/-- The canonical compact-to-ordinary comparison identifies the proper cases.
Source: latest blueprint thm-pod-point-perfectness
(blueprint: thm-pod-point-perfectness).

Proof plan:
1. Base change preserves separated finite type. Choose a dense compactification, of the
same dimension. Finite direct-image bounds give [a,b+2d] for ordinary sections; exact
extension by zero and proper direct image give the same interval for compact support.
2. Direct-image stability puts both point objects in Dctf. Finite scalar local models
and split covers of the algebraically closed point give perfect scalar models; shifts,
cones and summands preserve them. Exact point sections recover these scalar models.
3. Finite-projective duals reverse the interval. Over the integral DVR the cohomology
is finitely generated; over fields it is finite dimensional. Descend algebraic-closure
objects to a finite extension using the condensed two-colimit theorem.
4. Scalar-six comparisons identify integral reductions with the finite-level images.
Finite-projective tensor-Hom gives the same comparison for duals. A single bounded
projective model and its dual give intervals independent of the positive level n.
5. For proper X₀ the base-changed structure map is proper. The canonical mate comparison
between compact and ordinary image is an isomorphism; point evaluation preserves it.
The cited DAG plan is cor-sf-direct-image-ctf-proetale, det-thm-sf-ctf-stability-direct-images,
det-prop-scalar-six-ctf, lem-weil-point-proetale-sections-exact,
lem-sfb-perfect-scalar-change-model, lem-weil-bounded-finite-tor-perfect,
sk-thm-sfb-qlbar-two-colimit and prop-weil-proper-compact-coincidence. -/
theorem condensed_point_perfectness_proper_integral (hl : l ≠ D.p)
    (hproper : IsProper X₀.hom)
    (c : Compactification (D.geometricFiber X₀).hom)
    (K : sfCondensedDerived (DerivedNakayama.integerRing l E) (D.geometricFiber X₀).left)
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) (D.geometricFiber
        X₀).left K ∧
      DerivedCategory.finiteTorAmplitude _ K) :
    IsIso (condensedCompactComparison (DerivedNakayama.integerRing l E) c K) := by
  sorry

/-- The canonical compact-to-ordinary comparison identifies the proper cases.
Source: latest blueprint thm-pod-point-perfectness
(blueprint: thm-pod-point-perfectness).

Proof plan:
1. Base change preserves separated finite type. Choose a dense compactification, of the
same dimension. Finite direct-image bounds give [a,b+2d] for ordinary sections; exact
extension by zero and proper direct image give the same interval for compact support.
2. Direct-image stability puts both point objects in Dctf. Finite scalar local models
and split covers of the algebraically closed point give perfect scalar models; shifts,
cones and summands preserve them. Exact point sections recover these scalar models.
3. Finite-projective duals reverse the interval. Over the integral DVR the cohomology
is finitely generated; over fields it is finite dimensional. Descend algebraic-closure
objects to a finite extension using the condensed two-colimit theorem.
4. Scalar-six comparisons identify integral reductions with the finite-level images.
Finite-projective tensor-Hom gives the same comparison for duals. A single bounded
projective model and its dual give intervals independent of the positive level n.
5. For proper X₀ the base-changed structure map is proper. The canonical mate comparison
between compact and ordinary image is an isomorphism; point evaluation preserves it.
The cited DAG plan is cor-sf-direct-image-ctf-proetale, det-thm-sf-ctf-stability-direct-images,
det-prop-scalar-six-ctf, lem-weil-point-proetale-sections-exact,
lem-sfb-perfect-scalar-change-model, lem-weil-bounded-finite-tor-perfect,
sk-thm-sfb-qlbar-two-colimit and prop-weil-proper-compact-coincidence. -/
theorem condensed_point_perfectness_proper_rational (hl : l ≠ D.p)
    (hproper : IsProper X₀.hom)
    (c : Compactification (D.geometricFiber X₀).hom)
    (K : sfCondensedDerived (sfRationalCoefficient l E) (D.geometricFiber X₀).left)
    (hK : constantModelBoundedConstructible (sfRationalCoefficient l E) (D.geometricFiber X₀).left K
        ∧
      DerivedCategory.finiteTorAmplitude _ K) :
    IsIso (condensedCompactComparison (sfRationalCoefficient l E) c K) := by
  sorry

/-- The canonical compact-to-ordinary comparison identifies the proper cases.
Source: latest blueprint thm-pod-point-perfectness
(blueprint: thm-pod-point-perfectness).

Proof plan:
1. Base change preserves separated finite type. Choose a dense compactification, of the
same dimension. Finite direct-image bounds give [a,b+2d] for ordinary sections; exact
extension by zero and proper direct image give the same interval for compact support.
2. Direct-image stability puts both point objects in Dctf. Finite scalar local models
and split covers of the algebraically closed point give perfect scalar models; shifts,
cones and summands preserve them. Exact point sections recover these scalar models.
3. Finite-projective duals reverse the interval. Over the integral DVR the cohomology
is finitely generated; over fields it is finite dimensional. Descend algebraic-closure
objects to a finite extension using the condensed two-colimit theorem.
4. Scalar-six comparisons identify integral reductions with the finite-level images.
Finite-projective tensor-Hom gives the same comparison for duals. A single bounded
projective model and its dual give intervals independent of the positive level n.
5. For proper X₀ the base-changed structure map is proper. The canonical mate comparison
between compact and ordinary image is an isomorphism; point evaluation preserves it.
The cited DAG plan is cor-sf-direct-image-ctf-proetale, det-thm-sf-ctf-stability-direct-images,
det-prop-scalar-six-ctf, lem-weil-point-proetale-sections-exact,
lem-sfb-perfect-scalar-change-model, lem-weil-bounded-finite-tor-perfect,
sk-thm-sfb-qlbar-two-colimit and prop-weil-proper-compact-coincidence. -/
theorem condensed_point_perfectness_proper_qbar (hl : l ≠ D.p)
    (hproper : IsProper X₀.hom)
    (c : Compactification (D.geometricFiber X₀).hom)
    (K : sfCondensedDerived (Profinite.padicAlgClRingObj.{u} l) (D.geometricFiber X₀).left)
    (hK : constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} l) (D.geometricFiber
        X₀).left K ∧
      DerivedCategory.finiteTorAmplitude _ K) :
    IsIso (condensedCompactComparison (Profinite.padicAlgClRingObj.{u} l) c K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
