/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleCondensedCoefficientFamily
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfect
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.Topology.KrullDimension

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeModulePullbackBraiding
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationUnderivedModel
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ZetaWeil.ContractibleLisseEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectRingClassicalGenerator
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPoint.NativeCondensedPointSections

import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportAmplitude
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import WeilConjectures.Algebra.Homology.ModuleHomComplex
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.CategoryTheory.Exact.ExactDerivedAdjunctionBounds
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
import WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealization.AdmissibleScalarRealizationExactSupplement
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientSectionsLocalization
import WeilConjectures.CategoryTheory.ZetaWeil.SectionRingGlobalSections
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectScalarChangeModel
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Category.ModuleCat.Limits
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedDualizableIndependent
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackConstantModelConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.NumberTheory.Padics.IntegersLocalizationUniformizer
import WeilConjectures.CategoryTheory.Finite.FiniteMittagLeffler
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.InverseImageModuleFlat
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.Finite.FiniteProperLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.CoefficientHeartGeneralStatement
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
import Mathlib.Topology.NoetherianSpace
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.AlgebraicGeometry.StratifiedLatticeScheme
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousModuleEncodingUniverses
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeSheafBasicSupplement
import WeilConjectures.AlgebraicGeometry.LatticePairEffectiveDescent
import Mathlib.Analysis.Normed.Field.WithAbs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Topology.Defs.Filter
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Analysis.Normed.Algebra.Ultra
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import Mathlib.Order.CompletePartialOrder
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.RelativeGluing
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Representable
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.ProperBaseChange.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.AlgebraicGeometry.LatticeCosetMap
import WeilConjectures.AlgebraicGeometry.LatticePairLocalMatrix
import WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.ProetaleConstantSplitDescent
import WeilConjectures.AlgebraicGeometry.IndQuasiAffineEffectiveDescent
import WeilConjectures.AlgebraicGeometry.ProetaleAffineConstantCover
import WeilConjectures.AlgebraicGeometry.ProetaleEffectiveSheafDescent
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.SpectralEtaleLocalLattices
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.SpectralFiniteEtaleTraceLattice
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparison
import WeilConjectures.CategoryTheory.TruncationHypercohomology

/-! # Perfect cohomology at an algebraically closed point

Source: latest blueprint, sk-lem-finite, main statement and Complement, with the
six-step DAG proof repaired following Wei Yang #1412 item 13 (blueprint: sk-lem-finite).

The scalar ring is the actual ring Lambda(*). All geometric derived categories are
ordinary module-object categories over p_X^* Lambda. The point functor is the recorded
geometric-point realization, and neither a lattice nor a finite-stage presentation
is part of the input. The reduction clause uses quotient rings of Lambda(*), so it
includes precisely the uniformizer reductions under any integral scalar identification.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [local instance] DerivedCategory.braidedCategory'

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.GeometricPointFiniteness

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The two specified direct images, followed by the fixed point realization.
Source: sk-lem-finite, displayed RΓc and RΓ (blueprint: sk-lem-finite). -/
def cohomology (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} {aX : X ⟶ Spec (.of k)} (c : Compactification aX)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (compact : Bool) : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)) :=
  (CondensedGeometricPoint.fiber Λ k).obj
    (if compact then (CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).obj K
      else (CondensedRing.moduleObjectDerivedPushforward Λ aX).obj K)

/-- Perfectness of the complex and its derived dual, and invertibility of the canonical
signed double-evaluation map. The internal Hom is the ordinary-module presentation of
`def-pur-derived-internal-hom`; the bidual map transposes evaluation after symmetry.
Source: sk-lem-finite, main statement (blueprint: sk-lem-finite). -/
def PerfectDuality (P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ))) : Prop :=
  DerivedCategory.IsPerfectRingComplex P ∧
    DerivedCategory.IsPerfectRingComplex ((ihom P).obj (𝟙_ _)) ∧
    IsIso (MonoidalClosed.toIhomIhomUnit P)

/-- Bounded finitely generated cohomology over the actual scalar ring. For the field
coefficients finite generation is finite dimensionality; for integral coefficients
this is membership in D^b_fg(O_E).
Source: sk-lem-finite, Complement (blueprint: sk-lem-finite). -/
def FiniteCohomology (P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ))) : Prop :=
  DerivedCategory.TStructure.t.bounded P ∧
    ∀ i : ℤ, Module.Finite (condensedScalarRing Λ) ((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (condensedScalarRing Λ)) i).obj P)

/-- The point equivalence, perfectness and biduality of both cohomology complexes and
all geometric stalks, the sharp cohomological interval, and the integral uniform bound.
The integral clause is independent of a choice of scalar presentation: it applies to
every scalar, hence to the image of every choice of uniformizer. The same finite free
model gives this formally equivalent strengthened reduction formulation.

Source: latest blueprint sk-lem-finite, main statement and Complement.

Proof, following the six DAG steps.
1. The point equivalence `lem-sf-condensed-geometric-point-perfect-general` identifies
   Dctf(s,Lambda) with perfect scalar complexes. Apply `sk-thm-sf-ctf-stability` to aX.
   The finite compact-support case is also `sk-prop-sf-trace-perfectness`; the open part
   of an ordinary-image compactification uses `sk-cor-sf-direct-image-ctf`.
2. Exact inverse image preserves cohomological bounds and finite constant local models
   (`lem-sfb-pullback-constant-model-constructible`). Represent finite Tor objects by
   bounded flat models (`lem-sc-source-tor-amplitude-flat-model`), pull them back using
   `new-proetale-inverse-image-module-flat`, and use strong monoidality to identify units.
   Apply the point equivalence over each algebraically closed Omega. The finite-projective
   termwise dual stays finite projective (`lem-sf-finite-projective-dual`); the evaluation
   model of `lem-pod-projective-hom-evaluation-model` gives the signed bidual isomorphism.
3. For finite coefficients use the finite-coefficient etale comparison on Noetherian X,
   geometric cohomological dimension [0,2d], and `thm-sp-truncation-e2`. For compact supports
   use the fixed-compactification comparison, `lem-dg-compact-support-amplitude` and
   `lem-pur-bounded-heart-amplitude` for Rg_* j_!, deriving the two factors separately.
4. Integral perfectness first gives one bounded finite-free model; its reduction has
   one Tor interval for every n. `sk-prop-scalar-six` identifies these reductions with
   the cohomology of reduced K, compatibly with quotient transitions. Reduced K lies
   in [a-1,b], so step 3 gives the upper bound b+2d at every finite level.
5. Perfect tensor commutes with the surjective coefficient tower by
   `lem-sfb-perfect-tensor-surjective-module-limit`. Finite cohomology gives Mittag-Leffler;
   `lem-pc-derived-limit-milnor-sequence` then gives the integral upper bound. Exact
   extension by zero and the derived exact-pullback adjunction give the lower bound a.
6. For E use `sk-lem-coefficient-heart`, `sk-lem-stratified-lattice`, the constructible
   heart filtration and exact scalar comparison. For Qbar use finite-subextension
   descent `sk-thm-sfb-qlbar-two-colimit`, truncate to [a,b], and extend scalars flatly.
   Perfect field complexes have bounded finite-dimensional cohomology. Empty X gives
   zero complexes, so no finite-dimensional value of dim(empty) is required.
(blueprint: sk-lem-finite). -/
theorem geometric_point_cohomology_finiteness
    (D : WeilConjectures.FiniteFieldDatum.{v}) (coeff : D.CoefficientDatum)
    (hΛ : CondensedRing.IsAdmissibleCoefficientFor coeff (Mon.mk Λ))
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k D.p] :
    (∃ h : ∀ K : (CondensedGeometricPoint.ctf Λ k).FullSubcategory,
        CondensedGeometricPoint.perfect Λ ((CondensedGeometricPoint.fiber Λ k).obj K.obj),
      (CondensedGeometricPoint.restricted Λ k h).IsEquivalence) ∧
    ∀ (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
        [IsSeparated X.hom] (c : Compactification X.hom)
        (K : ConstantModelConstructibleFiniteTor Λ X.left),
      (∀ compact : Bool, PerfectDuality Λ (cohomology Λ k c K.obj compact) ∧
        FiniteCohomology Λ (cohomology Λ k c K.obj compact)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X.left),
        PerfectDuality Λ ((CondensedGeometricPoint.fiber Λ Ω).obj
          ((CondensedRing.moduleObjectDerivedPullback Λ x).obj K.obj))) ∧
      (∀ (a b : ℤ), K.obj.IsGE a → K.obj.IsLE b →
        ∀ (d : ℕ), topologicalKrullDim X.left ≤ (d : WithBot ℕ∞) →
          ∀ compact : Bool, (cohomology Λ k c K.obj compact).IsGE a ∧
            (cohomology Λ k c K.obj compact).IsLE (b + 2 * (d : ℤ))) ∧
      (∀ E : PadicAlgCl.FiniteIntermediateField coeff.l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj coeff.l E)) →
          ∀ π : condensedScalarRing Λ, ∃ a b : ℤ, a ≤ b ∧
            ∀ (n : ℕ), 1 ≤ n → ∀ compact : Bool,
              DerivedCategory.IsPerfectRingComplex
                ((reduction Λ π n).obj (cohomology Λ k c K.obj compact)) ∧
              DerivedCategory.torAmplitudeIn _ a b
                ((reduction Λ π n).obj (cohomology Λ k c K.obj compact))) := by
  sorry

end AlgebraicGeometry.ProEtale.GeometricPointFiniteness
