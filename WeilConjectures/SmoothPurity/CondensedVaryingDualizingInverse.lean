/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.PurityFiniteSettingComparisonHypotheses
import WeilConjectures.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import WeilConjectures.AlgebraicGeometry.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus
import WeilConjectures.AlgebraicGeometry.FiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.ExceptionalInverseImageExistence
import WeilConjectures.AlgebraicGeometry.MateOpenRestriction
import WeilConjectures.AlgebraicGeometry.SmoothTensorDuality
import WeilConjectures.SecSmoothPurity.FiniteNativeTensorComparison
import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksBlueprint
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
import WeilConjectures.AlgebraicGeometry.ProEtalePointPullbackSupplement
import WeilConjectures.Topology.ContinuousMapCondensedRingSupplement
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Monoidal.Mon
import WeilConjectures.AlgebraicGeometry.RoosIntrinsicCompletenessEquivalence
import WeilConjectures.AlgebraicGeometry.CompleteResidueLineInverse
import WeilConjectures.SixFunctors.ScalarSixExceptional
import WeilConjectures.Algebra.Homology.LineUnboundedDerivedTensor
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-! # Tensor inverse of the native smooth dualizing object

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-geometry/
def-pur-section-invariant.md, final invertibility assertion, and
sk-thm-dnc/thm-pur-cohomological-smoothness.md, invertibility clause
(blueprint: lem-pur-condensed-varying-dualizing-inverse).

All objects are ordinary derived internal modules over the pulled-back condensed ring.
The coefficient presentation allows exactly the fixed positive quotient, its integer ring,
its finite coefficient field, and the finite-subextension-valued algebraic closure.
The base-field typing facts and coefficient-unit membership are asserted, rather than assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The native exceptional image of the coefficient unit has a two-sided Dctf inverse,
without a section, pure global dimension or Tate orientation.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-geometry/
def-pur-section-invariant.md, final invertibility assertion; thm-pur-cohomological-smoothness,
invertibility clause (blueprint: lem-pur-condensed-varying-dualizing-inverse).

Proof, following the ten steps of the DAG:
1. By sbc-lem-smooth-relative-dimension-locally-constant, the fibre-dimension loci are
clopen and disjoint. Quasi-compactness gives finitely many nonempty loci, possibly none.
2. Each restricted map is smooth of pure dimension and stays separated and finite type,
by open restriction, the closed-immersion and finite-type permanence lemmas. Apply
lem-pur-finite-setting-comparison-hypotheses on these components.
3. Apply lem-pur-clopen-ringed-module-gluing and
lem-pur-finite-product-derived-tensor-calculus to the actual coefficient ring sheaf.
The internal/section tensor comparison identifies their tensors and K-flat tests.
The equivalence detects constructibility and all cohomological and Tor bounds; take
finite minima and maxima to obtain common bounds.
4. The coefficient unit has the constant rank-one local model and Tor interval [0,0].
The base field has ell-cohomological dimension zero. The right adjoint from
sk-thm-existence preserves Dctf, and det-sf-mate-open-restriction identifies its component
values with the component exceptional images of the coefficient unit.
5. At each finite quotient, thm-asd-smooth-tensor gives an etale rank-one line shifted
by twice the dimension. The counit-compatible lem-pur-finite-native-tensor-comparison
identifies this with the actual native exceptional value, including at the residue field.
6. At integral coefficients, lem-sfb-internal-integral-criterion-forward gives completeness.
Transport along the internal/section equivalence and the coefficient-ring limit isomorphism
of det-prop-sfb-qlbar-colimit-x-integral-limit. The Roos completeness equivalence identifies
this with the intrinsic completeness required by the residue-line theorem.
7. det-prop-scalar-six-exceptional identifies the residue of this same exceptional unit
with its residue-field exceptional value. Apply lem-pur-complete-residue-line-inverse:
the native integral object is a shifted pro-etale rank-one line.
8. The same scalar-six theorem for the integer-to-field and field-to-closure maps gives
the ordinary derived scalar extensions. A line is flat and K-flat in degree zero by
lem-pur-line-unbounded-derived-tensor, so these are shifted native lines as well.
9. In each case the dual line with the opposite shift gives the two evaluations, by
lem-pur-line-unbounded-derived-tensor and the internal/section tensor comparison.
Its constant rank-one local model and the opposite Tor interval give native Dctf membership.
10. Reassemble the component inverses with the finite-product equivalence. Full faithfulness
lifts both evaluation maps and their inverses, and faithfulness checks the identities.
When the source is empty this is the empty product: its unique object is both zero and
the coefficient unit, and its unique maps are the required isomorphisms. -/
theorem condensed_varying_dualizing_inverse
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (_hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hcoeff :
      Nonempty (Mon.mk Λ ≅ Mon.mk (IntegralModelsEmbedded.discreteObj
        (Padic.coefficientExtensionRing ell E n))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (g : V ⟶ B) [Smooth g.left] [IsSeparated g.left]
    [LocallyOfFiniteType g.left] [QuasiCompact g.left] :
    ∃ (hp : Fact (ringChar D.k).Prime) (hd : Fact (ringChar D.k ≠ ell))
      (hcd : BaseFieldFiniteCD ell D.k) (ha : IsLocalizingAdmissibleCoefficient ell Λ)
      (U : ConstantModelConstructibleFiniteTor Λ B.left),
      U.obj = 𝟙_ _ ∧
      ∃ P : ConstantModelConstructibleFiniteTor Λ V.left,
        Nonempty
          (((derivedTensor Λ V.left).obj
            ((@ctfExceptionalInverseImage Λ _ _ ell _ D.k _ hp hd hcd
              V B _ _ _ _ _ _ g ha).obj U).obj).obj P.obj ≅ 𝟙_ _) ∧
        Nonempty
          (((derivedTensor Λ V.left).obj P.obj).obj
            ((@ctfExceptionalInverseImage Λ _ _ ell _ D.k _ hp hd hcd
              V B _ _ _ _ _ _ g ha).obj U).obj ≅ 𝟙_ _) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
