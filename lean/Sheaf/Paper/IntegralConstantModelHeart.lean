/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.EssentiallySmall
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.DerivedNakayamaFirstReduction
import Sheaf.Paper.IntegralHeartLocalModel
import Sheaf.Paper.IntegralModels

/-!
# The integral constant-model constructible category and its heart

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-integral-heart/
sk-lem-int-integral-heart-triangulated.md, assertions 1--2
(blueprint: det-lem-int-integral-heart-triangulated).

Coefficients are pulled-back condensed continuous functions into the valuation ring,
and the derived category is the ordinary unbounded category of internal modules.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The condensed valuation ring for an arbitrary finite extension, using its canonical
spectral norm. A finite extension of the small field of p-adic numbers is small by
`Module.Finite.small`. Its `Shrink` is used only to fit the existing continuous-function
API; `Shrink.algEquiv` identifies it with the given extension. Thus no coefficient
embedding or equality of universes is assumed. Source: blueprint integral-heart setting
and def-weil-l-adic-coefficient-extension
(blueprint: det-lem-int-integral-heart-triangulated). -/
noncomputable abbrev integralHeartCoefficientRingObj
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI : Small.{0} E := Module.Finite.small (Padic ℓ) E
  letI : FiniteDimensional (Padic ℓ) (Shrink.{0} E) :=
    (Shrink.algEquiv (Padic ℓ) E).symm.toLinearEquiv.finiteDimensional
  letI := spectralNorm.normedField (Padic ℓ) (Shrink.{0} E)
  Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers ℓ (Shrink.{0} E))

/-- The integral bounded constructible category is full triangulated, bounded and stable
under both standard truncations. The degree-zero single functor identifies its heart
with the full abelian category of constructible module sheaves, which is closed under
ambient kernels, cokernels and extensions and is essentially small.
Source: blueprint main-20261015, integral-heart-triangulated, assertions 1--2
(blueprint: det-lem-int-integral-heart-triangulated).

Proof (the nine steps of the DAG node):
1. The coefficient DVR has finite residue field (lem-weil-l-adic-extension-integers-dvr).
The scheme is Noetherian by pqf-lem-locnoeth-lft and quasi-compactness of its finite-type
structure morphism. The actual integral-model equivalence sk-lem-integral-models(2)
identifies bounded constructibility with derived completeness and bounded constructible
etale-origin residue reduction. The zero object satisfies both conditions.
2. Completeness is stable under all shifts (det-pe-derived-nakayama-first-reduction).
Derived reduction is exact (lem-pur-derived-change-of-rings). The finite-coefficient
triangulation and origin results (lem-weil-proetale-dbc-triangulated and
lem-weil-pbc-finite-ring-constructible-derived-origin) give shift stability of the reduction;
apply the integral-model equivalence again.
3. For a distinguished triangle with constructible outside vertices, rotate it to use
cone closure of completeness. Exact reduction gives a finite-coefficient triangle, whose
middle vertex is bounded constructible and has etale origin by the same two results.
The integral-model equivalence gives the middle vertex. This is precisely
ObjectProperty.IsTriangulated, and the ambient full-subcategory inclusion is exact.
4. Boundedness is part of sk-def-sfb-constructible. Both standard truncations preserve
constructibility by det-lem-int-integral-heart-local-model(3). In degree zero, the
cohomological definition says exactly that the single module is constructible. Conversely,
lem-sf-derived-concentrated-single identifies every degree-zero complex with its H^0
placed in degree zero; lem-weil-pbc-derived-single-fully-faithful identifies all morphisms.
5. The cone of C to C' has H^-1 equal to its ambient kernel and H^0 equal to its ambient
cokernel, by lem-sf-derived-homology-long-exact. Its cohomology is constructible by
local-model(2), giving closure under the actual ambient kernels and cokernels.
6. Zero and finite sums are constructible (use the cone of the zero map C[-1] to C').
Fullness inherits addition and the ambient kernel/cokernel universal properties. The
ambient coimage-image comparison is invertible with inverse in the full subcategory,
so it is abelian. A module short exact sequence gives the distinguished triangle of
lem-weil-pbc-complex-ses-triangle; outside-vertex closure proves extension closure.
7. On a fixed stratum, finite scalar presentations form a set of finite matrices.
Covers and overlap isomorphisms on the fixed small site also form sets. The sheaf
axiom glues equal local data into a unique global isomorphism. Retain realizable data;
this gives a set of representatives of finite constant local models on that stratum.
8. For a stratification a_s and chosen models F_s, the adjunction units and their local
identifications define C to the finite product of a_s* F_s. Pulling back each component
has left inverse given by the counit and the inverse model identification, by the
triangle identity. Exact pullback and cartesian coefficients reduce its kernel to zero
on all strata. lem-weil-pbc-noetherian-stratum-detection kills the global kernel.
9. Stratifications and tuples of models form sets. Subobjects of each fixed product
are sectionwise subsheaves, specified by a subset of its sections on each site object.
They form a set and contain representatives of all constructible sheaves, proving
essential smallness in the chosen universe, including the empty scheme. -/
theorem integralConstantModelHeart
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ p)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    ObjectProperty.IsClosedUnderIsomorphisms
      (constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsTriangulated
      (constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    (∀ K, constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X K →
      DerivedCategory.TStructure.t.bounded K ∧ ∀ n : ℤ,
        constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X
          ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
        constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X
          ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
    (ObjectProperty.ι (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
      DerivedCategory.singleFunctor _ 0).Full ∧
    (ObjectProperty.ι (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
      DerivedCategory.singleFunctor _ 0).Faithful ∧
    (∀ K, (ObjectProperty.ι
        (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
        DerivedCategory.singleFunctor _ 0).essImage K ↔
      constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X K ∧
      DerivedCategory.TStructure.t.le 0 K ∧ DerivedCategory.TStructure.t.ge 0 K) ∧
    Nonempty (Abelian (ConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X)) ∧
    ObjectProperty.IsClosedUnderKernels
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsClosedUnderCokernels
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsClosedUnderExtensions
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    EssentiallySmall.{u + 1}
      (ConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) := by
  sorry

end AlgebraicGeometry.ProEtale
