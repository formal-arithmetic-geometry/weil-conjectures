/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.ConstructibleSheaf.MonoidalParts
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat

/-!
# Bounded flat constructible total tensors on the small etale site

Source: blueprint main-20261015, `sk-thm-sf-ctf-stability-direct-images`, proof (1),(2),
finite coefficients; Stacks Project, Tags 095I, 03RZ, 06YQ, 07A2 and 06YU
(blueprint: lem-sfb-finite-flat-constructible-total-tensor).

The total tensor is the existing signed direct-sum `CochainComplex.mapBifunctor`.
The equality naming `T` specifies this construction, rather than an arbitrary model.
All sheaves, cohomology objects and derived tensors use the same etale module category.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The signed total tensor of bounded flat constructible complexes over a finite ring
has flat constructible terms, the sum support interval, and constructible cohomology.
It is K-flat and represents the ordinary relative derived tensor. Tensoring its derived
image with any module sheaf in degree zero has cohomology in the same sum interval.

Source: blueprint main-20261015, `sk-thm-sf-ctf-stability-direct-images`, proof (1),(2),
finite coefficients; Stacks Project, Tags 095I, 03RZ, 06YQ, 07A2 and 06YU
(blueprint: lem-sfb-finite-flat-constructible-total-tensor).

Proof:
1. The upper term bounds and exactness of tensor with each term make P and Q K-flat,
   by `lem-weil-pbc-independent-bounded-flat-kflat` (06YQ). The small-site universe
   convention is `def-weil-size-convention`; no lower bound is needed in this step.
2. `lem-pur-kflat-total-tensor-model` (07A2 and 0G6Q) makes their actual signed total
   tensor K-flat with flat terms, over the same ringed site.
3. In `def-pc-tensor-complex-sheaves`, a nonzero summand has a <= i <= b,
   c <= j <= d and i+j=n. Only finitely many pairs remain. None remain outside the
   sum interval. Tensor preserves zero by `lem-weil-pbc-independent-sheaf-tensor-colimits`
   and `def-pur-sheaf-tensor-product`; the coproduct universal property discards the
   other zero summands. These are bounds on terms, not just cohomology.
4. Refine the stratifications of P^i and Q^j by actual fibre-product intersections,
   using `lem-weil-pbc-constructible-stratification-intersection` and
   `lemma-constructible-of-refines`. On each stratum, inverse image agrees with module
   pullback over the constant coefficient ring by `prop-weil-pbc-inverse-image-modules-exact`.
   Apply `lem-weil-pbc-ringed-topoi-module-pullback-tensor` and the locally constant and
   finite parts `lem-weil-pbc-flc-tensor-locally-constant-part` and
   `lem-weil-pbc-flc-tensor-finite-part`. Finitely generated values over finite A are
   finite. Thus each nonzero tensor summand is constructible.
5. `thm-constructible-serre` (03RZ) gives kernels, cokernels and extensions, hence zero
   and finite direct sums, proving termwise constructibility. The cycles are kernels
   of maps between constructible terms; cohomology is the cokernel of the previous
   term mapping into those cycles (`def-weil-derived-cohomology-sheaves`). It is
   constructible without asserting closure under arbitrary subsheaves.
6. `lem-weil-pbc-site-derived-tensor-descent` compares Q(T) with the ordinary derived
   tensor of Q(P), Q(Q). Use the identity K-flat resolution in `def-kun-derived-tensor`;
   `lem-kun-derived-tensor-well-defined` identifies this with every other K-flat model.
7. `lem-sf-ringed-kflat-single-tensor-comparison` represents Q(T) tensor-derived N[0]
   by the termwise tensor with N, with differential d_T tensor 1. Terms still vanish
   outside the sum interval, since tensor preserves zero. The kernel/image formula
   gives zero cohomology there. N need not be flat or constructible.

K-flatness uses `CochainComplex.IsKFlatForTotalTensor`, owned by the landed node
`def-sfb-preserves-kflat-quasi-iso`. Its two-sided quasi-isomorphism test equals the
acyclic-test K-flatness of `def-pc-kflat-complex` here: tensor preserves zero, so
preservation of quasi-isomorphisms sends an acyclic complex's map to zero to a
quasi-isomorphism. Conversely, the cone criterion and tensor's compatibility with
cones give preservation of quasi-isomorphisms from the acyclic test; signed tensor
symmetry identifies the left and right tests. No dependency record is rebound.
The zero ring, empty scheme, zero terms and one-degree intervals are included. -/
theorem finiteFlatConstructible_totalTensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (a b c d : ℤ) (_hab : a ≤ b) (_hcd : c ≤ d)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hPflat : ∀ i : ℤ, exactFunctor _ _
      (@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) (P.X i)))
    (_hQflat : ∀ j : ℤ, exactFunctor _ _
      (@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) (Q.X j)))
    (_hPc : ∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (P.X i))
    (_hQc : ∀ j : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (Q.X j))
    (_hPbound : ∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i))
    (_hQbound : ∀ j : ℤ, (j < c ∨ d < j) → IsZero (Q.X j))
    (T : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hT : T = CochainComplex.mapBifunctor P Q
      (@curriedTensor _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)))) :
    (∀ n : ℤ, exactFunctor _ _
      (@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) (T.X n))) ∧
    (∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (T.X n)) ∧
    (∀ n : ℤ, (n < a + c ∨ b + d < n) → IsZero (T.X n)) ∧
    (∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ n).obj
        (_root_.DerivedCategory.Q.obj T))) ∧
    (@CochainComplex.IsKFlatForTotalTensor _ _ _
      (Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} A)) _ _ T) ∧
    Nonempty (_root_.DerivedCategory.Q.obj T ≅
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj
        (_root_.DerivedCategory.Q.obj P)).obj (_root_.DerivedCategory.Q.obj Q)) ∧
    ∀ (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℤ),
      (n < a + c ∨ b + d < n) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          (_root_.DerivedCategory.Q.obj T)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj N))) := by
  sorry

end AlgebraicGeometry.Etale
