/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.IntegralCriterionReductions
public import Sheaf.Paper.CompletedCondensedCoefficients
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
import Sheaf.Paper.ContinuousIntegralCoefficients
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Sheaf.SixFunctors.ConstructibleOpenClosedRefinement
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Topology.NoetherianSpace
import Sheaf.Paper.IntegralLfpLocallyFreeResolution
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.CartesianCoefficients

/-!
# Integral constructibility and derived completion

Source: Bhatt--Scholze, Definition 6.5.1, Proposition 6.6.11 and
Proposition 6.8.11(3) (blueprint: lem-sfb-integral-constructible-completion-bridge).

The ordinary internal-module derived category is the ambient category. The detailed
integral predicate is evaluated under the existing projection-normalized coefficient
and section-action equivalence, without replacing K by its completion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- General ring-object bounded constructibility, detailed integral constructibility,
and bounded constructibility with finite constant scalar models are equivalent.
The uniformizer is arbitrary; the existing coefficient construction chooses a generator
of the same maximal ideal, hence the same positive quotient tower. The lift of the finite
intermediate field only places its scalar carrier in the scheme universe.

Source: Bhatt--Scholze, Definition 6.5.1, Proposition 6.6.11 and
Proposition 6.8.11(3) (blueprint: lem-sfb-integral-constructible-completion-bridge).

Proof:
1. Identify the pulled-back continuous integral ring with the inverse limit of the
finite quotient rings, using sk-prop-sfb-qlbar-colimit-x. The coefficient restriction
isomorphisms of sk-prop-sfb-cartesian-coefficients preserve presentations and cokernels.
The normalized integralSectionDerivedEquivalence makes this the same ring and the same
complex in the detailed integral presentation.
2. Locally closed strata of the Noetherian Z are Noetherian and finite dimensional,
with l invertible. Noetherian spaces have every subset quasi-compact, giving finite
affine covers of strata and quasi-separatedness; closure preserves strict irreducible
chains, and local-ring homomorphisms preserve units. Use the three Noetherian proof
leaves of the node, in particular lem-sfb-noetherian-space-compact-subsets.
3. For each nonzero cohomology sheaf on each original stratum, apply
lem-weil-pbc-integral-lfp-locally-free-resolution to its locally finite presentation.
It gives a short exact sequence with locally finite free terms, allowing torsion and
assuming no completeness.
4. Those free terms in degree zero have perfect scalar models. Apply
lem-weil-pbc-integral-stratified-perfect-characterization on the original stratum,
then lem-sf-derived-ses-triangle and cone closure, to place their cokernel in the
completed category and obtain its finite constant scalar models. No Noetherianity
is asserted of members of the trivializing pro-etale covers.
5. Refine the finitely many stratifications from the finitely many relevant degrees
using lem-fix-constructible-open-closed-refinement. Its factorization maps and exact
Cartesian coefficient pullbacks preserve scalar matrices. Apply
det-def-sfb-constructible-local-model to obtain condition (iii).
6. Conversely a finite constant scalar presentation is a finite presentation over
the pulled-back ring. Boundedness is unchanged, giving (iii) implies (i), with no
completeness hypothesis or claim that arbitrary coefficient sections are constant.
7. The integral stratified-perfect characterization identifies (iii) with (ii).
Its detailed-category comparison retains compatible etale-origin representatives
and a single cohomological interval for all positive reductions. Equivalently use
continuousIntegralConstructible_iff_sfIntegralConstructible under the fixed normalized
section-action equivalence. These implications give the two equivalences below.
-/
theorem integralConstructibleCompletionBridge
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (_π : PadicAlgCl.integers l E)
    (_hπ : Ideal.span {_π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E))
    (Z : Scheme.{u}) [IsNoetherian Z]
    (_hdim : ∃ n : ℕ, topologicalKrullDim Z ≤ n)
    (_hinv : IsUnit (l : Γ(Z, ⊤)))
    (K : DerivedCategory (AdicCompletion.Modules l (ULift.{u} E.val) Z)) :
    (boundedConstructible (AdicCompletion.ring l (ULift.{u} E.val) Z) K ↔
      WeilConjectures.sfIntegralConstructible l (ULift.{u} E.val) Z
        ((integralSectionDerivedEquivalence l (ULift.{u} E.val) Z).functor.obj K)) ∧
    (boundedConstructible (AdicCompletion.ring l (ULift.{u} E.val) Z) K ↔
      constantModelBoundedConstructible (DerivedNakayama.integerRing l (ULift.{u} E.val))
        Z K) := by
  sorry

end AlgebraicGeometry.ProEtale
