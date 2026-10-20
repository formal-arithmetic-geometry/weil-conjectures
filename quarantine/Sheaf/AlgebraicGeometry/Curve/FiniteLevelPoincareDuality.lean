/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.Curve.FiniteCoefficientCup
public import Sheaf.AlgebraicGeometry.Curve.DegreeNormalizedTrace
public import Sheaf.Paper.IntrinsicCoefficientTwists
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
import WeilConjectures.AlgebraicGeometry.Curve.EtaleCohomologicalDimension
import Sheaf.Algebra.Homology.BoundedFreeProjectiveCohomologySplitting
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
import WeilConjectures.AlgebraicGeometry.Curve.Estimate
import Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule
import WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise

/-! # Finite-level Poincare duality for a geometric curve

Source: Weil conjectures blueprint, main-20261015, sec-purity-real-sheaves,
sk-p-real-rankone, finite-level Poincare duality
(blueprint: lem-wf-curve-finite-level-pd).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Cup product followed by the degree-normalized trace is a perfect pairing.
Source: blueprint sk-p-real-rankone, finite-level Poincare duality
(blueprint: lem-wf-curve-finite-level-pd).

`Sheaf.H` is the ordinary etale cohomology model permitted by the recorded
`def-weil-pbc-etale-cohomology`. The first Tate twist is the etale root sheaf,
the finite-level realization of `def-coefficient-twists-detailed`.
The existential module structures are unique: an abelian group has at most one
module structure over ZMod N. Thus these quantify the canonical scalar actions,
not extra input structures. The following instance lambda keeps these structures
available to `LinearMap.IsPerfPair` without a hidden let in the statement.

Proof, following the five steps of the DAG:
1. Etale/pro-etale comparison, Kummer theory and the Jacobian Tate-module lemma
identify the degree-one groups as finite free modules. Cohomological dimension,
proper cohomology and `thm-av-final` give finite free groups also in degrees zero
and two, with vanishing outside [0,2].
2. Point-perfectness supplies bounded finite free models of the two derived
cohomology complexes. The bounded-free/projective-cohomology splitting lemma
splits off their cohomology and contractible summands.
3. Proper Poincare duality in relative dimension one identifies the derived dual
of the untwisted complex with the twisted complex shifted by two.
4. Taking degree minus one, and using the preceding splitting, identifies the
first twisted cohomology with the module dual of the first untwisted cohomology.
The degree-of-the-pairing compatibility identifies evaluation with the canonical
cup product and the smooth trace. In degree minus two the same duality identifies
the trace as an isomorphism. The point-class normalization gives precisely the
degree-normalized trace used here.
5. The adjoint maps in both variables are consequently bijective. Replacing a
trace isomorphism by another multiplies it by a unit, so perfectness is unchanged.
No equivariance assumption or conclusion is needed for this finite-level claim. -/
theorem exists_curveFiniteLevel_perfectPairing
    (k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K]
    [IsAlgClosure k₀ K] [IsAlgClosed K]
    (C₀ : Scheme.{u}) [C₀.Over (Spec (.of k₀))]
    [SmoothOfRelativeDimension 1 (C₀ ↘ Spec (.of k₀))]
    [IsProjective (C₀ ↘ Spec (.of k₀))]
    [GeometricallyConnected (C₀ ↘ Spec (.of k₀))]
    (C : Scheme.{u}) [C.Over (Spec (.of K))]
    [IsConnectedCurve (C ↘ Spec (.of K))] [Smooth (C ↘ Spec (.of K))]
    [IsProper (C ↘ Spec (.of K))]
    (p : C ⟶ C₀)
    (hC : IsPullback p (C ↘ Spec (.of K)) (C₀ ↘ Spec (.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (ell c : ℕ) [Fact ell.Prime] [CharP k₀ c] [CharP K c] (hell : ell ≠ c)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (m : Module (ZMod (ell ^ n)) (Sheaf.H (C.constantZMod (ell ^ n)) 1))
      (m' : Module (ZMod (ell ^ n)) (Sheaf.H (C.rootsOfUnitySheaf (ell ^ n)) 1)),
      ((fun [m₁ : Module (ZMod (ell ^ n)) (Sheaf.H (C.constantZMod (ell ^ n)) 1)]
          [m₂ : Module (ZMod (ell ^ n)) (Sheaf.H (C.rootsOfUnitySheaf (ell ^ n)) 1)] =>
        ∃ B : Sheaf.H (C.constantZMod (ell ^ n)) 1 →ₗ[ZMod (ell ^ n)]
            Sheaf.H (C.rootsOfUnitySheaf (ell ^ n)) 1 →ₗ[ZMod (ell ^ n)] ZMod (ell ^ n),
          (∀ (x : Sheaf.H (C.constantZMod (ell ^ n)) 1)
              (y : Sheaf.H (C.rootsOfUnitySheaf (ell ^ n)) 1),
            B x y = Scheme.degreeNormalizedCurveTrace K C (C ↘ Spec (.of K))
              ell c hell n hn (C.finiteCoefficientCup (ell ^ n) 1 1 2 rfl x y)) ∧
          B.IsPerfPair) (m₁ := m) (m₂ := m')) := by
  sorry

end AlgebraicGeometry
