/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit
import Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology
import Sheaf.AlgebraicGeometry.CurveCoefficientPair
import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.Paper.ZeroDimensionalCohomology
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-! # Primary vanishing and finiteness across a dense open -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- Primary vanishing and the two conditional finiteness assertions transfer across a
 dense-open counit for a constructible sheaf killed by a prime.
Source: Stacks Project, Tag 0GJA, proof, the five-term sequence and remarks (a), (b)
(blueprint: lem-pbc-s2-dense-open-primary-finiteness).

Proof: Put G = j_!j^*F and B = i_*i^*F for the reduced closed complement i:Z -> X.
The geometric stalks of G are those of F on U and zero outside U. Hence G is constructible
and killed by r. Both primary torsion and invertible-order torsion pass from F to G.
The complement is a finite union of k-rational points. Its degree-zero cohomology is a
finite product of stalk modules of F; these are finite because constructibility gives
finite generation and Λ is finite. Its positive-degree cohomology vanishes. The long exact
sequence gives 0 -> H^0(G) -> H^0(F) -> H^0(B) -> H^1(G) -> H^1(F) -> 0 and canonical
bijections H^q(G) -> H^q(F) for q >= 2. Consequently, finiteness of all groups for either
sheaf implies finiteness for the other: in degree zero use the injection and the finite
boundary group; in degree one use the surjection and its kernel, a quotient of that
boundary group; in higher degrees use the bijections. This proves the proper finiteness
assertion. For primary vanishing, fix a prime p equal to the characteristic. If r = p,
both sheaves are p-primary and the higher-degree bijections transfer the vanishings.
If r != p and G is p-primary, every stalk of G is killed by coprime integers, so G is zero
and its cohomology vanishes. In the reverse implication, if F is p-primary the same
coprimality argument makes F zero when r != p. For invertible-order finiteness, if r is
invertible in k, both sheaves have invertible-order torsion and the preceding finite-group
argument applies. If r is not invertible, an invertible-order hypothesis on either sheaf
forces that sheaf to be zero. All assertions are then automatic for that sheaf. These
cases prove the conditional equivalences without claiming the torsion hypotheses are
equivalent. Empty X and the full open U=X are covered by the same zero or identity maps. -/
theorem dense_open_primary_finiteness (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (r : ℕ) [Fact r.Prime] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0)
    (U : X.Opens) (hU : Dense (U : Set X)) :
    let G := (U.ι)_!open[ModuleCat.{u + 1} Λ].obj
      ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)
    (VanishingAboveOneOfIsPrimaryTorsionSheaf Λ F k ↔
      VanishingAboveOneOfIsPrimaryTorsionSheaf Λ G k) ∧
    (FiniteOfInvertibleOrder Λ F k ↔ FiniteOfInvertibleOrder Λ G k) ∧
    (FiniteOfIsProper Λ f F ↔ FiniteOfIsProper Λ f G) := by sorry

end AlgebraicGeometry.IsCurve
