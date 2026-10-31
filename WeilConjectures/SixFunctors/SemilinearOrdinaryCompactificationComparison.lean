/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralCompactificationOrdinaryComposition
public import WeilConjectures.SixFunctors.IntegralCompactificationComparisonData

/-! # Semilinear counits and ordinary integral composition

Source: blueprint fix-lem-exchanges Step 5; Stacks 0941 and 0F7B--0F7D
(blueprint: lem-sf-semilinear-ordinary-compactification-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralCompactificationBridge
open IntegralSystemRealization GeneratorReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section FiniteField
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [IsSeparated (Z ↘ Spec (.of D.k))]
  {f : X ⟶ Y} {g : Y ⟶ Z}
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [g.IsOver (Spec (.of D.k))] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

/-- Semilinear counit composition agrees with ordinary completed-ring composition.
No constant-coefficient word, q comparison or completedComparison occurs here.

Source: Stacks 0941 and 0F7B--0F7D; blueprint fix-lem-exchanges Step 5;
bridge proof Steps 2, 3 and the semilinear part of Step 7
(blueprint: lem-sf-semilinear-ordinary-compactification-comparison).

Proof: for a single compactification write d for its directIdentification. The
open reduction mate, inverse reconstruction unit and proper/limit comparison
are exactly its factors. Unit naturality and the reduction/limit right triangle
identify the transpose of d inverse with e followed after reduction of d inverse.
Apply this calculation to f and to g at F_f K. The recursive composite has the
intermediate counit e at B_f R K, exactly the middle factor in semilinearComparison.
The normalized semilinear proper/open mate and its ordinary ringed-site mate
have the same inverse-open transpose: open normalization identifies the units,
and the proper comparisons are the adjunction conjugates of the same normalized
pullback squares. Their transpose equality gives the proper/open comparison
square before evaluation. The same conjugation identifies the two push and open
compositors, including the equalities t.i_q and t.p_g. Paste this square with the
two single-compactification transpose calculations, apply the total limit, and
cancel the reconstruction units using the adjunction triangles. The resulting
map is completedShriekIntegralA conjugated by the three published compact-support realization
isomorphisms, which is ordinaryComparison by definition. The common-window
hypothesis supplies all intermediate normalized and etale-origin systems and
ensures the direct identifications are invertible. Identity cases reduce to the
same triangles; empty opens and zero inputs give the unique zero map.
The existing completedShriekIntegralComposition supplies the expression-realization
version of this square; the single-letter calculation above identifies its recursive
comparisons with the direct identifications used here. -/
theorem semilinearOrdinaryCompactificationComparison
    (o : IntegralSystemRealization.Operations l E) (r : Realizations l E D o)
    (t : Compactification.Triangle f g)
    [QuasiCompact t.cf.i] [QuasiCompact t.cg.i] [QuasiCompact t.cfg.i] [QuasiCompact t.q]
    (K : sfIntegralConstructibleCategory l E X) (lo hi torLo torHi : ℤ)
    (_hK : bridgeDomain l E D.k (coefficientPrimeUnit l D hl) o t K lo hi torLo torHi) :
    semilinearComparison l E D.k (coefficientPrimeUnit l D hl) o r t K =
      (ordinaryComparison l E D.k (coefficientPrimeUnit l D hl)
        r t).app K := by sorry

end FiniteField
end WeilConjectures.IntegralCompactificationBridge
