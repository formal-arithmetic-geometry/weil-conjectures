/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.Paper.SmoothPurityCompletedTowerRoos

/-! # Constructibility of the completed ell-power reduction

Source: latest blueprint, sec-smooth-purity, sk-lem-sp-tower-equivalence.proof.md;
Bhatt--Scholze, Lemma 3.5.7 (blueprint: lem-sp-completed-reduction-constructible).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Integral constructibility is carried to the existing normalized finite-Tor towers.
Source: latest blueprint, normalized equivalence, Restriction paragraph;
Bhatt--Scholze, Lemma 3.5.7; the reduction construction
(blueprint: lem-sp-completed-reduction-constructible).

Proof: transport M along the exact ring isomorphism R.coefficient. The defining
uniformizer reductions of sfIntegralConstructible have constructible cohomology in one
common interval. The intrinsic finite-torsion predicate is exactly the finite locally
closed stratification with locally constant finite stalks used by the pro-etale
constructibility predicate. Finite residue Tor gives a common Tor interval. Write
ell = unit times pi^e and select the positive uniformizer levels e(n+1); these are the
ell-power quotients, with identical completed scalar maps. The derived evaluation
isomorphisms R.evaluation identify them with the evaluations of spCompletedReduction.
Alternatively the integral constant-coefficient comparison identifies the transported
object with the constantModelBoundedConstructible input to R.constructible; Noetherian
T is qcqs, so that clause applies. All transitions are normalized by R.normalized.
The resulting bounded cohomology, constructible cohomology, and common Tor bounds are
exactly spConstructibleTorTowers, and normalization supplies the second conjunct. -/
theorem spCompletedReduction_constructible
    [∀ x : T, Invertible (l : T.residueField x)] [IsNoetherian T]
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    (hM : WeilConjectures.sfIntegralConstructible l E T M) :
    spNormalizedConstructibleTorTowers l E T D
      ((spCompletedReduction l E T D R).obj M) := by
  sorry

end AlgebraicGeometry.ProEtale
