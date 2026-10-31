/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCompletedTowerRoos
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCompletedReductionConstructibleTransport

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

Proof: the normalized coefficient-transport lemma
spCompletedReduction_constantModel turns sfIntegralConstructible M into the
constantModelBoundedConstructible hypothesis of R.constructible, for M restricted along
R.coefficient.hom and internalized. A Noetherian scheme is compact and quasi-separated,
so the clause R.constructible applies; its second conjunct is
spNormalizedConstructibleTorTowers of R.red applied to the restricted M, which is
spCompletedReduction M by definition. -/
theorem spCompletedReduction_constructible
    [∀ x : T, Invertible (l : T.residueField x)] [IsNoetherian T]
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    (hM : WeilConjectures.sfIntegralConstructible l E T M) :
    spNormalizedConstructibleTorTowers l E T D
      ((spCompletedReduction l E T D R).obj M) := by
  exact (R.constructible inferInstance inferInstance _
    (spCompletedReduction_constantModel l E T D R M hM)).2.1

end AlgebraicGeometry.ProEtale
