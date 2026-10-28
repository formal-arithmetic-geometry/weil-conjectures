/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.WeilSheaf.FourierInversion.ProjectiveLineRestriction
public import WeilConjectures.WeilSheaf.TateTwist

/-! # The projective-line decomposition, normalized at infinity -/

@[expose] public section

universe u
open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

/-- The relative projective-line calculation with restriction to infinity as its degree-zero
coordinate (blueprint: lem-pur-b3-weil-projective-decomposition).

Source: blueprint `thm-amb-p1-decomposition` and `sk-prop-an` (integration); also the
projective-line decomposition used in
`thm-pur-rank-one-thom`, Step 3. For the proper projection q of the projective line, the unit
and the first Chern class give the decomposition Rq_*q^*K = K ⊕ K(-1)[-2]. The second
coordinate in the ordering here is restriction to infinity. To check this normalization,
restrict the unit to infinity: it is the identity by the adjunction identities. The Chern
class restricts to zero since O(1) restricted to that section is trivial. Thus the matrix of
restriction is (0,1). The other coordinate is the trace. The finite-coefficient projective
bundle formula and projection formula prove that the resulting matrix is invertible; pass
through the compatible adic system, extend scalars, and retain the Frobenius-equivariant
maps. Descent from finite coefficients preserves this isomorphism, giving the asserted
natural transformation for bounded constructible Weil complexes. This is only the proper
projective-line calculation; it does not assert the affine-line Thom isomorphism. -/
theorem exists_projectiveLine_trace_decomposition
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ p : projectiveLineCohomology (k₀ := k₀) (l := l) X ⟶
        tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ),
      ∀ K, IsIso (biprod.lift (p.app K) ((projectiveLineRestriction X).app K)) := by sorry

end AlgebraicGeometry.WeilComplex
