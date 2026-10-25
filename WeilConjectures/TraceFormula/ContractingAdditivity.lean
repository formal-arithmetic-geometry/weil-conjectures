/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.LocalTermLocality
public import WeilConjectures.TraceFormula.PieceAdditivity

/-!

# Additivity of trace classes along a point with reduced fibre

Let `c = (c₁, c₂)` be an endocorrespondence of `(X, K)` and `y` a `k`-point of the fixed locus
such that the fibre `c₁⁻¹(x)`, `x = c₁(y)`, is the reduced point `y`. Then the closed point `{x}`
is `c`-invariant and the trace class of `c` is the sum of the trace classes of the induced
coefficient maps on the pieces `K^Z = Rx_* Lx^* K` and `K^U = j_! Lj^* K` of `K`
(`ProEtale.CondensedRing.Correspondence.traceClass_eq_add_of_isPullback`, blueprint
`prop-trf-trace-class-additivity`, item 1 for `Z = {x}`).

This is `Correspondence.traceClass_eq_add_of_distTriang` for the open–closed triangle
`K^U ⟶ K ⟶ K^Z ⟶`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

variable (c : Correspondence ℓ K)

/-- **Additivity of trace classes along the pieces of a point with reduced fibre** (blueprint
`prop-trf-trace-class-additivity`, item 1, and `lem-trf-trace-triangle-compatibility`, for the
`c`-invariant closed subscheme `Z = {x}` of the rational point `x = c₁(y)` of a `k`-point `y` of
the fixed locus such that `c₁⁻¹(x)` is the reduced point `y`; Varshavsky, Prop. 1.5.10 after
SGA 5, III 4.13): the trace class of `u` is the sum of the trace classes of the induced
coefficient maps `u^Z = [x, y]_! u_Z` on `K^Z = Rx_* Lx^* K`, the proper pushforward of the
restricted coefficient map along `(x, y)`, and `u^U = [j]_! (u|_U)` on `K^U = j_! Lj^* K`. -/
theorem traceClass_eq_add_of_isPullback (F : c.FixedLocus) {y : RationalPoint c.C}
    (hy : y ≫ c.c₁ = y ≫ c.c₂) (sq : IsPullback y (𝟙 (point k)) c.c₁ (y ≫ c.c₁)) :
    c.traceClass F =
      F.traceClassWithCoeff _ (restrictedClosedPieceDiagram hy sq).pushforwardCoeff +
        F.traceClassWithCoeff _ (c.pointOpenPieceCoeff (y ≫ c.c₁)
          (preimage_pointComplOpens_le_of_isPullback hy sq)) :=
  sorry

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
