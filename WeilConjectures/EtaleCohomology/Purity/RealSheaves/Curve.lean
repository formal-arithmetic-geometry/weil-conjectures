/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Construction
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity

/-!
# Purity of rank-one Weil sheaves on actual curves

For a smooth geometrically connected curve `C₀` over a finite field, the Weil group
`AlgebraicGeometry.WeilGroup.ofFundamentalGroup` built from its étale fundamental group is a
Weil group in the sense of `AlgebraicGeometry.WeilGroup`, and its geometric part is the
étale fundamental group of the geometric curve (the homotopy exact sequence,
`AlgebraicGeometry.WeilGroup.isEtaleQuotient_ofFundamentalGroup`). Hence the rank-one purity
theorems of `sk-p-real-rankone` apply to it.

## Main statements

- `AlgebraicGeometry.WeilGroup.isEtaleQuotient_ofFundamentalGroup`: the homotopy exact sequence
  `1 → π₁(C) → π₁(C₀) → Gal(𝔽̄_q / 𝔽_q) → 1`, in the form of
  `AlgebraicGeometry.WeilGroup.IsEtaleQuotient`.
- `AlgebraicGeometry.WeilGroup.ofFundamentalGroup_finite_geometric_image`: a rank-one lisse
  Weil sheaf on a curve has finite geometric image.
- `AlgebraicGeometry.WeilGroup.ofFundamentalGroup_isPunctuallyPure_of_finrank_eq_one`: a rank-one
  lisse Weil sheaf on a curve is punctually pure.
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} (p : C ⟶ Spec (.of K)) [IsCurve p]
  [GeometricallyConnected p] [ConnectedSpace C] (s : Spec (.of (AlgebraicClosure K)) ⟶ C)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

/-- **The homotopy exact sequence** (Stacks `0BTX`, SGA 1 IX.6.1): for a geometrically connected
curve `C₀` over a finite field `𝔽_q`, the geometric part `ker deg` of the Weil group
`W(C₀, s) ⊆ π₁(C₀, s) × ℤ`, that is the kernel of `π₁(C₀, s) → Gal(𝔽̄_q / 𝔽_q)`, is the étale
fundamental group of the geometric curve `C = C₀ ×_{𝔽_q} 𝔽̄_q`, Frobenius-equivariantly. -/
instance isEtaleQuotient_ofFundamentalGroup : (ofFundamentalGroup p s G).IsEtaleQuotient := by
  sorry

variable (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  [FiniteDimensional (PadicAlgCl l) V]

/-- Blueprint `thm-wf-rank-one-finite-geometric-image-curve`: the geometric image of a rank-one
lisse Weil sheaf on a smooth geometrically connected curve over `𝔽_q` is finite, for
`ℓ ≠ char 𝔽_q`; here the sheaf is a lisse representation of the Weil group
`AlgebraicGeometry.WeilGroup.ofFundamentalGroup` of the curve. -/
theorem ofFundamentalGroup_finite_geometric_image [SmoothOfRelativeDimension 1 p]
    [Fact (ringChar K ≠ l)]
    (ρ : Representation (PadicAlgCl l) (ofFundamentalGroup p s G).carrier V)
    (hrank : Module.finrank (PadicAlgCl l) V = 1) (hρ : (ofFundamentalGroup p s G).IsLisse l ρ) :
    (Set.range fun g : (ofFundamentalGroup p s G).geometric ↦ ρ g).Finite :=
  IsLisse.finite_geometric_image _ l ρ hrank hρ

/-- Blueprint `cor-wf-rank-one-punctual-purity-curve`: a rank-one lisse Weil sheaf on a smooth
geometrically connected curve over `𝔽_q` is punctually `ι`-pure, of weight `2 log_q |ι c|`
where `c` is its value at a degree-one element, for `ℓ ≠ char 𝔽_q`; here the sheaf is a lisse
representation of the Weil group `AlgebraicGeometry.WeilGroup.ofFundamentalGroup` of the
curve. -/
theorem ofFundamentalGroup_isPunctuallyPure_of_finrank_eq_one [SmoothOfRelativeDimension 1 p]
    [Fact (ringChar K ≠ l)]
    (ρ : Representation (PadicAlgCl l) (ofFundamentalGroup p s G).carrier V)
    (ι : PadicAlgCl l →+* ℂ) (hrank : Module.finrank (PadicAlgCl l) V = 1)
    (hρ : (ofFundamentalGroup p s G).IsLisse l ρ) :
    (ofFundamentalGroup p s G).IsPunctuallyPure l ρ ι (frobeniusWeight ι (Nat.card K)
      (LinearMap.det (ρ (ofFundamentalGroup p s G).frobeniusLift))) :=
  IsLisse.isPunctuallyPure_of_finrank_eq_one _ l ρ ι hrank hρ

end AlgebraicGeometry.WeilGroup
