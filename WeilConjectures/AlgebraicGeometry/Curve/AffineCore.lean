/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification

/-!
# Affine opens of a smooth curve and finite maps to the affine line

Two geometric inputs of the reduction of the Deligne–Laumon estimate from an arbitrary smooth
curve to the affine line (blueprint subsection `sk-thm-dl-a1-upper`).

## Main statements

- `AlgebraicGeometry.IsCurve.exists_isAffineOpen_dense_finite_compl`: a smooth geometrically
  connected curve has a nonempty dense affine open with finite complement.
- `AlgebraicGeometry.IsCurve.exists_isFinite_affineLine`: a smooth geometrically connected affine
  curve over a perfect field is a dense open with finite complement of a smooth geometrically
  connected curve admitting a finite, generically étale map to the affine line.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {C : Scheme.{u}}

/-- *Affine core of a smooth curve.* A smooth curve `C₀` which is geometrically connected has a
nonempty dense affine open `V₀` whose complement is finite.

The blueprint chooses `V₀` as the complement of a nonempty finite set in the smooth proper
completion of `C₀`. Here any nonempty affine open works: `C₀` is regular and connected, hence
irreducible, so a nonempty open is dense, and in an irreducible noetherian space of dimension
one the complement of a nonempty open is finite.
(blueprint: `lem-a1-affine-core-of-curve`) -/
theorem IsCurve.exists_isAffineOpen_dense_finite_compl (p : C ⟶ Spec (.of K)) [IsCurve p]
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] :
    ∃ V : C.Opens, IsAffineOpen V ∧ (V : Set C).Nonempty ∧ Dense (V : Set C) ∧
      (V : Set C)ᶜ.Finite := by
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsRegular C := IsRegular.of_smooth p
  obtain ⟨x, -⟩ := p.surjective (Classical.arbitrary _)
  have : ConnectedSpace C := GeometricallyConnected.connectedSpace_of_subsingleton (f := p)
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have : CompactSpace C := (quasiCompact_iff_compactSpace p).mp inferInstance
  have : IsNoetherian C := ⟨⟩
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  have hne : (V : Set C).Nonempty := ⟨x, hxV⟩
  exact ⟨V, hV, hne, V.isOpen.dense hne,
    V.isOpen.finite_compl_of_topologicalKrullDim_le_one (IsCurve.krullDim_le_one p) hne⟩

/-- *Finite map to the affine line.* Let `C₀` be a smooth affine curve over a perfect field `K`
which is geometrically connected. There is a smooth geometrically connected curve `C'₀`
containing `C₀` as a dense open with finite complement, and a finite morphism
`g : C'₀ ⟶ 𝔸¹_K` which is generically étale: étale on a dense open of `C'₀`.

In the smooth projective completion `C̄` choose a closed point `s ∉ C₀`. By Riemann–Roch there
is a function `f` with a single pole, at `s`, of order `m` prime to the characteristic; the
sections `1, f` of `𝒪(ms)` define a finite map `C̄ ⟶ ℙ¹` with `∞` pulling back to `s`, and
`df ≠ 0` since `ord_s f = -m` is prime to `p`, so the function-field extension is separable.
Then `C'₀ = C̄ \ {s}` and `g` is the restriction over `𝔸¹`.
(blueprint: `lem-a1-finite-map-curve`) -/
theorem IsCurve.exists_isFinite_affineLine [PerfectField K] (p : C ⟶ Spec (.of K)) [IsCurve p]
    [IsAffine C] [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] :
    ∃ (C' : Scheme.{u}) (p' : C' ⟶ Spec (.of K)) (j : C ⟶ C') (g : C' ⟶ affineLine K),
      IsCurve p' ∧ SmoothOfRelativeDimension 1 p' ∧ GeometricallyConnected p' ∧
      IsOpenImmersion j ∧ j ≫ p' = p ∧ DenseRange j.base ∧ (Set.range j.base)ᶜ.Finite ∧
      IsFinite g ∧ g ≫ (affineLine K ↘ Spec (.of K)) = p' ∧
      ∃ W : C'.Opens, Dense (W : Set C') ∧ Etale (W.ι ≫ g) :=
  sorry

end AlgebraicGeometry
