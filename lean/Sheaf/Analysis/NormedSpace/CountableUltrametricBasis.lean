module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Maps.Basic

/-!
# Uniformly bounded algebraic coordinates in a countable ultrametric space

Source: main-20261015 blueprint, `sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), agent auxiliary for the geometric norm projection; an exact external
reference is WANTED (blueprint: lem-sfb-countable-normed-orthogonal-basis).

The coordinates are algebraic finite-support coordinates. No completeness of the
vector space and no convergence of infinite series are asserted.
-/

@[expose] public section

universe u v

namespace Padic

open Classical in
/-- A countably generated ultrametric normed space has uniformly bounded algebraic
coordinates with any prescribed nonzero first basis vector.

Source: main-20261015 blueprint, `sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), agent auxiliary for the geometric norm projection; exact reference WANTED
(blueprint: lem-sfb-countable-normed-orthogonal-basis).

Proof: Prepend `v₀` to a spanning sequence. Starting with `v₀`, discard vectors already
in the retained finite span. Otherwise apply `lem-sfb-finite-ultrametric-best-approximation`
to subtract a nearest point in that span; `lem-sfb-ultrametric-orthogonal-extension`
shows that the resulting nonzero residual extends the orthogonal family and preserves
its span together with the next sequence vector. Each finite subfamily occurs in a
finite stage, so the retained family is independent and orthogonal. Every sequence
vector belongs to a finite-stage span, so the family is an algebraic basis indexed by
a nonempty initial segment of the naturals or all the naturals.

Put `q = |ℓ|⁻¹ > 1`. Leave the first vector fixed and multiply each other vector by
an integer power of `ℓ` so its norm lies in `[1,q)`. This preserves orthogonality and
the algebraic basis property. The exact orthogonal finite-sum formula implies the
two bounds with `c = min ‖v₀‖ 1` and `C = max ‖v₀‖ q`, including the empty support.
The lower bound controls every coordinate; the upper bound then controls every subset
projection and every injective basis relabeling by `C/c`. The lower bound for such a
relabeling also controls its inverse on the coordinate subspace, so it is an embedding.
All expansions are finite, and completeness of `V` is never used.

`J` is an initial segment or all of `ℕ`. `Finset.sup` in `ℝ≥0` gives zero on empty
support. The final embedding clause states continuity of each basis injection and of
its inverse onto its image, which is the span of the selected basis subset.
-/
theorem exists_countable_ultrametric_basis
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (V : Type v) [NormedAddCommGroup V]
    (h_ultra : ∀ x y : V, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (v₀ : V) (hv₀ : v₀ ≠ 0) :
    letI := spectralNorm.nontriviallyNormedField (Padic l) E
    ∀ [NormedSpace E V],
      (∃ s : ℕ → V, Submodule.span E (Set.range s) = ⊤) →
      ∃ (J : Set ℕ) (h₀ : 0 ∈ J) (b : Module.Basis J E V) (c C : ℝ),
        (J = Set.univ ∨ ∃ d : ℕ, 1 ≤ d ∧ J = Set.Iio d) ∧
        b ⟨0, h₀⟩ = v₀ ∧ 0 < c ∧ c ≤ C ∧
        (∀ a : J →₀ E,
          c * ((a.support.sup (fun j ↦ ‖a j‖₊) : NNReal) : ℝ) ≤ ‖b.repr.symm a‖ ∧
          ‖b.repr.symm a‖ ≤ C * ((a.support.sup (fun j ↦ ‖a j‖₊) : NNReal) : ℝ)) ∧
        (∀ j : J, Continuous (b.coord j)) ∧
        (∀ S : Set J, Continuous (b.constr E (fun j ↦ if j ∈ S then b j else 0))) ∧
        (∀ σ : J ↪ J, Topology.IsEmbedding (b.constr E (fun j ↦ b (σ j)))) := by
  sorry

end Padic
