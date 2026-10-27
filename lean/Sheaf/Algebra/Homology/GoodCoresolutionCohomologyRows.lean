module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Exact.Basic

/-! # Exact cohomology rows of a good coresolution

Source: Stacks Project, homology.tex, Tag 09J0,
`lemma-good-right-resolution-gives-qis`, displayed exact cohomology row, referring to
Tag 09IZ, `lemma-good-resolution-gives-qis`
(blueprint: lem-sfb-good-coresolution-cohomology-rows).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory HomologicalComplex

namespace CochainComplex.GoodCoresolution

/-- An augmented sequence exact on terms and differential cokernels is exact on cohomology.
Here `opcycles n` is the quotient of degree `n` by boundaries from degree `n - 1`.
Source: Stacks Project, homology.tex, Tag 09J0, displayed exact cohomology row, and
Tag 09IZ, first paragraph (blueprint: lem-sfb-good-coresolution-cohomology-rows).

Proof: reindex by `A₀ = M`, `Aⱼ₊₁ = Eⱼ`, and put `Aⱼ = 0` for negative indices;
write the horizontal maps as `hⱼ`. The term and quotient rows stay exact, including
at the initial position. Chain maps preserve cycles and boundaries; exactness on terms
gives zero consecutive horizontal composites, hence image is contained in kernel on
cohomology. If a cycle in `A₀` maps to a boundary, injectivity on differential cokernels
makes it a boundary already, proving injectivity of the first cohomology map.
For `j ≥ 1`, take a cycle `z` in `Aⱼ` whose next image is a boundary. Quotient-row
exactness gives `z = hⱼ₋₁(x) + d(y)`. Differentiating gives `hⱼ₋₁(d(x)) = 0`.
Term-row exactness in degree `n + 1` gives `d(x) = hⱼ₋₂(t)`; for `j = 1`,
injectivity of the augmentation gives `d(x) = 0` and we take `t = 0`.
The image of `t` is a boundary, so quotient-row exactness in degree `n + 1` gives
`t = hⱼ₋₃(s) + d(v)`. For `j = 1`, take `s = v = 0`; for `j = 2`, injectivity
of the first quotient map gives `t = d(v)` and `s = 0`. Thus
`d(x) = d(hⱼ₋₂(v))`. Set `x' = x - hⱼ₋₂(v)`. This is a cycle and
`hⱼ₋₁(x') = hⱼ₋₁(x)`, since consecutive horizontal maps compose to zero.
Consequently `z = hⱼ₋₁(x') + d(y)`, proving the reverse kernel-image inclusion.
Only degrees `n - 1`, `n`, `n + 1` and finitely many horizontal positions occur;
no boundedness is needed. -/
theorem homology_rows_exact (M : CochainComplex AddCommGrpCat.{u} ℤ)
    (E : ℕ → CochainComplex AddCommGrpCat.{u} ℤ) (u : M ⟶ E 0)
    (f : ∀ i : ℕ, E i ⟶ E (i + 1))
    (h_inj : ∀ n : ℤ, Function.Injective (u.f n))
    (h₀ : ∀ n : ℤ, Function.Exact (u.f n) ((f 0).f n))
    (h : ∀ (i : ℕ) (n : ℤ), Function.Exact ((f i).f n) ((f (i + 1)).f n))
    (hc_inj : ∀ n : ℤ, Function.Injective (opcyclesMap u n))
    (hc₀ : ∀ n : ℤ, Function.Exact (opcyclesMap u n) (opcyclesMap (f 0) n))
    (hc : ∀ (i : ℕ) (n : ℤ),
      Function.Exact (opcyclesMap (f i) n) (opcyclesMap (f (i + 1)) n)) :
    ∀ n : ℤ, Function.Injective (homologyMap u n) ∧
      Function.Exact (homologyMap u n) (homologyMap (f 0) n) ∧
      ∀ i : ℕ, Function.Exact (homologyMap (f i) n) (homologyMap (f (i + 1)) n) := by
  sorry

end CochainComplex.GoodCoresolution
