## Worker report

The module `Sheaf.RingTheory.GradedInjectiveMultiplicationPolynomialLift` states
`GradedAlgebra.injective_multiplication_polynomial_lift`, with a single `sorry`.
It introduces no new definitions and makes no changes to the natural-language node.
The source was read at Stacks Algebra, `proposition-graded-hilbert-polynomial`
(Tag 00K1), especially its final shifted exact sequence, and
`lemma-numerical-polynomial` (Tag 00JZ), the binomial-basis integration argument.
The source's general Noetherian/finite-module assumptions are not needed for this
isolated recurrence lemma: the node instead explicitly assumes finite-dimensional
pieces, injectivity, and the eventual quotient polynomial.

Clause-by-clause rendering:

- A field k: `{k : Type u} [Field k]`. The commutative k-algebra S is
  `{S : Type v} [CommRing S] [Algebra k S]`. Independent universes u, v, w
  allow any sizes for the field, algebra and module.
- The standard grading is `𝒜 : ℕ → Submodule k S`, `[GradedAlgebra 𝒜]`, and
  `[IsStandard 𝒜]`, using the recorded `GradedAlgebra.IsStandard` directly.
  Its `fg_one` and `adjoin_one` give finite degree-one generation; the recorded
  `grade_zero_eq_one` identifies degree zero with the image of k.
- The S-module is `{N : Type w} [AddCommGroup N] [Module S N]`.
  `[Module k N] [IsScalarTower k S N]` expresses its induced k-vector-space
  structure and the compatibility of this structure with its S-action.
- The finite-dimensional decomposition is `𝒩 : ℕ → Submodule k N`,
  `[DirectSum.Decomposition 𝒩]`, and `[∀ n : ℕ, FiniteDimensional k (𝒩 n)]`.
  Mathlib's decomposition is the canonical recomposition isomorphism, not an
  arbitrary equivalence. `[SetLike.GradedSMul 𝒜 𝒩]` expresses exactly
  `S_i N_j ⊆ N_(i+j)`.
- The multiplier is `(x : S) (hx : x ∈ 𝒜 1)` and injectivity is
  `hinj : Function.Injective (fun m : N ↦ x • m)` on the entire module.
- The quotient is Mathlib's `QuotSMulTop x N = N ⧸ x • ⊤`.
  Its canonical k-linear quotient map is
  `(x • (⊤ : Submodule S N)).mkQ.restrictScalars k`.
  Every appearance of C_n is exactly `(𝒩 n).map` of this map, the image of N_n
  in N/xN. `DirectSum.IsInternal` states these images give the quotient grading;
  the next conjunct gives finite-dimensionality of every C_n, including C_0.
- For every n : ℕ, the existential k-linear maps μ and q are fixed by the
  normalization equations `(μ m : N) = x • (m : N)` and
  `(q m : QuotSMulTop x N) = Submodule.Quotient.mk (m : N)`.
  Thus they are precisely the multiplication and quotient maps, with no freely
  chosen maps or extra assumptions. `Function.Injective μ`, `Function.Exact μ q`
  and `Function.Surjective q` express all three exactness positions of
  `0 → N_n → N_(n+1) → C_(n+1) → 0`.
- The same conjunct states
  `(Module.finrank k (𝒩 (n+1)) : ℚ) - (Module.finrank k (𝒩 n) : ℚ) = dim C_(n+1)`.
  Rational subtraction gives the stated dimension difference without truncated
  natural subtraction.
- The last conjunct separately quantifies every `(P : Polynomial ℚ) (d : ℕ)`.
  Its premise is precisely `∀ n, d ≤ n → (dim C_n : ℚ) = P.eval (n : ℚ)`.
  The exact-sequence and grading conclusions are independent of this premise.
- Its conclusion quantifies `B : Polynomial ℚ`, `c : ℚ`, `e : ℕ` with
  `B - B.comp (Polynomial.X - Polynomial.C 1) = P`, a polynomial equality,
  and `∀ n, e ≤ n → (dim N_n : ℚ) = B.eval (n : ℚ) + c`.
  This is the backward-difference identity and the eventual dimension formula.

Dependency declarations read and used:

- `WeilConjectures.RingTheory.GradedAlgebra.Standard`:
  `GradedAlgebra.IsStandard`, `grade_zero_eq_one`, `finite_grade`; this is the
  recorded interface for `def-pc-standard-graded-algebra`.
- `Mathlib.LinearAlgebra.Dimension.Finrank`: `Module.finrank`, the recorded
  dimension notion for `def-weil-vector-space-dimension`.
- `Mathlib.Algebra.Polynomial.Basic` through the public Eval.Defs import:
  `Polynomial`, the recorded `def-weil-polynomial-ring`, with evaluation and
  composition from its standard API.
- `Mathlib.Algebra.DirectSum.Decomposition`: `DirectSum.Decomposition` and
  `DirectSum.IsInternal`; the former's inverse is unique and canonical.
- `Mathlib.RingTheory.QuotSMulTop`: `QuotSMulTop`; `Submodule.mkQ`,
  `LinearMap.restrictScalars`, and `Submodule.map` give the canonical images.
- Proof import `Mathlib.LinearAlgebra.Dimension.RankNullity`:
  `Submodule.finrank_quotient_add_finrank`, the matched proof leaf; submodule and
  quotient finite-dimensionality instances are in FiniteDimensional.Defs.
- Proof import `WeilConjectures.Mathlib.Algebra.Group.ForwardDiff`:
  `Polynomial.exists_degree_lt_eval_eq_of_sub`, recorded by the closed upstream
  audit for `lem-trf-rational-sequence-polynomial-forward-difference`.
  Its bound is degree < b and its recurrence is f(n+1)-f(n)=A(n), as required.
- Proof import `Mathlib.Algebra.Polynomial.Roots`:
  `Polynomial.eq_of_infinite_eval_eq`, the matched integral-domain identity leaf.

Edge cases checked: n=0 gives N_0 → N_1 → C_1, with no negative index;
d=0 includes all natural quotient degrees; P=0 is permitted and integrates to
an eventually constant Hilbert function; N=0 gives zero pieces and zero maps,
which are injective/surjective on zero spaces. No Nontrivial assumption is placed
on S or N, and no infinite-field assumption is placed on k. A zero x can be
injective only on the zero module, which is allowed. The grading starts at zero,
so there is no lost negative-degree piece. No hypothesis of finite generation of
N is added. No counterexample or statement fault was found.

Searches for existing statements and notions:

- `msearch.py leanfinder`, query: "Injective degree one multiplication on a graded
  module gives quotient exact sequences and lifts eventual Hilbert polynomials".
  Eight hits included `HomogeneousSubmodule.toSubmodule_injective`,
  `HomogeneousLocalization.Away.eventually_smul_mem`, and
  `QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last`.
  None states this graded recurrence and eventual polynomial lift.
- `msearch.py loogle`, query `GradedAlgebra.IsStandard, Module.finrank`:
  no hits (the external index does not recognize the project's IsStandard).
- `msearch.py leansearch`, query: "The Hilbert function of a graded module is
  eventually polynomial if multiplication by a degree one element is injective
  and the quotient has eventually polynomial dimension". Eight hits chiefly
  `Polynomial.hilbertPoly`, `preHilbertPoly`, and identities for formal Hilbert
  polynomials. They do not assert the graded exact sequences or this implication.
- `msearch.py grep`, query `hilbertPoly|finrank.*quotient|exists.*polynomial`,
  subdirectory `RingTheory`: 25 hits, including polynomial quotient dimensions
  and Hilbert-polynomial formal constructions, without the desired statement.
- `rg` in Mathlib's direct sum, graded algebra, quotient, and dimension sources
  found the existing decomposition, graded action, quotient and dimension APIs
  used here. No notion needed a second definition.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for graded polynomial,
  injectivity and quotient dimensions found `StandardGradedHilbertFunction`,
  `GradedSubmoduleFinite`, and existing QuotSMulTop uses. The first asserts
  eventual polynomiality for a finite module and does not include the quotient
  exact sequences or the antidifference identity. `rg` for the item's id in
  `lean/WeilConjectures` found no existing declaration. The proposed declaration
  name has no hit in Mathlib, WeilConjectures, Sheaf, or dag/lean_names_upstream.json.

Validation: scompile.py compiled the module separately as a sandbox file and at
its intended module path against the live published library, with no errors or
warnings. `set_option autoImplicit false` forbids auto-bound variables. Every
universe and type variable is bound explicitly. The theorem's docstring gives
all four proof steps and their DAG inputs; its only proof is `sorry`.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
