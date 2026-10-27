## Worker report

The module `Sheaf.LinearAlgebra.DilatingWeightNakayama` states
`LinearMap.span_iterates_eq_top_of_dilating_weights`, with `sorry` as its entire
proof. No definition, dependency repair, new node or statement correction is
needed. Only `lean` changes in the existing node copy.

The statement corresponds to the node as follows.

- The field is `{k : Type u} [Field k]`; `u` is explicit. The sole statement
  dependency, `def-weil-field`, has status `mathlib` and records `Field` in
  `Mathlib.Algebra.Field.Defs`. I read its full declaration and docstring
  (lines 170–181): a commutative division ring, including nontriviality.
- The unital coefficient homomorphism is `(σ : k →+* k)`. There is no
  surjectivity, automorphism or characteristic assumption.
- The integer dilation factor is `(p : ℤ) (hp : 2 ≤ p)`. The nonnegative rank
  is `(s : ℕ)`, with integral lattice `Fin s → ℤ`. In particular the theorem
  does not silently require `p` prime or identify it with the characteristic.
- The vector space is `{V : Type v} [AddCommGroup V] [Module k V]` with an
  independent explicit universe `v` and no dimension or generation condition.
- The subspaces are `A : (Fin s → ℤ) → Submodule k V`. The finite, unique
  homogeneous decomposition is `hA : DirectSum.IsInternal A`, from
  `Mathlib.Algebra.DirectSum.Module` (definition in its public dependency
  `Mathlib.Algebra.DirectSum.Basic`). I read the definition and docstring:
  the canonical additive map from the direct sum of the submodules to `V`
  is bijective. Its source consists of finitely supported families, so
  bijectivity is exactly existence and uniqueness of a finite decomposition.
- The zero-weight summand condition is `hzero : A 0 = ⊥`, where `0` is the
  zero lattice vector and bottom is the zero subspace.
- Additivity and `T(av) = σ(a)T(v)` are bundled by `T : V →ₛₗ[σ] V`.
  I read the `LinearMap` signature and docstring in
  `Mathlib.Algebra.Module.LinearMap.Defs`: it extends an additive homomorphism
  and the scalar action homomorphism. It has no injectivity assumption.
- The dilation condition is
  `hT : ∀ (ν : Fin s → ℤ) (x : V), x ∈ A ν → T x ∈ A (p • ν)`.
  Integer scalar multiplication on lattice vectors multiplies each integer
  coordinate by `p`, exactly the node's `pν`.
- The subspace called `J` is written directly as
  `Submodule.span k (Set.range T)`. This is the set of finite `k`-linear
  combinations of images, including when the coefficient homomorphism is
  not onto. In particular it is not replaced by a semilinear-map range.
- The finite family is `(m : ℕ) (b : Fin m → V)`. The weights are
  `νb : Fin m → (Fin s → ℤ)` and `hb : ∀ j, b j ∈ A (νb j)`.
  Specifying witnessing weights is equivalent to the node's assertion that
  each vector lies in some summand; witnesses need not be unique for zero.
- Quotient spanning is `hspan : Submodule.span k (Set.range fun j ↦
  (Submodule.span k (Set.range T)).mkQ (b j)) = ⊤`.
  `Submodule.mkQ`, whose signature and docstring I read in
  `Mathlib.LinearAlgebra.Quotient.Defs`, is the canonical linear quotient map
  into `V ⧸ J`. Thus these are precisely the cosets of the given vectors.
- The conclusion is `Submodule.span k (Set.range fun rj : ℕ × Fin m ↦
  (T : V → V)^[rj.1] (b rj.2)) = ⊤`.
  The product index enumerates exactly all pairs `(r,j)` in the node.
  `Function.iterate` from `Mathlib.Logic.Function.Iterate` has the identity
  as its zeroth iterate, and `iterate_succ_apply'` gives `T ∘ T^r`.
  Equality to top says that this span equals the whole ambient space.

All other notions above are Mathlib declarations; the module imports their
defining modules publicly. `Submodule.span` is supplied by
`Mathlib.LinearAlgebra.Span.Defs`. The node has no proof dependencies, so no
proof imports are needed. The full six-step natural-language proof is included
in the theorem docstring, preserving the node's induction on the sum of absolute
values of the lattice coordinates.

Source comparison: I read the local Milne PDF page 308 (printed p.296).
Proposition 14.50 says that left ideals in the skew polynomial ring are principal
and submodules of finite free modules are free. It does not assert the graded
generation statement here; the node explicitly identifies this as an independent
agent refinement, and the module preserves that qualification. I also read
`literature/blueprint/latest/blueprint/sec-six-functors-basics/`'s
`sk-thm-sf-ctf-stability/_section.md` and its direct-images proof, especially
clause (3), as the inherited context. No stronger source claim is made.

Edge cases checked before writing:

- `s = 0`: `Fin 0 → ℤ` has only the zero weight, so internality and `A 0 = ⊥`
  imply that the whole space is zero. No positive-rank binder is present.
- `m = 0`: the range of the family in both spans is empty. The hypothesis is
  `V/J = 0`, and the weight induction proves `V = 0`. `Fin 0` is permitted.
- The zero space satisfies the statement, without a `Nontrivial V` assumption.
- `T = 0`: `J = ⊥`; the quotient-spanning family already spans `V`, and all
  zeroth iterates are included in the conclusion.
- Noninjective `T` is allowed. So are nonsurjective `σ` (for example the
  Frobenius on a nonperfect rational function field) and infinite-dimensional
  `V`; the proof only applies `σ` to coefficients in finite sums.
- Homogeneous vectors can be zero, and weights may repeat or be negative.
  No nonzero-family or positivity condition occurs.
- The zero-weight exclusion and the strict dilation are mathematically needed:
  with `V = k`, `T = id`, and an empty family, `V/J = 0` but the conclusion
  fails. Putting `V` at weight zero violates `hzero`; putting it at nonzero
  weight and taking `p = 1` violates `hp`. Both hypotheses are retained.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`: “Homogeneous generators modulo the span of the
  image of a semilinear map dilating integer lattice weights by p generate the
  vector space under iterates”. Eight results, headed by
  `HomogeneousLocalization.Away.span_mk_prod_pow_eq_top` and Profinite Nobeling
  span lemmas. None is this semilinear graded generation assertion.
- `msearch.py ... leansearch`: “A vector space with nonzero lattice weights
  and a semilinear weight dilating operator is generated by iterates of
  homogeneous lifts of generators modulo its image span”. Eight results on Lie
  generalized weight spaces; none has the operator or quotient in this node.
- `msearch.py ... loogle '"span", "iterate"'`: one result,
  `Polynomial.Chebyshev.T_iterate_derivative_mem_span_T`, a Chebyshev derivative
  membership assertion, not this theorem.
- `msearch.py ... grep 'nakayama|Nakayama|span.*iterate|iterate.*span'
  LinearAlgebra`: zero matches in Mathlib's linear algebra directory.
- `rg -n 'dilat.*[Ww]eight|[Ww]eight.*[Nn]akayama|semilinear.*weight'`
  separately over `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: zero matches. Searching the exact node id in
  `lean/WeilConjectures` also returned no matches.
- The broader `nakayama|Nakayama|dilating|span.*iterate|iterate.*span` search in
  both project source roots returned ordinary Nakayama and unrelated iterated
  constructions; the narrower semilinear-weight search above found no match.
- The proposed declaration name
  `span_iterates_eq_top_of_dilating_weights` has no match in Mathlib, either
  project source root, or the upstream declaration index.

Validation: prescribed `scompile.py Q84 lem-sfb-dilating-weight-nakayama`
compiled the delivered module in sandbox mode and at its library module name,
both in 1.0 seconds, with no errors or unexpected warnings. All universes and
variables are explicitly bound. There are no disputed statements or node faults.

## Second reading by Q84

No independent second worker was started: the dispatcher explicitly requires a
single worker to deliver directly, with the maintainer's independent review.
I re-read the node and the completed file against the correspondence above;
the integer factor, internality, zero summand, arbitrary coefficient
endomorphism, homogeneous finite family, actual quotient span and all iterates
are present. No mismatch or statement change was found.
