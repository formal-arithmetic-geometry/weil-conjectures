## Worker report

The module `Sheaf.LinearAlgebra.FieldCommonSection` states
`LinearMap.exists_common_section_of_surjective` with one `sorry` and no definitions.
The node's mathematical statement, dependency lists, and proof are unchanged.

Clause-by-clause correspondence:

- A field `k`: `(k : Type u) [Field k]`, for the explicitly declared universe `u`.
  This uses the `Field` declaration of `def-weil-field` in
  `Mathlib.Algebra.Field.Defs`, whose full signature and docstring were read.
- Nonnegative coordinate counts: `(m n : ℕ)` allows both counts to be zero.
- The concrete coordinate modules `k^{⊕n}` and `k^{⊕m}` are `Fin n → k` and
  `Fin m → k`, with Mathlib's componentwise module operations. For these finite
  index sets they are exactly the finite free modules in the statement, not
  arbitrary modules with a new choice of basis. `def-weil-pbc-free-module` records
  `Module.Free` in `Mathlib.LinearAlgebra.FreeModule.Basic`; that declaration and
  its basis-existence field were read and its module is publicly imported.
  No new freeness predicate or extra freeness assumption is introduced.
- The two given linear maps: `(a b : (Fin n → k) →ₗ[k] (Fin m → k))`.
- Their individual surjectivity: `(ha : Function.Surjective a)` and
  `(hb : Function.Surjective b)`.
- The required linear section: `∃ q : (Fin m → k) →ₗ[k] (Fin n → k), ...`.
- The first composite is the identity: `a.comp q = LinearMap.id`.
- The second composite is a linear isomorphism: `Function.Bijective (b.comp q)`.
  The composite already has a linear-map type; a bijective linear map has a
  linear inverse, so this states precisely invertibility of this composite.
- Arbitrary finite fields and empty coordinate sets remain included: there is
  no `Infinite k`, characteristic restriction, or positivity hypothesis.

The public imports supply the statement's field, free-module, coordinate-module,
linear-map and function predicates. The plain proof imports follow all three
recorded proof dependencies (their declarations and surrounding signatures were
read): `Submodule.exists_isCompl` in `Mathlib.LinearAlgebra.Basis.VectorSpace`,
`LinearMap.finrank_range_add_finrank_ker` in
`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`, and
`FiniteDimensional.nonempty_linearEquiv_of_finrank_eq` in
`Mathlib.LinearAlgebra.Dimension.Free`. The declaration docstring includes every
step of the DAG proof: kernel dimensions, intersection complements, the graph
of an isomorphism, an ambient complement, and inverse restriction.

The source was read directly at `literature/stacks-project/more-algebra.tex`,
Tag 0FJK, final paragraph of `lemma-homotopic-surjections`. It asserts a common
summand for the two surjections in the field case. Inverting the first restricted
map gives exactly the section formulation of this node. No source-based
correction or additional node is necessary.

Edge cases checked mathematically before writing:

- `m = 0`: the target is the zero space; the unique map from it is a section and
  its composite with `b` is the unique, bijective zero-space endomorphism.
- `n = 0`: surjectivity forces `m = 0`, since a field is nontrivial.
- `n = m`: both surjections are invertible and `q = a⁻¹` works.
- `a = b`: any right inverse of `a` works.
- Over `F₂`, for `n = 2`, `m = 1`, and the two different coordinate projections,
  `q(t) = (t,t)` works. The graph-complement proof uses subtraction without
  dividing by two, and hence includes characteristic two and all finite fields.
- No assertion that one can simultaneously make both composites the identity
  was added: only the first is prescribed to be the identity.

Searches for an existing statement (all with the prescribed `msearch.py Q15
lem-trf-field-common-section` wrapper, 2026-10-24):

- LeanFinder: "For two surjective linear maps a and b from k^n to k^m over any
  field, there is a linear map q with a composed q the identity and b composed
  q bijective". Eight hits, including
  `LinearMap.splittingOfFunOnFintypeSurjective_splits` and
  `LinearMap.exists_rightInverse_of_surjective`. These split one map and do not
  control the composite with a second map; no exact match.
- LeanSearch: "Two surjective linear maps from a finite dimensional vector space
  onto the same vector space admit a right inverse for the first whose composite
  with the second is bijective". Eight hits including individual right-inverse
  existence and injectivity/surjectivity equivalences; no common section result.
- Loogle: `LinearMap, Function.Surjective, Function.Bijective`. Eleven hits,
  including `OrzechProperty.bijective_of_surjective_endomorphism`, dimension
  comparisons, and exact-sequence lemmas. None constructs a common section.
- Mathlib grep: `common.*complement|exists.*isCompl.*isCompl|common.*[Ss]ection`
  in `LinearAlgebra`. Four hits: `Submodule.exists_isCompl` and three projection
  lemmas about a supplied complement; no simultaneous complement existence.
- `rg` with the same concept patterns across both `lean/WeilConjectures` and
  `lean/Sheaf`, followed by focused searches of their linear-algebra directories:
  unrelated common section/complement phrases only, no exact statement.
- `grep -rn 'lem-trf-field-common-section' lean/WeilConjectures`: no match.
- `rg 'exists_common_section_of_surjective|exists_common_section'` in Mathlib,
  both project roots, and `dag/lean_names_upstream.json`: no name collision.
- Read `Mathlib/LinearAlgebra/Finsupp/Pi.lean` lines 171–191: the existing
  splitting and its properties concern one surjection and do not satisfy this
  node's second composite clause.

Validation: the prescribed `scompile.py` wrapper completed successfully against
current server sources (8.0 seconds, 60-second limit, two threads). Its local
attempt reported `OSError(28, 'No space left on device')`; the wrapper's server
confirmation then succeeded with no errors or unexpected warnings.

No statement dispute or node fault found.

## Second reading by Q15

This is the dispatcher's single-worker delivery, with no additional agents
started. I reread the node and the completed Lean file as a separate comparison
pass; the maintainer's independent reading is still required. The explicitly
bound field and natural-number counts, concrete tuple modules, two linear maps,
and separate surjectivity hypotheses match the node. The existential reverses
the source and target of the original maps as required for a section. Its
conjunction specifies identity only for `a.comp q` and bijectivity only for
`b.comp q`; linearity is already part of the composite's type. Empty coordinates
and arbitrary fields are included. The proof docstring follows all five DAG
steps. No mismatch or correction was found in this rereading.
