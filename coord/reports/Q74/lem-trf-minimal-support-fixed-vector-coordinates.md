## Worker report

The module `Sheaf.LinearAlgebra.MinimalSupportFixedVectorCoordinates` states
`Module.Free.exists_minimal_support_fixed_vector_coordinates`. Its sole proof is
`sorry`; it introduces no definitions. The node is unchanged except for `lean`.
The source read was `literature/stacks-project/algebra.tex`, Tag 0592,
`lemma-projective-freeness-criteria`, the first two proof paragraphs and the
coefficient comparison in the last paragraph. The node isolates the linear-algebra
part of that proof, valid for any endomorphism fixing the vector.

Hypothesis and clause correspondence:

- A commutative ring is `{R : Type u} [CommRing R]`.
- The free module is `{F : Type v} [AddCommGroup F] [Module R F]
  [Module.Free R F]`; there is no finite-generation hypothesis.
- The nonzero element is `(x : F) (hx : x ≠ 0)`.
- The linear endomorphism and fixed-vector hypothesis are `(π : F →ₗ[R] F)`
  and `(hπ : π x = x)`; no idempotence or local-ring hypothesis is imposed.
- A basis is the existential `(ι : Type v) (B : Module.Basis ι R F)`.
- The positive integer is `(n : ℕ)` together with `1 ≤ n`.
- The selected distinct basis vectors are `B (e i)` for `(e : Fin n → ι)`;
  `Function.Injective (fun i ↦ B (e i))` expresses their distinctness directly.
- The coefficients are `(a : Fin n → R)` with `∀ i, a i ≠ 0`.
- The first expansion is `x = ∑ i : Fin n, a i • B (e i)`.
- Support is precisely Mathlib's `(B.repr x).support`, the finitely supported
  coordinate representation. Its cardinality is `n` by
  `(B.repr x).support.card = n`. The next conjunct compares `n` to the support
  cardinality in every basis `C`, so the cardinality is attained and least.
- No basis is lost by taking index types in `Type v`: for a nontrivial ring a
  basis is injective and reindexes by its range, a subset of `F : Type v`,
  without changing support cardinality. Here `hx` forces the module and ring
  to be nontrivial. This is also the convention of `Module.Free.exists_basis`.
- Irredundancy is `∀ j : Fin n, ¬ ∃ c : Fin n → R,
  a j = ∑ i ∈ Finset.univ.erase j, a i * c i`. The unused value `c j` adds
  no restriction to the coefficients indexed by `i ≠ j`.
- The complement span `T` is written inline as
  `Submodule.span R (B '' (Set.range e)ᶜ)`. Since the basis is injective under
  `hx`, this image of the complementary indices is exactly the basis vectors
  other than the selected ones.
- The `y_i` are written inline as `π (B (e i))`, avoiding a second name for
  the same objects. The existential `b : Fin n → Fin n → R` gives `b_ij`,
  and `t : Fin n → F` with `∀ i, t i ∈ ...` gives elements of `T`.
- The image expansion is `∀ i, π (B (e i)) =
  (∑ j : Fin n, b i j • B (e j)) + t i`.
- The second vector expansion is `x = ∑ i : Fin n, a i • π (B (e i))`.
- The coefficient identities are `∀ j : Fin n,
  a j = ∑ i : Fin n, a i * b i j`; row and column order agree with the node.

Dependency used: `def-weil-pbc-free-module`, recorded as `Module.Free` in
`Mathlib.LinearAlgebra.FreeModule.Basic`. I read its full class signature and
docstring, its `exists_basis` field, `Free.exists_set`, `free_iff_set`, and
`Basis`/`Basis.repr` in `Mathlib.LinearAlgebra.Basis.Defs`. The public import
supplies the sole statement/proof dependency and the basis and span API.
No dependency repair or new node is needed.

Edge cases checked before writing: the zero module and the zero ring have no
`x ≠ 0`, so those instances are correctly covered by an impossible premise,
without an added `Nontrivial` assumption. Empty support would give `x = 0`,
explaining `1 ≤ n`. When `n = 1`, the excluded-index sum is empty and the
irredundancy clause is exactly nonzeroness of the sole coefficient. Infinite
bases are permitted and all coordinate and complement sums still have finite
support. No domain, locality, finite-rank, or projector condition is used.
Ring and module universes `u`, `v` are independent and explicitly bound.

Searches for an existing statement:

- `msearch.py` LeanFinder: "A free module over a commutative ring has a basis
  minimizing the support of a fixed vector with irredundant coefficients and
  coordinates of an endomorphism fixing it". Eight hits included
  `Module.Free.chooseBasis`, `Module.Free.exists_set`,
  `LinearMap.nilRankAux_basis_indep`, pairing bases over fields, and Smith
  normal form over PIDs. None states this result over arbitrary rings.
- `msearch.py` LeanSearch: "A vector in a free module admits a basis minimizing
  support and irredundant nonzero coordinates". Eight hits concern basis
  existence, `chooseBasis`, and free modules; no minimizing statement.
- `msearch.py` Loogle: `Module.Basis, Finsupp.support`. Six hits include
  `Module.Basis.mem_span_repr_support`,
  `Module.Basis.repr_support_subset_of_mem_span`, and
  `Module.Basis.mem_span_image`; these concern a fixed basis, not minimizing
  among bases and the fixed-endomorphism relations.
- `msearch.py` grep: `minimal.*support|support.*minimal|irredundant`, restricted
  to `LinearAlgebra`: zero hits.
- `rg` with the same pattern in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: unrelated support arguments, the consumer
  `ProjectiveElementFreeSummand`, the different flat Mittag-Leffler support
  lemma, and `LocalIrredundantRelationMatrix` (which takes irredundancy and
  relations as input). None supplies this statement.
- `rg` for the blueprint item id in `lean/WeilConjectures`: no match.
- `rg` for `exists_minimal_support_fixed_vector_coordinates` in Mathlib,
  `WeilConjectures`, `Sheaf`, and the upstream name index: no match.

Validation: `scompile.py Q74 lem-trf-minimal-support-fixed-vector-coordinates`
compiled both sandbox and library module successfully (1.4 s and 1.0 s), with
no errors or warnings. No statement dispute or node fault was found.

## Second reading by Q74

This is the assigned worker's separate rereading, not an independent agent review;
the dispatcher explicitly forbids starting another agent and assigns independent
review to the maintainer. With the node, source paragraph, and completed file open,
I checked the nonzero and fixed-vector premises, arbitrary commutative ring and
free module, positive support size, distinct vectors, nonzero coefficients,
both expansions of `x`, attained global minimality, every irredundancy condition,
the precise complementary span, every image expansion, and every column relation.
All are present. In particular `b i j` multiplies the `j`th basis vector in the
`i`th image, and the last equation sums over `i`, matching the source.
The index universe convention preserves all bases by reindexing their ranges;
there is no finite-generation restriction. No mismatch requiring a change was found.
