## Worker report

The module `lean/Sheaf/AlgebraicTopology/NondegenerateSimplexFacePoset.lean`
states `SSet.nondegenerate_simplex_face_poset`.  It uses Mathlib's canonical
`SSet.S` representation of all simplices and `SSet.N` representation of
nondegenerate simplices.  A displayed subtype of ordinal maps with the equation
`X.map f.op y.simplex = x.simplex` is exactly the hom-set of the ordinary
simplex category (the map is the monotone operator in the node's statement).
The theorem has no proof beyond the required `sorry`.

The hypothesis `[X.Nonsingular]` is Mathlib's class saying that every
nondegenerate simplex map is a monomorphism.  The five conclusion clauses render
the node as follows.

* For `x y : X.N`, `Subsingleton {f : [x.dim] ⟶ [y.dim] // ...}` says that
  there is at most one morphism between any two nondegenerate simplices.
* For every such `f`, `Mono f.1` says its monotone operator is injective.
* `IsPartialOrder X.N (fun x y => Nonempty {f // ...})` says that existence of
  a morphism is reflexive, transitive, and antisymmetric on the actual
  nondegenerate simplex objects.
* For every `σ : X.S`, the sigma-type `p : Σ r, X.nonDegenerate r ×
  ([σ.dim] ⟶ [r])` and the predicate `Epi p.2.2 ∧ X.map p.2.2.op
  p.2.1.1 = σ.simplex` state the existence and uniqueness of the
  nondegenerate simplex and surjective monotone operator in the decomposition
  `σ = barσ Δ(sσ)`.  `Epi` on `SimplexCategory` is precisely surjectivity of
  the ordinal map.
* For a simplex `σ`, a nondegenerate target `τ`, and any arrow `α` represented
  by the displayed subtype, `∃! t` with `α.1 = σ.toNπ ≫ t.1` is the required
  unique factorization through the canonical degeneracy map `σ.toNπ`; the
  source factor is `σ.toN` and the target factor is an arrow between
  nondegenerate simplices.  The preceding injectivity clause applies to `t`.

The statement dependency `def-cbc-enhanced-diagrams-cones` is imported from
`Sheaf.CategoryTheory.EnhancedDiagramsCones`; its canonical simplicial-set,
standard-simplex, and ordinary-nerve primitives are used by the node's setup.
The decomposition dependency is Mathlib's `SSet.S.toN`, `SSet.S.toNπ`,
`SSet.S.existsUnique_toNπ`, and `SSet.unique_nonDegenerate_*` API from
`Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices` and
`Mathlib.AlgebraicTopology.SimplicialSet.Degenerate`.  The proof dependency
`lem-weil-pbc-simplex-degeneracy-factorization` is represented by Mathlib's
`SimplexCategory.eq_σ_comp_of_not_injective'`, imported privately from
`Mathlib.AlgebraicTopology.SimplexCategory.Basic`.

Edge cases checked before writing were the empty simplicial set (all quantified
families are empty and the implication remains valid), a 0-simplex (every
operator from `[0]` is injective), a degenerate simplex over a vertex (the
canonical `toNπ` is the unique surjection), and a nondegenerate input (the
canonical surjection is an isomorphism).  The hypothesis is necessary: a
simplicial set with two distinct vertices identified by a nondegenerate
1-simplex gives non-unique face operators when the monomorphism condition is
removed.  The factorization subtype keeps the source and target dimensions
explicit, so no universe or empty-index case is lost.

Searches for an existing declaration were made as required:

* `msearch.py ... leanfinder "nondegenerate simplex face category is a poset with unique factorization"` returned Mathlib's `SSet.N.instPartialOrder`, `SSet.N.le_iff_exists_mono`, and related individual lemmas, but no full factorization theorem.
* `msearch.py ... loogle "SSet.Nonsingular, SSet.N.existsUnique_of_le, SSet.S.toNπ"` returned no hits.
* `msearch.py ... grep "nondegenerate_simplex_face_poset|existsUnique_toNπ|simplexCategory" Mathlib/AlgebraicTopology/SimplicialSet` returned no direct theorem matching this conjunction.
* `rg` over `WeilConjectures/` and the project's `lean/Sheaf/` found no declaration named
  `nondegenerate_simplex_face_poset`; the only related declaration is the separate
  `SSet.simplexCategory` construction, which does not state this result.

No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by Q127

I reread the node and the module signature clause by clause.  The hypothesis is
exactly the nonsingularity/monomorphism condition.  The first three conjunctions
match thinness, injective face operators, and the partial order induced by arrow
existence.  The sigma-type decomposition includes both the nondegenerate core
and the surjective operator with its defining simplicial equation.  The final
subtype quantifies every arrow into a nondegenerate target and states existence
and uniqueness of the factor through `toNπ`, with composition in the same order
as `α = t ∘ sσ`.  No extra finiteness, nonemptiness, or dimension hypothesis was
introduced, and no clause of the node was omitted.
