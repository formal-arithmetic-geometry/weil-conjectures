## Worker report

The module `lean/Sheaf/AlgebraicTopology/RealizationCWSubcomplex.lean` introduces the
canonical characteristic map `SSet.realizationCharacteristic`, the open barycentric
interior predicate `SSet.realizationInterior`, and the canonical map on standard
simplex realizations `SSet.realizationBarycentricMap`.  It states
`SSet.realization_cw_subcomplex` with proof `sorry`.

The theorem renders the node statement clause by clause:

* For each point `x : |K|`, the sigma type packages a degree, a nondegenerate
  simplex in `K`, and a point of `|Delta^n|` whose coordinates under
  `SimplexCategory.toTopHomeo` are all strictly positive; `ExistsUnique` asserts
  existence and uniqueness of the representative and the characteristic map sends
  it to `x`.
* The second conjunct gives a unique triple `(m, alpha, sigma)` for every simplex,
  with `Function.Surjective alpha.toOrderHom` expressing the order-preserving
  surjection, `sigma ∈ K.nonDegenerate m`, and `tau = K.map alpha.op sigma`.
* The third conjunct states `q_tau = q_sigma` composed with the canonical realization
  of `alpha` whenever `tau` is that degeneracy.
* The fourth conjunct states the coordinate formula for this canonical map: the
  `j`-coordinate is the finite sum over the fiber of `alpha`.
* The fifth conjunct gives the realization relation for every order-preserving map
  `beta : [m] -> [n]` and simplex `rho ∈ K_n`.
* The sixth conjunct is the quotient-topology closed-set criterion, quantified over
  every subset `B` and every characteristic simplex map.
* The final conjunct quantifies over every simplicial subcomplex `A`.  Its inclusion
  realization is the canonical map `SSet.toTop.map A.ι`, is an embedding with closed
  range, and its range is exactly the points having an interior nondegenerate
  representative in `A` (the stated `sigma.1 ∈ K.nonDegenerate n` condition).

The statement dependency is imported through the already landed module
`Sheaf.CategoryTheory.EnhancedDiagramsCones`; its realization convention uses
Mathlib's `SSet.toTop` directly. Its primary recorded declaration,
`SSet.Enhanced.coneCategory`, describes coherent cones and is not used as a
realization construction here. The nondegenerate decomposition is the Mathlib
leaf `SSet.exists_nonDegenerate` and uniqueness declarations in
`Mathlib.AlgebraicTopology.SimplicialSet.Degenerate` (the node
`lem-weil-pbc-simplicial-set-nondegenerate-decomposition` is a Mathlib-status
statement dependency in the source blueprint, but it is not in this item's
`stmt_deps`).

Edge cases checked while choosing the types include `n = 0` (the positivity
predicate has one coordinate), the empty simplicial set and empty subcomplex, and
`A = ⊤`; the sigma-type formulation does not add a nonemptiness assumption and the
closed-range clause permits an empty range.  The finite sums use the full finite
ordinal fibers, including empty fibers only where the source's order map permits
that coordinate; no index universe is introduced independently of `K`.

Searches recorded on the node were rerun/inspected: LeanSearch for a canonical CW
structure and for realization monomorphisms; LeanFinder for nondegenerate interior
representatives and closed realization embeddings; Loogle for `SSet.toTop` and the
simplicial primitives; and grep in `Mathlib/AlgebraicTopology` for realization,
nondegenerate, CW-complex, and closed-embedding declarations.  They returned only
`SSet.toTop`, standard simplex/horn/quasicategory/Kan primitives, and the
combinatorial `SSet.unique_nonDegenerate_*` results; no declaration states the full
point-representative, quotient-topology, and closed-subcomplex theorem, so no
existing attachment was used.

## Earlier second reading (a previous round; superseded)

I opened the node and module independently. The first conjunct binds an
arbitrary simplicial set and matches the unique nondegenerate interior
representative clause. The second uses `Surjective` on the order map and
`nonDegenerate` for the unique degeneracy decomposition. The third, fourth,
and fifth conjuncts state characteristic-map functoriality, the coordinate sum
formula, and the general realization relation. The sixth is the quotient
closed-set criterion. The final conjunct uses `K.Subcomplex`, whose closure
under faces and degeneracies is the simplicial-subset condition, and
`Topology.IsClosedEmbedding`, which is an embedding with closed range and
therefore gives the required homeomorphism onto a closed subset. Its range
existential restricts the representative simplex to `A`. No hypothesis or
clause is added or omitted; the empty simplicial set and empty/full
subcomplexes remain allowed.

## Second reading by NE

I read the shared node, its sandbox copy, the entire Lean module, the statement
dependency and its recorded source module, and the combinatorial decomposition
Mathlib leaf independently of the earlier reading. There is no repair note and
no `statement_change`. There are no new nodes or dependency modules in this
delivery, and no source-based correction to the node is needed.

Source verification: [Kerodon 0014](https://kerodon.net/tag/0014), Proposition
1.1.3.8, gives a unique factorization into a surjection and a nondegenerate
simplex for every simplicial set. [Kerodon 001X](https://kerodon.net/tag/001X),
the proof of Proposition 1.2.3.4 and Remarks 1.2.3.12 and 1.2.3.16, supplies
the nondegenerate cells and simplex-colimit topology. The paragraph before
Proposition 3.6.1.11 in [Kerodon 0130](https://kerodon.net/tag/0130) explicitly
asserts the closed-subset homeomorphism for every simplicial subset of an
arbitrary simplicial set; the surrounding discussion of finite simplicial
sets imposes no finiteness hypothesis on that paragraph. I also read Stacks
`simplicial.tex`, `lemma-splitting-simplicial-sets` (017R), including its proof.
These sources require no Kan, quasicategory, separation, or nonemptiness assumption.

Object, hypothesis, and conclusion checklist, in node order:

1. **Small simplicial set and its realization:** `(K : SSet.{u})` binds an
   arbitrary simplicial set in any universe `u`. Mathlib's notation `|K|`
   means `SSet.toTop.obj K`. In `SingularSet.lean`, `toTop` is the left Kan
   extension of the topological simplex functor, with `sSetTopAdj` its singular
   set adjunction. This is precisely the realization convention of
   `def-cbc-enhanced-diagrams-cones`, whose module explicitly uses that functor.
   Verdict: same object and topology, with no extra hypothesis. The dependency's
   primary record `SSet.Enhanced.coneCategory` is about cones; I checked its
   module's actual use of `SSet.toTop`, rather than confusing the primary name
   with the realization API.
2. **Continuous characteristic maps:** `realizationCharacteristic σ` is
   `SSet.toTop.map (SSet.yonedaEquiv.symm σ)`, of type
   `|SSet.stdSimplex.obj ⦋n⦌| ⟶ |K|`. Yoneda identifies `σ` with its canonical
   simplex morphism, and a `TopCat` morphism carries continuity. Verdict: exactly
   the specified characteristic map, with no arbitrary choice of map.
3. **Unique nondegenerate interior representatives and disjoint covering:**
   the first conjunct uses `∀ x : |K|, ∃! p, ... = x`. The sigma type includes
   the degree, a simplex with `σ ∈ K.nonDegenerate n`, and a simplex point
   satisfying `realizationInterior`. This predicate requires every coordinate
   under `SimplexCategory.toTopHomeo` to be strictly positive. That homeomorphism
   targets the real simplex with nonnegative coordinates summing to one.
   Unique existence in the dependent sigma type states uniqueness across
   degrees as well as uniqueness of the simplex and its interior point.
   It entails that these interior images cover and are pairwise disjoint;
   neither separate clauses nor a supplied CW structure are needed. Verdict: exact.
4. **Unique degeneracy decomposition:** for every `n` and `τ`, the second
   conjunct gives a unique triple `(m, α, σ)` with
   `Function.Surjective α.toOrderHom`, `σ ∈ K.nonDegenerate m`, and
   `τ = K.map α.op σ`. A simplex-category morphism is an order-preserving map;
   its underlying surjectivity is equivalent to Mathlib's `Epi` convention.
   I read all four declarations in the decomposition node's `mathlib_match`:
   `exists_nonDegenerate`, `unique_nonDegenerate_dim`,
   `unique_nonDegenerate_simplex`, and `unique_nonDegenerate_map`.
   Verdict: same objects, order of quantifiers, and all uniqueness clauses.
5. **Degeneracy identity and barycentric formula:** the third conjunct
   identifies the characteristic maps whenever `τ = K.map α.op σ`; the fourth
   states the coordinate sum over the fiber of `α` as a finite sum with zero
   outside the fiber. `realizationBarycentricMap α` is the realization of the
   canonical `SSet.stdSimplex.map α`. I checked
   `SimplexCategory.toTopHomeo_naturality_apply`, `SimplexCategory.toTop`, and
   `stdSimplex.map`: the coordinate convention is the pushforward of weights,
   with the direction and finite-ordinal sizes as stated. The third conjunct
   allows all order maps, but adds no strength to the whole theorem: that
   general identity is already explicitly required by the next node clause.
   Verdict: exact.
6. **General realization relation:** the fifth conjunct independently binds
   `ρ : K _⦋n⦌` and `β : ⦋m⦌ ⟶ ⦋n⦌`. It says
   `realizationCharacteristic (K.map β.op ρ) =
   realizationCharacteristic ρ ∘ realizationBarycentricMap β`.
   The fourth conjunct supplies its coordinate formula for every such `β`.
   Verdict: the domain and codomain degrees and all quantifiers agree.
7. **Quotient closed-set criterion:** the sixth conjunct quantifies over
   every `B : Set |K|` and gives an equivalence between `IsClosed B` and
   closed inverse images under every characteristic map, including those
   of degenerate simplices. Verdict: both directions and every summand are present.
8. **Simplicial subsets:** `A : K.Subcomplex` uses Mathlib's abbreviation
   for `Subfunctor K`, hence degreewise subsets stable under every simplicial
   operator. `A.toSSet` is its subtype-valued functor and `A.ι` its canonical
   inclusion. Stability under all operators is equivalent to the node's
   face-and-degeneracy stability. `K.nonDegenerate` is the complement of
   `K.degenerate`; `degenerate_eq_iUnion_range_σ` verifies exactly the
   node's "not in a degeneracy image" convention. Verdict: neither notion
   is replaced by an unrelated topological subcomplex or private definition.
9. **Homeomorphism onto a closed subset and exact image:** the last conjunct
   has `e = SSet.toTop.map A.ι`, fixing the inclusion-induced map.
   `Topology.IsClosedEmbedding e` extends `IsEmbedding e` by closedness of
   its range; an embedding is injective and induces the domain topology.
   This is equivalent to the required homeomorphism onto the closed range.
   The membership equivalence uses a simplex in `A.toSSet`, requires its
   underlying simplex to be nondegenerate in `K`, and a positive-coordinate
   point mapping to `x`. Together with unique normal forms this is exactly
   membership of the ambient nondegenerate representative in `A`.
   Verdict: all image and topology clauses are present and canonical.

Edge cases: the empty simplicial set has no realization points or simplices
requiring witnesses; no `Nonempty` instance is assumed. The empty subset has
empty closed range and the full subset has the full range. At `n = 0`,
`Fin (n + 1) = Fin 1`, the sole real coordinate is one, and every vertex is
nondegenerate by `nondegenerate_zero`. Arbitrary maps may have empty fibers,
whose coordinate sum is zero; surjections in the decomposition have nonempty
fibers. Boundary points are covered by lower-dimensional normal forms.
`universe u` is unrestricted; the real simplex is transported by the
standard `toTopHomeo`, with no imposed universe equality. There is no
coefficient ring, field, characteristic, scheme, or zero module in this node.
All binders are explicit under `autoImplicit false`.

Independent duplicate searches used `msearch.py` with LeanSearch for
"Points of the topological realization of a presheaf on the simplex category
are uniquely represented by a nondegenerate simplex with positive coordinates",
LeanFinder for "topological simplicial realization positive barycentric
coordinates simplex quotient topology", and Loogle for
`SSet.toTop, "IsClosedEmbedding"` (successful, zero hits). An earlier unquoted
Loogle query was invalid and was retried; no absence conclusion uses it.
The semantic results give `SSet.toTop`, the topological simplex, and the
combinatorial decomposition, not the full realization theorem. Local `rg`
searches for the three helper names and theorem name, `toTopHomeo`, barycentric
coordinates, and combinations of `toTop` with embedding or closedness covered
Mathlib's algebraic topology files, upstream `WeilConjectures`, the project's
`lean/Sheaf`, and the upstream name index. No duplicate declaration was found.
The existing primitives are used directly by the three helper constructions;
no second simplex, realization, nondegeneracy, or subcomplex notion is introduced.

Mismatches found and repaired: the three helper docstrings lacked source places
and blueprint identifiers (H8). The theorem docstring omitted most of the
node's seven-step proof, especially normalization invariance, the subcomplex
ancestor argument, and the closed-image induction (H8). I supplied these details,
added the standard copyright header, completed the module's source references,
and corrected the worker report's misleading description of `coneCategory`
as the realization declaration. There was no mismatch in the theorem signature,
and it was preserved. All three definitions contain actual canonical data;
the only postponed proof is the named theorem, whose proof remains `sorry`.
No target or dependency statement was changed.

Validation: `scompile.py NE lem-cbc-realization-cw-subcomplex` compiled the
module as a sandbox file and at its library module path, within the default
60-second per-file limit, without errors or warnings. The recorded
`lean.statement` was checked verbatim against the unchanged file signature.
