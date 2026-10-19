## Worker report

Item: lem-coef-infinity-edge-pullback-mapping-fiber. The module
`Sheaf.CategoryTheory.EdgePullbackMappingFiber` states
`SSet.Enhanced.edge_pullback_mapping_fiber`, with one postponed proof (`sorry`).
All other declarations are genuine data constructions or proposition definitions belonging
to this same node. No new DAG notion, dependency repair or statement correction is needed.

Hypotheses and objects, clause by clause:

- Simplicial sets are Mathlib `SSet.{u}` in the fixed common small universe of the
  definition dependency. `p : E ⟶ B`, `[InnerFibration p]`, `[Quasicategory E]`, and
  `[Quasicategory B]` are exactly the stated inner fibration of quasicategories.
- An edge, including a degenerate one, is `f : Δ[1] ⟶ B`. Its source and target are
  the images under `f` of `stdSimplex.obj₀Equiv.symm 0` and `... 1`.
- The actual edge pullback is Mathlib `pullback p f`, with `pullback.fst p f` as `j`
  and `pullback.snd p f` as `p_f`. Both projections are used, not arbitrary maps.
- `EdgePullbackFrame.K` is any `SSet.{u}`, without a quasicategory, nonemptiness,
  or finiteness condition. `A,Z` are vertices in `Fun(K,E_f)`. The frame's `source`
  and `target` equations require their entire projections to be the constant zero
  and one diagrams. These are precisely the original diagrams in `E_b,E_s`:
  factor a diagram into the zero/one fiber through the pullback, and conversely use
  the projection to `E` with its constant-base equation. There is no extra choice or
  hypothesis; this is the pullback-universal-property presentation of the same data.
  Vertices of the internal hom are diagrams by the dependency's `diagramVertex`
  equivalence. Using vertices also avoids adding irrelevant endpoint transport lemmas.

Conclusions:

1. The first five conjuncts assert innerness of `p_K`, quasicategoricity of both
   functor objects, of `E_f`, and of `Fun(K,E_f)`. The existential isomorphism `d`
   identifies `Fun(K,E_f)` with `pullback ((ihom K).map p) ((ihom K).map f)`;
   its two projection equations fix the canonical identification. The latter is
   the node's degreewise equality, expressed as the canonical simplicial isomorphism
   rather than literal equality of chosen implementations of limits.
2. `∀ n, Nonempty (Unique (F.interval.obj n))` says exactly one simplex in each
   degree of the interval mapping space. The frame equations identify its endpoints
   with `Δ_K 0, Δ_K 1`. `IsComparison` fixes the underlying simplex of `v` as
   `(constantDiagrams K B).app _ (yonedaEquiv f)`, namely `Δ_K f`. The conjunct
   after `IsComparison` states that applying `(ihom K).map f` to every interval
   mapping simplex is exactly the corresponding degeneracy of `v` (using
   `SSet.const v`). Equality of underlying simplices is equality in the mapping
   subtypes; it retains all degrees, not only components or vertices.
3. `F.total` and `F.base` are the two right-pinched mapping spaces, and `F.pi`
   is exactly `mappingSpaceMap ((ihom K).map p)` on their actual endpoints.
   The endpoint images equal `Δ_K b, Δ_K s` by the pullback and frame equations.
   The three `KanComplex` conjuncts cover the edge-pullback mapping space and both
   relative mapping spaces; `modelCategoryQuillen.J.rlp F.pi` is the Kan fibration
   condition (all horns of positive dimension, including the two outer horns).
   `e : F.domain ≅ fiber F.pi v` is the strict-fiber simplicial isomorphism.
   Its projection to the total mapping space is required to equal `F.forget`,
   the recorded `mappingSpaceMap F.inclusion F.A F.Z`. Thus it is induced by `j`.
   The existing `fiber` convention orders the point factor first, so the inclusion
   is `pullback.snd`, as in the defining dependency.
   `c` lands in the dependency's actual `homotopyFiber F.pi v`. In every degree its
   first coordinate is `F.forget` and its path coordinate is the constant path at
   `v`. These coordinates uniquely determine `c`: it is precisely `e.hom` followed
   by the constant-path inclusion. `IsWeakHomotopyEquivalence c` uses the recorded
   realization-based predicate, not a new notion of equivalence.
4. `RestrictionNatural` quantifies over every `a : G.K ⟶ F.K`, including maps
   involving empty indexing sets, and every other comparison with the same canonical
   coordinate formulas. The maps `r,t,b` are specified degreewise as actual internal
   hom restriction on the edge-pullback, total and base mapping spaces; `s` is their
   strict-fiber restriction and `h` applies restriction to the map and path coordinates.
   It asserts `b(v)=w` and both commuting squares `e.hom ≫ s = r ≫ d.hom` and
   `c ≫ h = r ≫ c'`. Taking the map from `K` to `Δ[0]` gives compatibility with
   `Δ_K`, since precomposition of a point diagram is the constant-diagram map.
   `CoherentNatural v c` expresses the chosen-witness convention from the node:
   for every parameter simplicial set `T`, every higher simplex dimension `r` and
   every monotone zero-one word `word : Δ[r] ⟶ Δ[1]`, an enhanced witness with
   that base word has image under `j` over `word ≫ f`. For every simplex of such
   a witness and every ordinal restriction `a : [n+1] → [r]` which is a mapping
   simplex `q`, its comparison has the restricted `j` image, lies over the prescribed
   degeneracy of `v`, and keeps its path coordinate constant. The words `001` and
   `011` give the precomposition and postcomposition triangles, respectively.
   All words and ordinal restrictions include their higher supplied witnesses.
   This describes coherent composition via the recorded triangle-and-restriction
   convention, with the image triangle used as the chosen composite downstairs;
   it does not impose a functor-independent strict choice of composition.

The final individual-object assertion is the `K=Δ[0]` instance. The internal-hom
unit isomorphism identifies its diagrams with objects and its postcomposition with `p`.
No cartesian or cocartesian edge, nor a lift of `f`, occurs in the hypotheses.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.mappingSpace`,
  `mappingSpaceMap`, `constantDiagrams`, `homotopyFiber`, and
  `IsWeakHomotopyEquivalence`, together with Mathlib `ihom`, `SSet.const`,
  `Quasicategory`, `KanComplex` and standard simplices. The path coordinates use
  exactly `homotopyFiber = comma ... true`, including paths directed to the vertex.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`, the currently
  recorded module of def-coef-infinity-fibrations, publicly reexports
  `Sheaf.CategoryTheory.InfinityFibrations`: `SSet.InnerFibration` and
  `SSet.Enhanced.fiber` (the latter is explicitly used in the statement).
- `Sheaf.CategoryTheory.InfinityMappingComposition`: `triangleFiber`,
  `triangleEdgePair`, `triangleLongEdge`, `MappingCompositionStatement`,
  `mapping_composition`. The full signatures and proof docstrings were read;
  the coherent-witness clause uses its convention of restricting supplied triangles.
- Proof imports: `SSet.innerAnodyneExtensions_pushoutObjObjι'` from Mathlib's
  `AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`;
  `SSet.Enhanced.innerFibration_mappingSpaceMap_isKanFibration` from
  `Sheaf.CategoryTheory.InnerMappingFiber`;
  `SSet.Enhanced.kan_pullback_path_comparison` from
  `Sheaf.AlgebraicTopology.KanPullbackPathComparison`;
  `SSet.Enhanced.right_pinch_comparison` from
  `Sheaf.CategoryTheory.RightPinchComparison`. These are all the proof dependencies
  with recorded declarations; none creates an import cycle.

Sources: downloaded the cited HTT PDF into the sandbox and read the proof of
Proposition the project server, printed pp. 265–266, Corollary the project server (p. 101), and Lemma
the project server (p. 130). The first is the edge-pullback reduction motivating this node;
this is the agent-added supporting lemma described by the existing DAG record,
not a claim that HTT prints this exact four-clause statement. The node's nine-step
proof is carried into the sole theorem docstring, including the canonical strict
fiber inverse, constant-path comparison, restriction formulas and higher words.
No source or node fault was found, and no statement is disputed.

Edge cases checked before and during drafting:

- Empty `K`: all diagram sets and the interval mapping set are terminal; no
  `Nonempty K` assumption appears and restriction quantifies over empty sets.
- Degenerate `f`: the two interval labels remain distinct coordinates even if their
  images coincide; no condition `b ≠ s` or nondegeneracy is used.
- Empty relative mapping fiber: `e` may identify two empty simplicial sets, and the
  path comparison is still well typed. No vertex is chosen in `F.domain`.
- Empty `E` with nonempty `K`: no fiber diagrams exist, as in the original hypotheses;
  empty `K` still permits the unique diagrams. No condition excludes either case.
- `p=id`, and `K=Δ[0]`: the strict fiber is respectively the specified base edge and
  the ordinary objectwise mapping fiber. Taking the unique indexing map to a point
  gives the constant-diagram case, rather than assuming it as extra data.
- Universes and all binders are explicit; `set_option autoImplicit false` is present.

Searches for an existing complete statement (raw service logs in sandbox searches.jsonl):

- LeanFinder, “For an inner fibration of quasicategories the mapping space in the
  pullback along an edge is the fiber of the induced map on mapping spaces naturally
  for diagrams”: eight hits, including `HasFibers.pullbackMap`, the simplicial Kan
  fibration horn instance, `fibrations_eq`, finite pullback and general path-object
  results. None is this right-pinched edge-pullback statement.
- Loogle, `SSet.InnerFibration, SSet.mappingSpace, pullback`: no match; unknown
  identifier `SSet.mappingSpace` (the right-pinched definition is project-local).
- LeanSearch, “quasicategory pullback along an edge mapping space fiber”: eight
  ordinary chosen-pullback / over-category hits, no quasicategory comparison.
- msearch grep, `edgePullback|edge_pullback|mappingSpace` in Mathlib
  `AlgebraicTopology`: zero hits. Direct reading also found the known inner-exponentiation
  instance in `AnodyneExtensions/Inner/PushoutProduct.lean`, only part (1).
- Direct `rg` over the upstream `WeilConjectures` sources for the item id and
  `edgePullback|edge_pullback|mappingFiber|mapping_fiber|RightPinch|rightPinch`:
  no upstream match for this statement. Searches in `lean/Sheaf` found the existing
  right-pinch, cartesian mapping-fiber and right-fibration morphism-space modules.
  These require extra edge/fibration data or assert different comparisons, so are
  not the current statement. Those notions and the current recorded dependency
  declarations are reused, rather than copied.
- Searched the exact proposed declaration and helper names in `lean/Sheaf`,
  upstream sources and `dag/lean_names_upstream.json`: no collision.

Validation: scompile.py compiled the delivered file cleanly both as a sandbox file
and under its actual module name (1.6 s / 1.8 s); no errors or unexpected warnings.
Only the item theorem has a postponed proof. No test theorem, axiom, private notation
or file-local instance is left in the module.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
