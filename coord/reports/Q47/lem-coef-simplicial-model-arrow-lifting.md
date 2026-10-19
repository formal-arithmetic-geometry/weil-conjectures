## Worker report

The module `Sheaf.CategoryTheory.SimplicialModelArrowLifting` states
`SSet.Enhanced.simplicial_model_arrow_lifting`, with its sole proof `sorry`.
No definition or additional theorem is introduced. The natural-language node is unchanged.

Hypothesis and clause correspondence:

- The small simplicial-set category is `SSet.{u}`. Its ordinary nerve in an ambient universe
  is `largeNerve.{u + 1, u, v} SSet.{u}`. The category of small spaces is the recorded
  `CategoryTheory.Spaces.infinityCategory.{u}`, lifted degreewise by
  `SSet.uliftFunctor.{v}` to `max (u + 1) v`. This is universe transport of the stipulated
  category, rather than a change of its objects or a restriction on the size of `E`.
- The stipulated passage to homotopy type is the coherent functor `j`, with `hj :
  IsLocalization (fun _ _ f ↦ IsWeakHomotopyEquivalence f) j`. The weak equivalences are
  precisely the recorded realization-based weak homotopy equivalences, and localization
  tests entire coherent functor categories.
- The arbitrary infinity category and coherent functor are `(E : SSet.{max (u + 1) v})
  [Quasicategory E]` and `p : E ⟶ SSet.uliftFunctor.{v}.obj Spaces.infinityCategory.{u}`.
  The independent universe `v` permits larger ambient categories without increasing the
  universe of the endpoint models. There is no Cartesian-fibration assumption.
- The pullback is the ALREADY LANDED general construction `chainTwoGluing j p`.
  Despite its historical name, its signature is unrestricted in its three simplicial sets.
  Its definition is exactly `(N(sSet) × E) ×_(S × S) Eq(S)`, with `Eq(S)` the full
  subcomplex `equivalenceDiagrams Δ[1] S`. It retains all parameter transformations.
  `chainTwoGluingLeft j p` and `chainTwoGluingRight j p` are the actual projections.
- An arrow `F : A → B` is a vertex `F : (mappingSpace E A B) _⦋0⦌` of the recorded
  right-pinched mapping space. Quantifying `A,B,F` covers every edge with its endpoints.
- The small Kan models and actual simplicial map are the existential `K L : SSet.{u}`,
  `KanComplex K`, `KanComplex L`, and `f : K ⟶ L`.
- The lifted arrow is `e : (chainTwoGluing j p) _⦋1⦌`. Its first projection is specified
  by the literal equality to `ULift.up (ComposableArrows.mk₁ f)`. Consequently its endpoint
  first coordinates are exactly `K,L`.
- The equivalences `α : jK ≃ pA` and `β : jL ≃ pB` are retained data in the two vertices
  of `e`: applying `chainTwoGluingPath j p` gives the coherent square, whose endpoint rows
  lie in `equivalenceDiagrams Δ[1] S`. The pullback equations identify their endpoints
  with the `j` and `p` images. They are not replaced by mere existence of unrelated models.
- The component condition is expressed by `G : (mappingSpace E A B) _⦋0⦌`, the equation
  `(chainTwoGluingRight j p).app _ e = G.1`, and `SSet.π₀.mk G = SSet.π₀.mk F`.
  This keeps exactly the requested component condition instead of requiring equality
  with the particular representative `F`.
- Essential surjectivity of `Fun(Δ¹,r)` is the second conjunct: for every edge `F` of `E`,
  there is an edge `e` of the pullback and an `EquivalentObjects` witness in
  `((ihom Δ[1]).obj E)` between the image diagram and `F`. `yonedaEquiv.symm` turns an
  edge into its coherent interval diagram and `diagramVertex` into the corresponding
  arrow-category object. This is equivalence in the entire coherent arrow category,
  not merely equality of components in the underlying category of objects.

Dependency declarations used, read with their signatures and docstrings:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.mappingSpace`,
  `IsWeakHomotopyEquivalence`, `diagramVertex`, `equivalenceDiagrams`, and the underlying
  equivalence/full-subcomplex definitions. Mathlib supplies `Quasicategory`, `KanComplex`,
  the internal hom, `nerve`, `ComposableArrows.mk₁`, `SSet.π₀.mk` and `yonedaEquiv`.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`: `CategoryTheory.Spaces.infinityCategory`,
  whose definition is the coherent nerve of the enriched category of all small Kan complexes.
- `Sheaf.CategoryTheory.FiniteReedyLocalization`: `HomotopicalAlgebra.FiniteReedy.largeNerve`,
  `IsLocalization` and `EquivalentObjects`. The owning landed definition node
  `def-coef-coherent-localization-interface` is added to `stmt_deps`.
- `Sheaf.CategoryTheory.ComposableBimoduleOperadSegal`: `SSet.Enhanced.chainTwoGluing`,
  `chainTwoGluingLeft`, `chainTwoGluingRight` (and its path coordinate read for the review).
  The owning landed node `lem-coef-composable-bimodule-operad-segal` is added to `stmt_deps`.
  Its theorem is not used as an assumption: these helpers have unrestricted generic signatures.
  A DAG closure check confirms neither added node depends on this item.

Proof-only imports are the stated nodes `lem-coef-kan-quillen-right-proper`,
`lem-coef-cosimplicial-frame-mapping`, and `lem-coef-infinity-pinch-comparison`.
The remaining proof dependency `lem-coef-accessible-pullback-filtered-colimit` has no
recorded declaration or Mathlib match; no module is imported for it. The source lookup
for the expected module also reports unavailable. The present statement needs only the
already published concrete pullback construction, not that unstated general theorem.
The docstring records every proof step, including the inner 3-horn construction of the square.

Edge cases checked before writing: empty `K,L` satisfy the intended positive-dimensional
Kan condition; there is no `Nonempty`, `Inhabited`, or nonzero condition on either model.
If `pB` is empty, existence of the original arrow forces `pA` to be empty, and the empty
simplicial map is permitted. Empty `E` makes the arrow quantifications vacuous. Degenerate
arrows and identity equivalences are included. Arbitrary ambient `v` does not force site
or model universes equal. The pullback is formed using equivalence arrows rather than all
arrows, and retains the coherent square in every degree.

Searches made:

- `msearch.py`, LeanFinder: “Every arrow of an infinity category over spaces lifts through
  the homotopy pullback along simplicial sets with Kan endpoint models”. Eight hits,
  including Joyal-trick lifting and `SSet.Truncated.HomotopyCategory.morphismPropertyHomMk`;
  none has the coherent pullback and Kan endpoint assertion.
- `msearch.py`, Loogle: `SSet.KanComplex, CategoryTheory.nerve`. No hits.
- `msearch.py`, LeanSearch: “Every arrow over spaces is represented by a simplicial map
  between Kan complexes in an infinity categorical pullback”. Eight hits, principally
  ordinary Cech nerves; none is this assertion.
- `msearch.py`, Mathlib grep, AlgebraicTopology:
  `arrow.*(lift|represent)|homotopyPullback|equivalencePullback`. Three ordinary
  model-category/nerve-adjunction hits, none matching this theorem.
- `rg` in upstream `WeilConjectures`: simplicial arrow/model/lifting patterns, and
  `grep -rn` for the exact node id: no matching assertion.
- `rg` in `lean/Sheaf/CategoryTheory`: pullback, equivalence-arrow, localization and
  essential-surjectivity patterns. Found and read `chainTwoGluing` and its projections;
  reused them rather than introducing another construction. Also read the localization,
  mapping-space, category-of-spaces and frame interfaces.
- `tools/blueprint_refs.py search 'equivalence-arrow pullback'`: no blueprint node title
  match. `ancestor` reports `prop-coef-integral-exceptional-adjoint`.
- Opened the source paper online, Theorem 5.3.17 and its proof. The source motivates the
  localization comparison; the node explicitly labels arrow representation an agent
  consequence, rather than claiming it is a separately numbered source theorem.

No statement correction, disputed statement, new node, or dependency repair is needed.
The only added dependencies are already landed owning nodes for definitions actually used.

## Second reading by Q47

Author's self-check only; no independent worker was launched, as the dispatcher brief
forbids it. The maintainer's independent review remains the independent reading.
Reopened the node and final Lean signature and checked every clause above. In particular,
the first conjunct uses equality of components of the specified mapping space, while the
second uses an actual equivalence in the coherent arrow category. Endpoint equivalences
are carried by the literal pullback vertices, and `K,L` remain in universe `u`. No new
hypothesis, nonemptiness condition, weaker category, or arbitrary replacement map was found.

Validation: `scompile.py Q47 lem-coef-simplicial-model-arrow-lifting` checked the delivered
file successfully, both as its sandbox file and its library module. No errors or warnings
were printed. The JSON changes only `lean` and adds the two landed owning nodes to
`stmt_deps`; its recorded signature is copied verbatim from the source. Every Lean line
is at most 100 characters and every universe and variable is explicitly bound.
