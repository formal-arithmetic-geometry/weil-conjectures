## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSourceUnramifiedBaseOpen` states
`AlgebraicGeometry.AlgebraicSpace.exists_openSubspace_universal_unramified_of_closed_source`.
Its sole theorem has proof `sorry`; no definition or theorem proof is supplied.
The source read was `literature/stacks-project/spaces-more-morphisms.tex`, Tag 05X8,
`lemma-where-unramified`, statement and entire proof (lines 11528–11563).
The DAG statement agrees with that source, including mere closedness of p.
No statement correction or disputed mathematical assertion is needed.

Clause-by-clause correspondence:

- The base scheme S and size convention are `{S : Scheme.{u}}` with explicit `universe u`.
  All test spaces are in the same universe as the existing algebraic-space framework;
  the underlying point quotients live in `Type (u + 1)` as their recorded definition does.
- The spaces A, C, B over S are `(A C B : AlgebraicSpace S)`, using the recorded full
  subcategory of fppf sheaves, not scheme-only or representable-map specializations.
- The three maps are `(p : A ⟶ B) (q : C ⟶ B) (u : A ⟶ C)` and the commuting triangle
  is `(w : u ≫ q = p)`. Category composition has the order corresponding to q composed u.
- Local finite type of p is `hp_lft : MapIsLocally (@LocallyOfFiniteType) p`.
  Unfolding the shared chart test quantifies over every pair of compatible representable
  etale scheme charts and imposes exactly the recorded scheme local finite type property.
- Closedness of the original point map is `hp_closed : IsClosedMap (mapPoint p.hom.hom)`.
  This sends every closed subset to a closed subset in the recorded final/atlas topology;
  it does not impose universal closedness.
- Existence of the parameter open is `∃ W : OpenSubspace B`. The recorded definition
  is a subfunctor with inclusion representable by scheme open immersions.
- Every B' and every g are tested in `∀ (B' : AlgebraicSpace S) (g : B' ⟶ B)`.
  Factorization is `∃ l : B'.obj.obj ⟶ W.val.toFunctor, l ≫ W.val.ι = g.hom.hom`.
  As open subfunctors are algebraic spaces and morphisms are natural transformations,
  this is precisely factorization as an algebraic-space morphism.
- The biconditional's right side is `MapIsLocally (@AlgebraicGeometry.IsUnramified)`
  on the canonical induced map. Its source is the sheaf pullback `pullback p.hom g.hom`
  and target `pullback q.hom g.hom`, each bundled as an algebraic space using
  `(fibreProduct_isAlgebraicSpace ...).1`. The map is `pullback.map` with components
  `u.hom`, the identity of B', and the identity of B. Its commuting-square proof is
  exactly the projection of w to sheaf morphisms. Thus the map sends (a,b') to (u(a),b').
  The generic chart test uses the recorded `AlgebraicGeometry.IsUnramified`, which is
  `LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)`. No representability
  assumption on u is introduced. This also unfolds to the existing
  `SpaceChartwiseUnramified` predicate from `SpaceUniversalConormal.lean`; no new
  predicate or private copy of it is defined here.
- The scheme-base clause quantifies over every `(T : Over S)` and every representing
  isomorphism `(e : B.obj.obj ≅ yoneda.obj T)`. It produces `(V : Over S) (j : V ⟶ T)`
  with `IsOpenImmersion j.left`, and an actual isomorphism
  `eW : W.val.toFunctor ≅ yoneda.obj V`. The equation
  `W.val.ι ≫ e.hom = eW.hom ≫ yoneda.map j` identifies the inclusion with that open
  immersion, so it asserts an open subscheme of the specified scheme base.
- No binder assumes flatness, quasi-compactness, separation, representability of the
  diagram maps, or a stack structure.

Recorded dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsEtale`, `IsRepresentableWith`, full signatures
  and docstrings. The size-convention node is metatheoretic and supplies no extra object.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, whose first clause is the closure witness used twice.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  `PointRepresentative.map`, `pointImage`. Its transitive point-class definitions were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`.
  The already landed node `def-sfb-space-morphism-properties` is added to stmt_deps
  for this existing shared definition, as authorized by the standing brief's landed-node
  rule. Its imports also expose `ProperCurveModuli.mapPoint` (full signature and
  representative-level construction read) and the canonical point topology.

The stated proof dependencies `AlgebraicSpaceEtaleOpenImage`,
`AlgebraicSpaceOpenFactorSchemeTests`, and `AlgebraicSpacePointOpenCalculus` are plain
proof imports; their declarations are read against the proof steps reproduced in the
new theorem docstring. The two proof nodes `lem-sfb-space-lft-cancellation` and
`lem-sfb-space-unramified-locus-base-change` have no Lean record yet, so there is no
module to import for them. They are not prerequisites to typing this statement.

Edge cases checked mathematically before writing:

- If A is empty, the bad locus is empty and W is all of B. The theorem permits this;
  the pullback map has empty source and is unramified.
- If B is empty, the diagram has empty sources and the unique empty open works.
- If B' is empty, it factors through every open and its induced source is empty.
- Taking g to be the identity recovers the original unramifiedness test.
- If u is an isomorphism, every base change is unramified, so W is all of B.
- Nonreduced scheme tests and arbitrary maps g are retained: the statement imposes no
  etale, flat, reduced, or finite-type restriction on g.
- The scheme-base clause covers every representing isomorphism, not an arbitrary
  additional scheme model chosen independently of B or of W's inclusion.

Searches actually run:

- `msearch.py ... leanfinder`: “For maps of algebraic spaces A to C over B with A to B
  closed and locally of finite type there is a universal open in B where A to C is
  unramified”. Eight results: ring unramified locus, scheme formal unramifiedness,
  etale cancellation, and universally open maps; no universal parameter-open theorem.
- `msearch.py ... leansearch`: “A closed locally finite type map A to B and a map A to C
  over B have an open universal parameter locus where the base changed map A to C is
  unramified”. Eight results, including `Algebra.isOpen_unramifiedLocus`, scheme
  formal-unramified instances, and algebra base change; no exact match.
- `msearch.py ... loogle '"unramifiedLocus"'`: six results, all ring-theoretic source
  loci; none is the parameter locus in the node.
- `msearch.py ... grep 'unramified.*[Oo]pen|[Cc]losed.*[Uu]nramified|where_unramified'
  AlgebraicGeometry`: four scheme formal-unramified/diagonal results, no exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node id, universal/closed
  unramified-open phrases, local-finite-type predicates, and unramified definitions:
  no exact theorem. Nearby `UniversalUnramifiedRadicialOpen` adds radiciality and has
  scheme-only data; `AlgebraicSpaceUniversalIsomorphismOpen` concerns isomorphisms and
  stronger diagram hypotheses. Neither can be attached to this node. The search found
  the shared `MapIsLocally`, the scheme `IsUnramified`, and the already compatible
  `SpaceChartwiseUnramified` definition, which were inspected rather than duplicated.
- The prescribed recursive node-id grep of `lean/WeilConjectures` found no declaration.
- Current blueprint `literature/blueprint/latest` was searched for this node and the
  Stacks label/tag; the exact source is the Stacks statement cited by the DAG.

Validation: the delivered module compiled through the prescribed `scompile.py Q14
lem-sfb-space-closed-source-unramified-base-open <file>` in both sandbox and library
modes (1.8 seconds each), with no errors or warnings reported. `autoImplicit` is false,
all variables/universes are explicit, and maximum Lean line width is 87 characters.

## Second reading by Q14

This is the dispatcher's worker's second pass, not a claim of a separate agent review;
the brief explicitly forbids starting other agents and provides the maintainer's
independent delivery review. With the DAG, Stacks 05X8 and final Lean file open, I
matched the base and three spaces, all three morphisms, w, local finite type of p,
closedness of p, the existential open, both directions for every g, and the scheme-base
clause to the signature above. The two identities in `pullback.map` keep the same B'
and B as the node; w gives the sole nontrivial square. Neither q nor g acquires any
extra hypothesis. The chart property is the full scheme unramified conjunction, not
formal unramifiedness alone. The explicit representing isomorphism and inclusion equation
prevent the scheme-base clause from merely asserting an unrelated representation.
No mismatch was found; no source statement or hypothesis was changed. The only DAG
addition is the already landed owner of the shared chart-test interface.
