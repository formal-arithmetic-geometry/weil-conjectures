## Worker report

The module `Sheaf.CategoryTheory.HomotopyPrecompositionEquivalence` states
`SSet.Enhanced.homotopy_precomposition_equivalence` with `sorry`. Its two real-data helpers
are `homotopyPrecomposition` and `homotopyPrecompositionEdge`, both listed in the node's
`lean.declarations`. They implement the specific evaluation construction in the node; no
arbitrary transformation, equivalence, or chosen inverse replaces that construction.
The only change to the node is its `lean` field. There are no new nodes, dependency repairs,
statement changes, or disputed statements.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Small simplicial sets X,Y: `{X Y : SSet.{u}}`. There is no quasicategory or nonemptiness
  instance on either. The universe `u` is the node's common containing universe, arbitrary
  and large enough to hold the chosen objects, rather than a fixed minimum universe.
- Simplicial maps a,b and homotopy H: `(a b : X ⟶ Y) (H : X ⊗ Δ[1] ⟶ Y)`.
  Mathlib's cartesian tensor is the degreewise product in the node.
- H restricts to a at 0: `h₀` composes H with the product pairing of `𝟙 X` and the
  constant map to vertex `stdSimplex.obj₀Equiv.symm 0` of the interval, and asserts equality
  to a as an entire simplicial map.
- H restricts to b at 1: `h₁` uses the same pairing with vertex 1 and asserts equality to b.
- Every vertex track is degenerate: `hvertex` quantifies over every `x : X _⦋0⦌` and asserts
  that `H.app _ (X.σ 0 x, yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))` equals `Y.σ 0 y` for some
  `y : Y _⦋0⦌`. These are exactly the constant X-edge at x and the identity edge of the
  interval. The existential permits every degenerate edge and requires no arbitrary chosen
  track. The endpoint equations force y to be both a(x) and b(x).
- Every target quasicategory in the common containing universe:
  `(E : SSet.{u}) [Quasicategory E]`. Mathlib's internal Hom remains in SSet.{u}, so the
  iterated functor objects also use that universe. There is no cardinal bound or finiteness
  assumption on E, X, Y, D, or T.
- D and T are precisely `(ihom Y).obj E` and `(ihom X).obj E`.
- The specified map Φ_H is `homotopyPrecomposition H E`. Before its first curry, the nested
  `lift` sends `(x,(f,t))` to `(H(x,t),f)` in `Y ⊗ D`. Composing with `(ihom.ev Y).app E`
  is internal evaluation. Currying in X gives `D ⊗ Δ[1] ⟶ T`, as required.
- The specified adjoint edge is `homotopyPrecompositionEdge H E`, defined as
  `yonedaEquiv (MonoidalClosed.curry (homotopyPrecomposition H E))`. The second curry is
  in D, so it is a map `Δ[1] ⟶ Fun(D,T)` before Yoneda identifies it with an edge.
- The claimed source is a*: the first conjunct says the edge's face δ1 is
  `diagramVertex ((MonoidalClosed.pre a).app E)`; `pre` is Mathlib's internal-Hom
  precomposition. This identifies the endpoint on every simplex, rather than only vertices.
- The claimed target is b*: the second conjunct is the corresponding δ0 equation for b.
- The coherent natural equivalence assertion is the last conjunct, `IsEquivalenceEdge`
  in `Fun(D,T)` applied to this very edge. No existentially unspecified natural equivalence
  or ordinary homotopy-category isomorphism is substituted.

Dependencies read and used:

- `def-cbc-enhanced-diagrams-cones`,
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsEquivalenceEdge` and
  `SSet.Enhanced.diagramVertex`. Its full statement, lean record, and module were read;
  its evaluation and natural-equivalence definitions confirm the same conventions.
- `lem-cbc-internal-hom-quasicategory` is a Mathlib leaf whose recorded match is
  `SSet.instQuasicategoryObjIhom` in
  `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`.
  The source instance asserts `[Quasicategory X] → Quasicategory ((ihom A).obj X)`
  for any `A : SSet.{u}`. Imported as a proof dependency.
- `lem-coef-infinity-pointwise-equivalences`,
  `Sheaf.CategoryTheory.PointwiseEquivalences`: `SSet.Enhanced.pointwise_equivalences`.
  The source theorem and its proof docstring were read. It tests equivalence of an edge
  with specified diagram endpoints on every vertex of an arbitrary small shape.
  Imported as a proof dependency for the two applications described in this theorem's
  five-step deferred proof docstring.
- Mathlib primitives reused directly: `SSet`, `Quasicategory`, `stdSimplex`, `SSet.const`,
  `SSet.yonedaEquiv`, `ihom`, `ihom.ev`, `MonoidalClosed.curry`, `MonoidalClosed.pre`,
  `CartesianMonoidalCategory.lift`, `fst`, and `snd`. The signatures/docstrings of curry,
  pre, const, and yonedaEquiv were read. There is no duplicate internal-Hom construction.

Source checked: [Kerodon Theorem the project server, Tag 01DK](https://kerodon.net/tag/01DK), read
online on 2026-10-17. Its pointwise natural-isomorphism criterion is applied first with
shape X and target E and then with shape Fun(Y,E) and target Fun(X,E), exactly as the
node's proof specifies. The node already records the archive as WANTED.

Edge cases checked by reading the constructions and hypotheses:

- X empty: `hvertex` is vacuous and Fun(X,E) is terminal; the specified transformation
  still exists and is an equivalence. No `Nonempty` binder excludes it.
- Y empty: a and b can exist only when X is empty; the statement still includes this case.
- E empty: the empty simplicial set is a quasicategory. If Y is inhabited then D is empty
  and the second vertex test is vacuous; if Y is empty, so is X and both functor objects
  are terminal. No E-vertex is selected by a helper.
- X=Δ[0]: the hypothesis is exactly that the tracked edge in Y is degenerate; evaluation
  carries it to a degenerate equivalence. Constant H and a=b are admitted.
- Necessity of the vertex condition: for X=Δ[0], Y=E=N([1]), H the noninvertible arrow,
  its image under the identity diagram gives a nonequivalence component, so the condition
  has genuine mathematical content. Endpoint hypotheses likewise constrain H on all
  simplices and are not automatic.

Searches performed through `msearch.py Q81 lem-coef-infinity-homotopy-precomp-equivalence`:

- LeanFinder: `A vertex-fixed simplicial homotopy induces a coherent natural equivalence
  between precomposition maps of internal functor quasicategories`: eight hits, including
  `SSet.Truncated.HomotopyCategory.mkNatTrans`, `mkNatIso`, and truncated left/right
  homotopy conversions. None states the equivalence of the specified edge in the iterated
  internal Hom. Read HomotopyCat.lean:385-443: the constructors concern ordinary functors
  from a homotopy category and ordinary natural transformations/isomorphisms.
- Loogle: `"Quasicategory", "homotopy"`: zero hits.
- Mathlib grep: `precomp|[Hh]omotopy|[Ee]quivalence` under
  `AlgebraicTopology/Quasicategory`: eight hits in StrictBicategory and TwoTruncated.
  Read StrictBicategory.lean:14-32: it uses homotopy categories and explicitly lists
  identification with interval homotopies as future work; it does not supply this result.
- LeanSearch: `A simplicial homotopy constant at every vertex gives an equivalence edge
  between precomposition functors`: eight hits, including
  `SSet.RelativeMorphism.Homotopy.precomp`, `SSet.const`, model-category homotopy
  classes, and `SSet.hoFunctor.unitHomEquiv`. Read RelativeMorphism.lean:139-166:
  precomp constructs a relative homotopy under composition, not this coherent equivalence.
- `rg` in upstream `WeilConjectures`, side `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id and candidate names `homotopyPrecomposition`,
  `homotopy_precomposition_equivalence`: no declaration match. `grep -rn` of the item id
  in upstream `WeilConjectures`: no match.
- `rg` for `homotopy.*[Pp]recomp|[Pp]recomp.*[Hh]omotopy|homotopyPrecomp` in upstream
  and side sources found generic weak-homotopy and chain-complex statements, but no exact
  construction/theorem here. The narrower search of the chosen full declaration names
  in Mathlib, upstream, and the side library returned no matches.

Validation: the required `scompile.py` invocation compiled this file both as a sandbox
file and under its library module name, with no errors or warnings (1.3 s and 1.4 s).

## Second reading by Q81

A separate second pass in this worker session reopened the node and the completed module;
no other worker or sub-agent was started, as the dispatcher brief forbids that. The
maintainer's independent reading follows delivery. This pass checked the two endpoint
indices (δ1 is source/0, δ0 is target/1), the input association X×(D×Δ1), the projection
pair `(H(x,t),f)`, and both currying domains, so the final predicate is on the requested
edge of Fun(D,T). It checked hvertex at the unique nondegenerate interval edge and found
that membership in the image of σ0 is expressed without any stronger choice of vertex.
The smallness, arbitrary shapes, quasicategory-only target, empty cases, and equality on
whole simplicial maps are all retained. No mismatch or change was found. Helpers are
real constructions, and the only postponed theorem is the item's own named theorem.
