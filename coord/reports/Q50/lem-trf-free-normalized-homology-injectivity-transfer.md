## Worker report

The module `Sheaf.AlgebraicTopology.FreeNormalizedHomologyInjectivityTransfer`
states `AlgebraicTopology.freeNormalizedHomologyInjectivityTransfer`, with a single
`sorry` proof. It states both the explicit generator lifts and the consequent
injectivity transfer. No definitions, helper theorems, new nodes, dependency
repairs, or statement corrections are needed. The node changes only in `lean`.

Source read: `literature/stacks-project/simplicial.tex`, Tag 08P2,
`lemma-homotopy-equivalence`, especially lines 5935–5958. Stacks uses the
lower-face normalization and final face differential. The node uses the mirrored
higher-face normalization and zeroth face differential; Mathlib's Moore complex
uses exactly the node's convention. The source's bijectivity hypothesis supplies
injectivity in this paragraph; its argument uses only that injectivity, as the
node states. No mathematical fault or disputed statement was found.

The correspondence for every hypothesis, construction and conclusion is:

- Simplicial abelian groups `X,Y`: `{X Y : SimplicialObject AddCommGrpCat.{u}}`.
  The universe `u` is arbitrary. An additive simplicial morphism is `f : X ⟶ Y`,
  a natural transformation whose components are abelian-group homomorphisms.
- The underlying simplicial set `UZ` is `Z ⋙ forget AddCommGrpCat`, a functor
  from the simplex category opposite to types, precisely the abbreviation `SSet`.
  The degreewise free construction `F(S)` is `S ⋙ AddCommGrpCat.free`.
  The source of `AddCommGrpCat.free` was read: its objects are
  `AddCommGrpCat.of (FreeAbelianGroup α)` and its map is
  `AddCommGrpCat.ofHom (FreeAbelianGroup.map f)`. Thus all simplicial operators
  send the basis vector `[s]` to `[S(φ)(s)]`, exactly as required.
- `F(Uf)` is `Functor.whiskerRight f
  (forget AddCommGrpCat ⋙ AddCommGrpCat.free)`. Its component is the free
  homomorphism on the underlying function of `f.app`, with no arbitrary map.
- Evaluation `ε_Z` is Mathlib's canonical free-forgetful adjunction counit.
  Its degree `n` component is `AddCommGrpCat.adj.counit.app (Z _⦋n⦌)`.
  Reading the adjunction's `FreeAbelianGroup.lift` hom-equivalence shows it
  sends `[z]` to `z` and therefore a finite integral sum to its evaluation.
  The degreewise family is natural by the counit's naturality, whiskered by `Z`.
- `N(Z)` is `AlgebraicTopology.NormalizedMooreComplex.obj Z`, and its term
  of degree `n` is `(obj Z).X n`. This is the underlying object of `objX Z n`.
  Reading `objX` verifies that degree zero is top and positive degrees are
  exactly the finite intersection of kernels of faces `k.succ`.
  `(objX Z n).arrow` is the canonical monomorphism into `Z_n`; it is essential
  because a categorical subobject's chosen representative need not be a literal
  subtype. This does not replace the normalization by another construction.
- The positive-degree differential is `objD Z n : N(Z)_(n+1) ⟶ N(Z)_n`,
  induced by face zero. `(obj Z).d n (n - 1)` is the outgoing differential,
  with degree zero equal to `.d 0 0 = 0` by `ComplexShape.down ℕ`.
  `NormalizedMooreComplex.map f` is the canonical restriction chain map.
- The fixed degree `n ≥ 0` is the unrestricted binder `(n : ℕ)`.
  The first conjunct quantifies over every normalized
  `x : (obj X).X n` and `y : (obj Y).X (n + 1)`.
  The cycle hypothesis is `(obj X).d n (n - 1) x = 0`.
  The boundary hypothesis is `objD Y n y =
  (NormalizedMooreComplex.map f).f n x`. Composing with the canonical
  inclusion gives precisely `d₀ y = f_n(x)`; conversely the inclusion is mono.
- Membership of the first specified lift is expressed by an element `xt` of
  `(obj (X ⋙ forget AddCommGrpCat ⋙ AddCommGrpCat.free)).X n` and the equation
  `(objX (...) n).arrow xt = FreeAbelianGroup.of ((objX X n).arrow x)
  - FreeAbelianGroup.of 0`. This is exactly `[x] - [0_n]`, not just an
  unspecified preimage. The canonical arrow is mono, so its witness is unique.
- The next conjunct asserts the outgoing differential of `xt` is zero,
  including degree zero. Thus the specified lift is a normalized cycle.
- Membership of the second specified lift is the analogous element `yt` in
  the normalized free target in degree `n+1` with inclusion equal to
  `FreeAbelianGroup.of ((objX Y (n+1)).arrow y) - FreeAbelianGroup.of 0`.
  This is exactly `[y] - [0_(n+1)]`.
- Its boundary equation is `objD (...) n yt =
  (NormalizedMooreComplex.map (Functor.whiskerRight f (...))).f n xt`.
  Thus its boundary is precisely the normalized restriction of `F(Uf)_n`
  applied to the specified first lift, as the node requires.
- The last lift clause applies `AddCommGrpCat.adj.counit.app (X _⦋n⦌)`
  to the ambient image of `xt` and sets it equal to `(objX X n).arrow x`.
  This is exactly `ε_X(xt) = x` in the ambient simplicial group.
- The second top-level conjunct is the implication between two
  `Function.Injective` assertions. The maps are obtained by applying
  `HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n`
  to, respectively, `NormalizedMooreComplex.map (Functor.whiskerRight f (...))`
  and `NormalizedMooreComplex.map f`. These are the canonical maps
  `H_n(N(F(Uf)))` and `H_n(N(f))` of the node, not arbitrary maps or
  quasi-isomorphism hypotheses. Mathlib homology in an abelian category is
  the quotient of cycles by boundaries, so it gives the stated homology groups.
  The implication has no dependence on a chosen `x,y`; lifts are the independent
  first conjunct, not additional assumptions for homology injectivity.

Dependency declarations used:

- `def-weil-pbc-simplicial-object`: its recorded
  `Mathlib.AlgebraicTopology.SimplicialObject.Basic`,
  `CategoryTheory.SimplicialObject`, with morphisms natural transformations.
  The full signatures and docstrings of its `δ` and `σ` were also read.
  This module is publicly imported by `Mathlib.AlgebraicTopology.MooreComplex`.
- `def-weil-pbc-simplicial-set`: its Mathlib match `SSet` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic` is definitionally
  `SimplicialObject (Type u)`, used here through functor composition with the
  forgetful functor. The match's degeneracy, subcomplex, and finiteness
  declarations were read; those further clauses are not needed in this lemma.
- `Mathlib.AlgebraicTopology.MooreComplex`: `NormalizedMooreComplex.objX`,
  `objD`, `obj`, and `map` are used directly; no normalization is copied.
- `Mathlib.Algebra.Category.Grp.Adjunctions`: `AddCommGrpCat.free`,
  `AddCommGrpCat.adj`, and `FreeAbelianGroup.of` implement the free construction
  and evaluation. `Mathlib.Algebra.Category.Grp.Abelian` supplies the standard
  abelian structure needed to form normalized complexes and homology.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.homologyFunctor` gives the canonical homology maps.

Edge cases checked before and after writing:

- `n = 0`: `objX X 0 = ⊤`, the outgoing `.d 0 0` is zero, `objD Y 0`
  is the degree-one differential. No negative-degree group or face occurs.
- `x = 0` or `y = 0`: the corresponding difference of basis vectors is zero;
  the evaluation and boundary formulas agree. In particular `[0]` itself is
  not incorrectly identified with zero in the free abelian group.
- Constant simplicial abelian groups: higher normalized groups vanish and
  degree-zero normalized homology is the original group. The result reduces
  to the fact that injectivity of the free map forces injectivity of the map.
- The zero morphism from a nonzero constant group to zero fails the degree-zero
  free-homology injectivity hypothesis, as it should. Identity maps satisfy it.
- A generator difference is not additive as a function of `x`; the theorem
  asserts individual lifts, not a homomorphism sending `x` to `[x] - [0]`.
- Neither a boundary witness nor a homology injectivity assumption is imposed
  globally as extra data: the first clause is conditional on the stated cycle
  and boundary, and the second has exactly the node's homology implication.

Searches for an existing statement:

- `msearch.py`, LeanFinder: “If homology of the free abelian simplicial map is
  injective then normalized homology of the original simplicial abelian map
  is injective”. Eight results, including `normalizedMooreComplex`, its map
  formula, the mono inclusion into the alternating complex, and group-homology
  chain-map injectivity. None states the lift formulas or injectivity transfer.
- `msearch.py`, Loogle: `AlgebraicTopology.normalizedMooreComplex,
  AddCommGrpCat.free, SSet.freeAbelian`. Zero results; `SSet.freeAbelian`
  is unknown. The actual free functor was then found and read in
  `Algebra/Category/Grp/Adjunctions.lean`.
- `msearch.py`, grep in `AlgebraicTopology`:
  `normalizedMooreComplex|NormalizedMooreComplex|freeAbelian`. Twenty-five
  results, all the normalized construction and its Dold–Kan comparisons,
  not this theorem. The full MooreComplex source was read.
- `msearch.py`, LeanSearch: “injectivity on homology of simplicial abelian
  group from degreewise free underlying abelian group normalized Moore
  complex”. Eight results on the normalized Moore functor, Dold–Kan, and
  its subobjects and inclusion. None states this result.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `normalizedMooreComplex|NormalizedMooreComplex|freeNormalized|free_normalized|normalized.*[Ii]njectiv`:
  no matching result; the last pattern returned unrelated normalized derived
  comparisons. A focused search for `FreeAbelianGroup` and `AddCommGrpCat.free`
  in both algebraic-topology directories found only the unrelated
  `FreeBisimplexProjectiveResolutions` definition. Searching the item ID in
  `lean/WeilConjectures` returned no result. Searching the chosen theorem name
  and possible helper name `freeUnderlyingSimplicialAbelian` across Mathlib,
  `lean/Sheaf`, and `lean/WeilConjectures` returned no declaration.

Validation: `scompile.py Q50 lem-trf-free-normalized-homology-injectivity-transfer`
compiled the single delivered file in sandbox and actual library module mode,
cleanly with no warnings (1.4 s and 1.5 s). An initial compile found that
`Functor.whiskerRight` and `HomologicalComplex.homologyFunctor` needed their
namespace qualifiers; both were corrected before this clean compile.

## Second reading by Q50

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
