## Worker report

The module `Sheaf.Paper.ComponentLiftBaseChange` states
`AlgebraicGeometry.ProEtale.component_lift_base_change`, with `sorry` as its only
postponed proof. It adds three public helpers belonging to this same comparison:
`relativeComponentLift`, `relativeComponentCoordinate`, and `affineComponentMap`.
All three have actual data and source/blueprint docstrings. No statement correction,
new DAG node, or dependency repair is needed.

Source read: Hemo--Richarz--Scholbach, *Constructible sheaves on schemes*, PDF
pp. 8--9, the paragraph defining the affine-transition limit immediately before
(4.1), and Corollary 4.4(2). In particular, this paragraph explicitly states that
the functor on profinite component spaces preserves limits. The node's five proof
steps expand the natural base-change comparison using the geometric description
and stalkwise lifting. All five steps are carried into the theorem docstring.

Hypotheses and clauses, in node order:

* Arbitrary morphism of affine schemes: the single existential family `c` is
  indexed by `{X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)`.
  Each subsequent clause binds the same hypotheses explicitly. No condition on f
  other than being a scheme morphism occurs.
* Actual component spaces with quotient topology: `affineComponentSpace X` and
  `affineComponentSpace Y` are the dependency's bundled `ConnectedComponents`.
  `affineComponentMap f` bundles Mathlib's
  `f.continuous.connectedComponentsMap`; its value on a quotient representative
  is definitionally `ConnectedComponents.mk (f y)`.
* Compatible universes: `universe u`; schemes and profinite spaces use u, with
  cofiltered presentation indices `I : Type u` and `[SmallCategory I]`. Slice
  categories inherit their object and morphism sizes from these categories.
  There is no additional bound, nonempty-object assumption or universe equality.
* The relative lift is the existing characterized construction:
  `relativeComponentLift T` is the functor witness from
  `component_relative_profinite_site T`, followed by `Scheme.ProEt.forget T`.
  `relativeComponentCoordinate` takes the coordinate of that same witness.
  This is permitted choice from a universal-property characterization, which
  determines the functor and coordinate up to the unique compatible natural
  isomorphism. It does not choose an arbitrary object from a bare existence
  statement. The source theorem supplies the finite clopen stages and preservation
  of every cofiltered finite-stage presentation for precisely this witness.
* Canonical isomorphisms of Y-schemes: `c f` has type
  `relativeComponentLift X ⋙ Over.pullback f ≅
   Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y`.
  All components are isomorphisms in `Over Y`, hence preserve the Y projection.
  Mathlib `Over.pullback f` chooses the product `X_E ×_X Y`; the existing
  `pullbackSymmetry` identifies it with the node's `Y ×_X X_E`, with its two
  projections exchanged. The profinite slice pullback similarly orders its
  factors E then Q, canonically the same as Q then E. No alternative product
  notion is defined.
* Preservation of E coordinate: the first conjunct projects the output
  `relativeComponentCoordinate Y` by profinite `pullback.fst` and equates it to
  `relativeComponentCoordinate X` applied to scheme `pullback.fst` on the input.
  Together with being a Y-scheme map this characterizes the canonical comparison.
* Naturality in every continuous E-map: `c f` is a `NatIso` on the entire profinite
  slice, so its hom naturality is exactly the desired equation for every morphism
  over P, with no factorization hypothesis.
* Identity normalization: the second conjunct gives a slice isomorphism `e`
  from pullback along `affineComponentMap (𝟙 X)` to E, fixes its underlying map
  to `pullback.fst`, and equates `c (𝟙 X)` followed by the lift of e to
  `Over.pullbackId`. This handles the literal quotient map and all chosen
  pullback identifications without relying on definitional equality.
* Composition normalization: for f and g the third conjunct supplies the
  profinite associativity isomorphism e. Its two projection equations determine
  it canonically. The displayed comparison equation uses `Over.pullbackComp g f`,
  the pullback of `c f` along g, and `c g`, and identifies their composite with
  `c (g ≫ f)` followed by the lift of e. Thus one family satisfies both equations
  simultaneously, rather than choosing unrelated pairwise isomorphisms.
* Finite clopen stages: A and C are `FintypeCat`, q is a surjective finite quotient,
  and r is the map of finite sets used in the dependency's `componentFiniteStage`.
  The existential cofan j has domain the actual
  `Over.mk (componentFiniteOpen X A C q r a).ι`, its coordinate has label a, all
  its legs are open immersions, and it is a colimit. After base change, its legs
  followed by `c f` are open immersions forming a colimit of the target lift.
  The explicit range equation identifies each such leg with the inverse image
  of `componentFiniteOpen Y A C (affineComponentMap f ≫ q) r a`, exactly the
  part Y corresponding to h^{-1}(U_a). No surjectivity is assumed for h or h ≫ q;
  this includes empty pulled-back parts. The cofan and coordinate identify the
  restriction on each individual summand, including repeated labels.
* Every cofiltered finite-stage presentation: the last conjunct universally
  quantifies D and its cone s with `∀ i, IsComponentFiniteStage (D.obj i)` and
  `IsLimit s`. Both mapped cones are limiting. For every leg `s.π.app i` the
  equality of its two composites with c is written explicitly. This is exactly
  the normalized cone compatibility for any presentation, not only a preferred
  presentation. The pulled-back presentation is handled by the second composite
  functor, with no assumption that the scheme pullback's topology itself is a
  topological pullback.
* The concluding natural isomorphism of the two functors is the same `c f`
  already quantified, carrying all the normalizations. Henselian, w-local,
  w-contractible, surjectivity of f, and nonemptiness hypotheses are absent.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
* `Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite`:
  `spectralSpace_connectedComponents_profinite`, via the relative-site import.
* `def-weil-size-convention`: recorded metatheoretic convention; rendered by
  explicit universes, not an invented Lean object or import.
* `Sheaf.Paper.ComponentRelativeProfiniteSite`:
  `AlgebraicGeometry.ProEtale.affineComponentSpace`, `componentFiniteStage`,
  `IsComponentFiniteStage`, `componentFiniteOpen`, `componentFiniteScheme`, and
  `component_relative_profinite_site`. The theorem's full signature and its
  universal property and finite-stage clauses were read before using its witness.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, and `pullbackSymmetry`, through the
  existing dependency imports. `Mathlib.CategoryTheory.Comma.Over.Pullback`
  provides `Over.pullback`, `Over.pullbackId`, and `Over.pullbackComp`; all were
  read, in particular the factor ordering and associativity orientation.
* Proof dependency `Sheaf.AlgebraicGeometry.StalkIsomorphismLifting`:
  `AlgebraicGeometry.Scheme.existsUnique_lift_of_stalkMap_isIso`, imported plainly.
* Proof Mathlib matches: `AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion`,
  `AlgebraicGeometry.Scheme.Pullback.range_map` from
  `Mathlib.AlgebraicGeometry.PullbackCarrier`, and
  `CategoryTheory.FinitaryPreExtensive.isUniversal_finiteCoproducts` from
  `Mathlib.CategoryTheory.Extensive`, imported plainly. Their signatures were read.
* `lem-sfb-relative-component-lift-pullback-space` has no Lean attachment in the
  supplied DAG and no module is imported for it. It is a proof-only dependency,
  and the theorem docstring retains its role. The statement itself uses the
  recorded relative-site universal property, so no missing object has been
  replaced or given a private duplicate.

Edge cases checked before statement drafting: E empty; X empty (forcing Y and E
empty); Y empty without requiring X empty; empty A, repeated clopen blocks,
empty inverse-image blocks when h misses a component; identity morphisms and
arbitrary composite morphisms; general continuous profinite maps that do not
factor through a finite stage; arbitrary small cofiltered categories and their
presentations. Slice isomorphisms and limit properties cover these cases without
selecting points or assuming object nonemptiness. The `IsCofiltered` index
condition is the source's presentation condition, not an extra scheme hypothesis.

Searches made:

* `msearch.py`, leanfinder: "Base change of affine relative component lift along
  arbitrary morphism of affine schemes is naturally isomorphic to pullback of
  profinite spaces". Eight hits, involving general affine transition limits,
  open-cover affine refinement and affine-space base change; none states this
  comparison or its normalizations.
* `msearch.py`, loogle: `Profinite, AlgebraicGeometry.Scheme`. Zero hits.
* `msearch.py`, grep under AlgebraicGeometry:
  `(component|profinite).*(baseChange|base_change|pullback)`. One hit,
  `Mathlib/AlgebraicGeometry/Geometrically/Reduced.lean:118`, about reducedness
  under flat base change; not a match. Exact wrapper output is also preserved
  by `searches.jsonl` in the sandbox.
* `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for component/profinite
  base-change and pullback terminology, then `affineComponentSpace` and all four
  proposed declaration names. Existing relative-site and affine component-site
  constructions were found and read; there is no declaration of this comparison.
  Exact node-id search in `lean/WeilConjectures` returned no match. Proposed public
  names were also searched in Mathlib and had no matches.

The first compilation exposed a bundling issue: `CompHausLike.ofHom` tried to
synthesize unbundled quotient Hausdorff instances. Using `ConcreteCategory.ofHom`
with the already bundled `affineComponentSpace` objects fixes it without adding
hypotheses or changing universes. The module was compiled cleanly through
`scompile.py` after this repair, then its finite-summand range and cone equations
were expanded explicitly and submitted for a fresh compile. No mathematical
statement discrepancy or STATEMENT-DISPUTED issue was found.

## Second reading by Q118

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
