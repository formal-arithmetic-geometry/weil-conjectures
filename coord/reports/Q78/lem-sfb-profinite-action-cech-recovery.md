## Worker report

The module `Sheaf.CategoryTheory.ProfiniteActionCechRecovery` states the complete
node as five named theorem statements in
`Profinite.CondensedAction.CechRecovery`, with every theorem proved by `sorry`.
Its four data declarations are actual constructions: `actionCover` is the
recorded continuous action map bundled as an equivariant map; `cechSpace`,
`cechFirst`, and `cechSecond` are the categorical pullback and its projections.
No definition selects an object from an existence theorem. The one proof needed
to bundle `actionCover` is separately named `actionCover_wellDefined` and is the
associativity/equivariance clause of this same node.

Only the node's `lean` record changes. No new nodes, dependency repairs, or
statement corrections are needed. The source remains honestly agent-formulated:
the current blueprint direct-image paragraph (3) supplies the route, not this
auxiliary theorem. Stacks Sites 00VM supplies exactly the sheaf equalizer used.
There is no claim of an external citation for the whole auxiliary result.

Hypotheses and clauses, matched with Lean:

- Compatible sizes and small models: explicit `universe u`, `J : Type u`, the
  existing `Base.{u}` and `Space J` (`AsSmall.{u+1}`), and sections in
  `Type (u+1)`. `set_option autoImplicit false` prevents unbound implicits.
  These are the exact common universes of the recorded dependencies.
- Compact Hausdorff totally disconnected topological group: `[Group J]`,
  `[TopologicalSpace J]`, `[IsTopologicalGroup J]`, `[CompactSpace J]`,
  `[T2Space J]`, and `[TotallyDisconnectedSpace J]`.
- P and P_J, their continuous maps and finite jointly surjective covers:
  existing `Base`, `Space J`, `baseCoverage`, and `coverage J`. The sheaf category
  is `Sheaf (coverage J).toGrothendieck (Type (u+1))`.
- H and t: existing `freeParameter J` and `trivialParameter J` are the small-model
  forms of the recorded parameter functors. The latter introduces no additional
  claim here. The actual free underlying space is J times the original parameter.
- Internal actions: existing `Actions J`, `groupPresheaf J`, and
  `InternalActionSite.setAction`. This is the existing category of internal
  modules over the represented group sheaf, not an ordinary-point action.
- h_T(S)=C(S,T) and its induced action: `h`, `hs`, and the two implications in
  `profiniteAction_cech_recovery` repeat exactly the represented sections,
  induced-map and pointwise-action normalizations of the dependency theorem.
  These are specifications of the functor named in the node, not added
  mathematical assumptions about F or X.
- Phi: the dependency's actual `phi J h hh`; `hh` is exactly the already asserted
  sheaf condition of `phiPresheaves J h`. G: an arbitrary `G : FreeRestriction J`,
  whose fields already specify its original sections, restrictions, actions and
  sheaf-map components. No equivalence is included in this interface.
- a_T(j,t)=jt and its singleton-cover property: `actionCover` uses precisely
  `(actionMap J T).down`; `actionCover_wellDefined` supplies equivariance;
  the first conjunct of `actionCover_cech` is
  `Presieve.singleton (actionCover J T) ∈ coverage J T`.
- Equivariant homeomorphism H(J times T) to H(T) times_T H(T): the `c` in
  `actionCover_cech` is an isomorphism in `Space J`, hence an actual continuous
  equivariant bijection with continuous equivariant inverse. Its source is
  `(freeParameter J).obj (productParameter J T)` and its target is the actual
  categorical pullback `cechSpace J T`.
- Forward coordinates ((j,kt),(jk,t)) and the two named projections: the two
  arrow equalities in `actionCover_cech` fix `c.hom` after each pullback projection
  as H(alpha_T) and `freeRightTranslation gamma` followed by H(pi_T).
  They determine the forward map by the pullback universal property and express
  exactly the two requested coordinate formulas, without assuming a particular
  implementation of the categorical pullback carrier.
- Inverse coordinates (j,j^-1*j',v): the final universally quantified equation
  of `actionCover_cech` gives the pointwise value of `(underlying J).map c.inv`.
  It reads j and (j',v) from the two projections, so covers every fibre-square
  point and specifies the stated inverse on the actual underlying space.
- F(a_T) is a bijection onto the equalizer: `actionCover_descent` is `Set.BijOn`
  from `Set.univ` onto `{x | IsEquivariantSection J (G.functor.obj F) T x}`.
  Its function is actual F(a_T), transported only by `(G.sections F).inv` to
  the existing realization of G(F)(T). Since `G.sections` is an isomorphism,
  this is precisely the requested bijection, including injectivity and the
  exact range. `IsEquivariantSection` is the dependency's equation on the full
  parameter J times T, with `actionMap`, `secondProjection`, and `groupProjection`.
- Eta:F to Phi G(F): the main theorem asserts the natural isomorphism
  `η : 𝟭 _ ≅ G.functor ⋙ phi J h hh`. Its first conjunct fixes each component
  under `identityEvaluation h hs` as F(a_T) transported by `G.sections.inv`.
  Thus it is exactly the inverse equivariant-Yoneda identification of the
  descent section, not an unnormalized isomorphism.
- Naturality for every equivariant u and the equality u a_T=a_T' H(u): this is
  `actionCover_naturality` (categorical composition is left to right). Eta's
  components are sheaf morphisms, so naturality holds for every map in `Space J`.
  Eta is itself a natural isomorphism of functors on sheaves, including all
  sheaf morphisms as requested.
- Epsilon:G Phi(X) to X: `ε : phi J h hh ⋙ G.functor ≅ 𝟭 (Actions J)` is a
  natural isomorphism in the category of internal actions. Its second conjunct
  fixes each component after `G.sections.hom` as the dependency's actual
  `freeEvaluation h hs X S`, evaluation at `(1,id_S)`. Its components are
  therefore natural in profinite parameters and equivariant, and the natural
  isomorphism is natural in equivariant sheaf morphisms X to Y.
- Evaluation intertwines Phi(X)(r_g) with the given action: the last conjunct
  spells out this exact equality, using `freeRightTranslation J S g.down` and
  `InternalActionSite.setAction`. The binder is every section
  `g : (groupPresheaf J).obj (op S)`, hence every continuous S to J, including
  nonconstant ones.

Dependency declarations read and reused:

- `def-weil-size-convention`: its record is a metatheoretic convention, with no
  object declaration; the universe binders above implement it.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` and its
  public coherent-profinite-site imports. No ring coefficient is added here.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; sheaves use its retained
  Mathlib `Sheaf` interface.
- `Sheaf.CategoryTheory.ProfiniteActionParameters`:
  `Profinite.ContinuousActionParameter.freeAction` and `trivialAction`, through
  the already published small-model functors.
- `Sheaf.CategoryTheory.ActionToposGeometricRestriction`:
  `CategoryTheory.InternalActionSite.SetActions` and `setAction`, read together
  with the recorded `geometricRestriction` interface. Its geometric equivalence
  theorem is not used to assume the result being stated.
- `Sheaf.CategoryTheory.ProfiniteActionYonedaFreeEvaluation`: its recorded
  `profiniteAction_yoneda_free_evaluation`, `base`, `productParameter`,
  `actionMap`, `secondProjection`, `groupProjection`, `IsEquivariantSection`,
  `phiPresheaves`, `phi`, `identityEvaluation`, `component`, `unitParameter`,
  and `freeEvaluation`. The actual signature and normalizations are reused.
- `Sheaf.CategoryTheory.ProfiniteActionFreeRestriction`: `FreeRestriction`,
  `freeRestriction_exists`, `freeRightTranslation`; its section and action
  normalizations are used exactly as recorded.
- The dependencies publicly reuse `ProfiniteActionCoherentPresentation`'s small
  site and represented group definitions. This module uses those definitions
  only; it never invokes its downstream presentation existence theorem or
  assumes `SetPresentation` with an equivalence.

Edge cases checked mathematically before writing and again against the final
signatures: empty T (the cover and fibre-square carrier are empty; F(empty) is
singleton), empty S (the evaluation and action equations remain valid), trivial J
(the cover is the identity up to the existing model identifications), non-free
T actions (a_T needs no equivariant section), and noncommutative J (the inverse
is j^-1*j' and right translation produces jk in the second projection).
Contravariance reverses composition in exactly the required order. Every equation
of internal sections is quantified over whole profinite parameters. Neither an
extra freeness hypothesis nor constant-only action tests occur. No statement is
disputed.

Searches for an existing exact declaration:

- `msearch.py` LeanFinder: "Sheaves on profinite group actions recovered by the
  Cech equalizer of the free action cover" returned eight condensed/profinite
  presentation declarations (`CondensedSet.ofSheafProfinite`,
  `Condensed.isSheafProfinite`, and related transport declarations). They do not
  state this equivariant action-cover square or either recovery normalization.
- `msearch.py` Loogle: `"Profinite", "action"` returned zero hits.
- `msearch.py` grep: `[Cc]ech.*[Aa]ction|[Aa]ction.*[Cc]ech|profinite.*recovery`
  returned two hits in `Mathlib/RepresentationTheory/Homological/Resolution.lean`.
  Read lines 84--120: these identify the simplicial nerve of an abstract G-set
  with EG, not profinite-site sheaf descent or the natural recovery maps.
- `msearch.py` LeanSearch: "Descent along the free action cover identifies
  sections with equivariant Yoneda sections and gives natural recovery
  isomorphisms" returned eight ordinary Yoneda/free-module/cover-dense comparison
  results. They do not state this node.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `cech_recovery`, `CechRecovery`, `actionCover`, `cechRecovery`, and the
  chosen theorem names found no existing declaration. The prescribed recursive
  grep of the item id in `lean/WeilConjectures` found no match. Existing related
  declarations are exactly the dependencies used above, not a second copy.

Validation: the prescribed `scompile.py Q78 lem-sfb-profinite-action-cech-recovery`
compiled the delivered module both as a sandbox probe and at its library module
name, against the live published build and source overlay. No errors or warnings
other than permitted `sorry` declarations. All lines are at most 100 columns.
Delivery dry-run and push results follow the wrapper's final output.

## Second reading by Q78

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
