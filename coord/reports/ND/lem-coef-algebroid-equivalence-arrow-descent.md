## Worker report

Repair of return L / immutable head 11829b58246e, H1. The sandbox was empty at
restart; the complete module, node Lean binding, compilation evidence and required
report sections are supplied by this delivery. The read-only current node has no
Lean binding. The node's mathematical statement and all its other fields are
preserved. No dependency repairs, new nodes or statement corrections are needed.

Module: `Sheaf.CategoryTheory.AlgebroidEquivalenceArrowDescent`.
Main declaration:
`SSet.Enhanced.Algebroid.algebroid_equivalence_arrow_descent`.
It is a stage-2 theorem with exactly `sorry` as its proof. All helper definitions
have real data. Index-functor laws are proved as part of those definitions.

The module uses two equivalent universal-property presentations, made explicit
here for independent review. First, the naturally equivalent `I₀(C)` is the model
for `U(C)`, as identified naturally in the recorded equivalence-nerve dependency.
Second, products are expanded into their two projection factors when testing the
homotopy pullback. No hypothesis concerning these presentations is added.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Presentably monoidal V: `E`, `[Quasicategory E]`, `p` and
  `hp : IsPresentablyMonoidal.{u,v} p`. `p` is precisely the operadic monoidal
  category of the dependency. `unit : UnitSection p` represents its canonical
  coherent tensor-unit section, as in the dependency interface.
- Algebroids, FF and ES: `total.{u,v} p`, `IsFullyFaithful`, and
  `IsEssentiallySurjective unit (algebroidArrow ...)` are the recorded predicates;
  none is restated or replaced by ordinary enriched-category data.
- Universes: the two original parameters `u v` remain independent, with ambient
  `w = max (u+1) v`. The Hom pairing lives in the next universe, so `D` maps into
  the standard `uliftFunctor.{w+1}.obj (total.{u,v} p)`. Removing a lift on an
  individual edge changes no mathematical datum or size restriction.
- A small coherent simplicial diagram together with a coherent cocone to B is
  the single `D` on `GeometricDescent.AugmentedIndex`, the ordinary opposite
  simplex category with a final vertex adjoined, with its entire lifted nerve.
  Its restriction is C_bullet and its adjoined final vertex is B. All simplices,
  rather than only the individual maps j_n, are supplied by D.
- Every structure map FF and ES: `hstructure` quantifies over all `j k` and all
  `f : j ⟶ k` in `SimplexCategoryᵒᵖ`, including degeneracies and identities.
  `descentAlgebroidEdge` extracts the actual edge of D, and `WithTerminal.incl.map`
  includes the structure arrow into its augmentation.
- Every j_n FF: `hcocone` tests `descentAlgebroidEdge D (WithTerminal.homFrom n)`
  for every n. It does not impose ES on the cocone legs.
- The object-space comparison `|U(C_bullet)| → U(B)` is an equivalence:
  `hobjects` says that the specified augmented I₀ diagram is colimiting. In any
  infinity category with these colimits, a specified cocone is colimiting iff its
  canonical comparison from the colimit is an equivalence. The natural `I₀ ≃ U`
  identifies this hypothesis with exactly the node's hypothesis, including the
  cocone map, not just an equivalence between the apex objects.
- The endpoint projections: `endpointRestrictionIndex` sends its initial vertex
  to `[1]` and its two other vertices to `[0]`; its two legs are the opposite
  maps of `const [0] [1] 0` and `const [0] [1] 1`. `endpointCocone unit D` is
  their full simplicial restriction in the first variable of `nerveBifunctor`,
  evaluated on D in its second variable. Thus it contains exactly I₁ and the two
  I₀ endpoints of the statement, with the canonical higher compatibilities.
- Pullback naturality squares: the first conclusion tests `IsEndpointCartesian`
  for every structure arrow. The full index `Fin 2 × EndpointIndex` has six
  vertices. Removing `(0,star)` leaves five: Y_target, X_source in each endpoint,
  and X_target in each endpoint. Their limit is
  `Y_target ×_(X_target × X_target) (X_source × X_source)`.
  The canonical cone with apex Y_source is fixed by `endpointSquareLegs` and
  `GeometricDescent.IsLimitingConeAt`, including the specified commutations.
  It is therefore exactly the homotopy pullback square over object-space squares.
- Realization square in every n: the second conclusion applies the same predicate
  to `WithTerminal.homFrom n`, so its top-right vertex is I₁(B) and its two bottom
  factors are I₀(B). The final conclusion identifies that very I₁(B) cocone with
  the realization, while `hobjects` does so for I₀(B). Transport across these
  canonical identifications yields exactly the displayed realization square.
- The canonical comparison `|I₁(C_bullet)| → I₁(B)` is an equivalence: the third
  conclusion is `IsColimitCocone` of the I₁ column of `endpointCocone unit D`.
  This is precisely the universal-property statement that the comparison of
  this specified cocone is an equivalence. No comparison map is freely supplied.
- Compatibility over `U(B)²`: all three columns lie in the same endpointCocone,
  and the square predicates restrict that same coherent diagram. Thus the
  colimit comparison is the one induced by the two specified endpoint maps;
  factoring through their product recovers the exact compatibility in the node.
- No completeness assumption: there is no `IsComplete` binder for B or C_n.

Dependencies read and used:

- `Sheaf.CategoryTheory.CompleteAlgebroid` (publicly imported by the nerve module):
  `total`, `UnitSection`, `IsPresentablyMonoidal`, `IsFullyFaithful`,
  `IsEssentiallySurjective`, `unitAlgebroid`, `iotaLevel` and the coherent unit
  cosimplicial diagram, with their full signatures and source docstrings.
- `Sheaf.CategoryTheory.AlgebroidEquivalenceNerve`: `nerveBifunctor`, its source
  diagram `nerveSource`, and `algebroid_equivalence_nerve` for the natural I₀ ≃ U
  identification, equivalence fibers and the FF/ES criterion. `algebroidArrow`
  converts the actual 1-simplex to the internal-functor vertex required by ES.
- `Sheaf.CategoryTheory.SpaceGeometricDescent` (publicly imported by that module):
  `index`, `indexMap`, `AugmentedIndex`, `selectArrow`, `column`,
  `IsLimitingConeAt`, `IsColimitCocone`, and `space_geometric_descent` for the
  four-step proof plan. The underlying limit/colimit predicates are those of
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`.
- Mathlib: `WithInitial.lift`, `WithInitial.starInitial`, `WithTerminal.incl`,
  `WithTerminal.homFrom`, `ObjectProperty.FullSubcategory`, product-category
  projections and `SimplexCategory.const`. These are actual index constructors.

Edge cases checked before writing:

- Empty object spaces are permitted; no chosen point of any algebroid occurs.
  If all object spaces are empty, `hobjects` forces the apex object space to be
  empty up to equivalence, and all the statements have their usual empty meaning.
- No connectedness or surjectivity on vertices is required. Object spaces may
  have arbitrary higher homotopy and many components. ES uses components of the
  recorded equivalence realization, not surjectivity of a set of objects.
- Degree zero, all identities and all degeneracies occur in the quantifiers.
  Both projections remain distinct even though their target I₀ diagrams agree.
- Noncomplete algebroids are included; the result never asserts U ≃ I.
- The two ambient size parameters are independent; no equality of universes or
  choice of a smaller category is introduced.
- The expanded boundary has both source endpoint factors and both target
  endpoint factors; it is a product pullback, not a single-endpoint pullback.

Searches for an existing statement and helper notions:

- `msearch.py ... leanfinder "Equivalence arrow spaces of algebroids descend along
  fully faithful simplicial cocones"`: eight results, including ordinary nerves,
  coskeleta, and ordinary Cech conerves; no operadic algebroid descent theorem.
- `msearch.py ... leansearch "Equivalence arrows in simplicial enriched infinity
  categories commute with geometric realization"`: eight results, including
  mapArrowEquivalence, simplicial enrichment and SSet.toTop; no matching theorem.
- `msearch.py ... loogle '"EnrichedCategory", "colimit"'`: zero results.
- `msearch.py ... grep 'algebroid|equivalenceNerve|equivalence_arrow_descent'`:
  one unrelated Mathlib hit, Lie-Rinehart algebra definitions.
- `rg` for those expressions in the upstream WeilConjectures source, including
  the exact node id: no matching declaration.
- `rg` over current `lean/Sheaf`: the CompleteAlgebroid and
  AlgebroidEquivalenceNerve modules supply the notions used here; no theorem for
  this fully faithful simplicial cocone descent statement. Read the full relevant
  signatures and docstrings, not only the search names.
- `rg` for all eight new declaration names over Mathlib, upstream
  WeilConjectures and current `lean/Sheaf`: no name collisions.

Source verification: opened https://arxiv.org/html/1312.3178v4, Theorem 5.6.2,
particularly its final cartesian-transformation and endpoint-fiber argument. This
is the source of the given generalized descent statement. The helper indices
merely spell out the same two vertex maps and the same square universal property;
they introduce no independent missing mathematical notion needing a new DAG node.
The theorem docstring preserves every step of the node's four-step proof.

No STATEMENT-DISPUTED flag or mathematical node fault was found.

## Second reading by ND

This is the author's explicit second pass, not a claim of an independent worker
review. The dispatcher brief forbids starting other agents; the maintainer supplies
independent review of this repair.

With both the node and module open, checked each clause listed above. In
particular, `hobjects` concerns the actual I₀ cocone, not an arbitrary equivalence
between apex objects; `hstructure` has both FF and ES while `hcocone` has only FF;
and the conclusions retain both endpoint coordinates and the canonical cocone.
The final colimit predicate is equivalent to the canonical comparison equivalence,
and simultaneously permits its I₁(B) apex in the realization-square conclusion.
There is no completeness assumption, no set-level replacement for spaces, and no
arbitrary endpoint or comparison map. The two changes of presentation (I₀ for U,
and expanded product corners) preserve exactly the universal properties and all
coherent maps, as detailed above. No mathematical mismatch remained on this pass.
Compiler corrections were confined to a discrete-object equality, fully qualified
product-functor names, the explicit edge degree, and the initial-object uniqueness
proof in the index functor; they did not change the mathematical statement.

Validation (2026-10-17 UTC): the prescribed `scompile.py ND
lem-coef-algebroid-equivalence-arrow-descent <module>` completed with exit 0 and
no warnings or errors. Its sandbox compile took 30.5 s and the named library-path
confirmation took 4.2 s, each below the unchanged 60 s limit. Both dependency
modules needed by the private overlay also compiled through the wrapper.
A local artifact audit confirms exactly one `sorry`, no line longer than 100
characters, the recorded signature verbatim, all eight declarations listed, and
the sole node-field delta `lean`. The dry run below checks the complete repair
against current newtargets-dag using the wrapper-owned immutable delivery base.

`deliver2.py ND lem-coef-algebroid-equivalence-arrow-descent --no-push`
completed successfully: `OK (dry run): commit ee8d5a19fa passes the preflight
and compiles; nothing pushed`. The packet contains exactly the module, the
item's node file and this report. Return H1 is repaired by these complete artifacts.
