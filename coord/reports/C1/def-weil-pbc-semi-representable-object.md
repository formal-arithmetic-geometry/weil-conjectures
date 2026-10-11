## Worker report

The module `lean/Sheaf/AlgebraicGeometry/SemiRepresentableObject.lean` defines points,
covering morphisms, chosen matching objects/maps, and the hypercover predicate on
`FormalCoproduct.{w} X.Etale`. It introduces no new category, simplicial-object,
coskeleton, or boundary-diagram definition. There are no `sorry`s in this module.
Matching cones and maps are extracted from the existential statements of the
recorded matching-object dependency; their data are not postponed. No statement
correction, new node, dependency replacement, or disputed statement was needed.

Sources checked: [Stacks 01G0](https://stacks.math.columbia.edu/tag/01G0),
[Stacks 01G3](https://stacks.math.columbia.edu/tag/01G3), and
[Stacks 01G5](https://stacks.math.columbia.edu/tag/01G5). The local Stacks TeX file
is absent on this machine, so the original definitions were read online. They
specify formal families, coverings component by component, and all-degree
hypercovers. The recorded matching/coskeleton dependency modules were read in full.

Clause-by-clause correspondence:

1. The only base hypothesis is `X : Scheme.{u}`. The category is exactly the
   dependency's `FormalCoproduct.{w} X.Etale`, with an arbitrary index universe `w`.
   Its objects have fields `I` and `obj`; morphisms have `f : U.I → V.I` and
   `φ i : U.obj i ⟶ V.obj (f i)`. Identities and composition are Mathlib's
   `FormalCoproduct.category`. `X.Etale` supplies precisely étale morphisms to X
   and morphisms over X. `semiRepresentableHasFiniteLimits` applies the recorded
   `hasFiniteLimits_of_hasTerminal_and_pullbacks` to Mathlib's existing terminal
   and pullback instances for formal coproducts. Mathlib's `pullbackCone` uses
   `Function.Pullback f.f g.f` as its index set and component pullbacks, as in the
   node. Degree zero uses the literal family `{id_X}`:
   `(FormalCoproduct.incl X.Etale).obj (Etale.mk (𝟙 X))`. Its finality is obtained
   from `Over.mkIdTerminal`, reflected through `Etale.forget`, then lifted by
   `FormalCoproduct.isTerminalIncl`.
2. `semiRepresentablePoints T L` is the morphism type
   `(FormalCoproduct.incl X.Etale).obj T ⟶ L`. The dependency's
   `FormalCoproduct.inclHomEquiv T L` identifies it with the dependent pairs
   `(j, t : T ⟶ L.obj j)`; no second point representation is introduced.
   `semiRepresentablePointsMap T f` is `fun t => t ≫ f`.
3. `IsSemiRepresentableCovering f` quantifies `∀ j : V.I`. The fibre index type
   `{i : U.I // f.f i = j}` is exactly the source's indices with α(i)=j.
   The component family is
   `fun i => f.φ i.val ≫ eqToHom (congrArg V.obj i.property)`.
   The equality transport merely gives all components the common codomain
   `V.obj j`. The generated `Sieve.ofArrows` is required to belong to
   `X.smallEtaleTopology (V.obj j)`. This is exactly a covering family by the
   recorded `ofArrows_mem_smallEtaleTopology_iff`, which equates this condition
   with joint surjectivity. No finiteness or nonemptiness hypothesis is added.
4. `K : SimplicialObject (FormalCoproduct.{w} X.Etale)` is the existing functor
   category from `SimplexCategoryᵒᵖ`. `K _⦋n⦌`, `K.map`, `K.δ`, and `K.σ` are
   the dependency's terms, operators, faces, and degeneracies; morphisms are
   natural transformations. `semiRepresentableMatchingFan K` chooses the fan of
   `matching_object_one K`; `semiRepresentableMatchingCone K n` chooses the cone
   of `matching_object_succ_succ K n`. Both choose witnesses from existence
   statements that also supply the limiting proof, compatible-point equivalence,
   and naturality, rather than assume arbitrary cones. The diagram is exactly
   the dependency's `matchingBoundaryIndex K n`: n+3 faces and ordered pairs,
   with arrows d_(j-1) and d_i. `semiRepresentableMatchingObject K` treats zero,
   one, and `n + 2` separately, giving `{id_X}`, the two-copy product, and the
   finite boundary limit. `semiRepresentableMatchingMap K` in positive degrees
   selects the unique map with face projection equations from the same theorem's
   `choose_spec`; in zero it is the unique terminal map. Thus the dependency's
   point-tuple bijections apply with `W = {T}`. The imported
   `matching_object_coskeleton_one` and `matching_object_coskeleton` apply to
   these chosen cones with their `choose_spec` limiting proofs and face-map
   equations; they give precisely the coskeleton isomorphisms carrying the
   canonical map to the chosen matching map. These claims already belong to the
   dependency statements and are not restated with new proofs in this definition.
5. `IsSemiRepresentableHypercover K` is
   `∀ n : ℕ, IsSemiRepresentableCovering (semiRepresentableMatchingMap K n)`.
   It includes every degree, with no truncation. At n=0 the target is the
   one-member family `{id_X}`, so the covering predicate is exactly that K₀
   covers X in the small étale site. Its positive-degree meaning agrees with
   the source's coskeleton condition by the recorded comparison dependency.

Dependency declarations used (all signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.smallEtaleTopology`,
  `AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff`; and
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`:
  `AlgebraicGeometry.Scheme.Etale`, `Etale.mk`, `Etale.forget`.
- `Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic`:
  `CategoryTheory.Limits.FormalCoproduct`, `.Hom`, `.category`, `.incl`,
  `.inclHomEquiv`, `.isTerminalIncl`, the terminal/pullback instances,
  `.pullbackCone` and `.isLimitPullbackCone`.
- `Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers`:
  `CategoryTheory.Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks`.
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`:
  `CategoryTheory.SimplicialObject`, `.δ`, `.σ`, `.Truncated`, `.truncation`,
  `.Truncated.cosk`, `.coskAdj`; and
  `Mathlib.CategoryTheory.Functor.KanExtension.Basic`:
  `CategoryTheory.Functor.IsRightKanExtension`.
- `Sheaf.CategoryTheory.SimplicialMatchingObject`:
  `CategoryTheory.SimplicialObject.matchingBoundaryShape`, `.matchingBoundaryIndex`,
  `.matching_object_zero`, `.matching_object_one`, `.matching_object_succ_succ`.
- `Sheaf.CategoryTheory.MatchingObjectCoskeleton`:
  `CategoryTheory.matching_object_coskeleton_one`, `.matching_object_coskeleton`.
- The simplicial-set dependency was read too: `SSet`, `SSet.degenerate`,
  `SSet.nonDegenerate`, `SSet.Subcomplex`, and `SSet.Finite` from their recorded
  Basic/Degenerate/Subcomplex/Finite modules. Only its simplex category is needed
  here; no finite-simplicial-set assumption is introduced.

Edge cases checked before writing:

- An empty source family over a nonempty component gives an empty generated sieve,
  hence is not covering; an empty scheme component admits the empty covering.
- An empty target family makes the covering predicate vacuous, as in the source.
- The empty base scheme is allowed. Formal families with many copies of the empty
  scheme retain their indices, as formal coproducts must; they are not identified
  with an empty family or with a coproduct scheme.
- n=0 and n=1 are explicit separate branches. n=1 has no face-compatibility
  constraints; every n≥2 is uniquely n'+2 with the recorded boundary diagram.
- No family is required finite, nonempty, affine, separated, or Noetherian.
  Independent arbitrary `w` permits every set-sized family in its universe;
  this is not a scheme-limit indexing universe restriction.

Searches for existing declarations:

- `msearch.py ... leanfinder "semi representable objects over an etale site and
  simplicial hypercovers whose matching maps are covering families"`: eight
  hits, including `smallEtaleTopology` and `OneHypercover`/`HOneHypercover`;
  none defines all-degree simplicial hypercovers of formal families.
- `msearch.py ... loogle "FormalCoproduct, Hypercover"`: zero hits, unknown
  identifier `FormalCoproduct` in the search service's namespace.
- `msearch.py ... grep "SemiRepresentable|IsHypercover|matchingMap|matchingObject"
  CategoryTheory`: zero Mathlib hits.
- `msearch.py ... leansearch "simplicial hypercover semi representable etale site
  matching object coverings"`: service unavailable (Internal Server Error),
  recorded as unavailable without inferring absence from this failure.
- `rg -n 'SemiRepresentable|semiRepresentable|semi-representable|FormalCoproduct|
  matchingObject'` on the project's `lean/Sheaf` and the source's
  `WeilConjectures`: only FormalCoproduct Čech uses in CechComparison and
  FreeCechComplexExact. They do not define the notion of this item.
- `rg -n 'def-weil-pbc-semi-representable-object'` on `WeilConjectures` and
  `dag/lean_names_upstream.json`: no hit. The prescribed upstream node-id search
  therefore finds no recorded duplicate.

Validation: the complete module compiled on the server in 1.9 seconds with no
errors or warnings. All variables and universes are bound explicitly. The
signature in the node copy is extracted verbatim from the module. Only the
item's `lean` field is changed. The second reader must independently review this
report and file and perform the delivery; no second-reading section is fabricated.


## Second reading by C1

Independent review of the node and module, with all eight statement-dependency
nodes and their recorded declarations open. I read the original Stacks TeX from
https://raw.githubusercontent.com/stacks/stacks-project/master/hypercovering.tex
at definition-SR, definition-covering-SR and definition-hypercovering, including
the surrounding assumptions, and simplicial.tex at lemma-existence-cosk and
lemma-formula-limit. I also checked the rendered tags
[01G0](https://stacks.math.columbia.edu/tag/01G0),
[01G3](https://stacks.math.columbia.edu/tag/01G3),
[01G5](https://stacks.math.columbia.edu/tag/01G5) and
[0186](https://stacks.math.columbia.edu/tag/0186).
The source requires a site and fibre products; the small etale site provides
both for every scheme. There is no hidden Noetherian, separation, finiteness or
characteristic assumption.

The object/hypothesis/conclusion list and its Lean correspondence:

1. Arbitrary scheme X and its small etale site, final object id_X:
   `X : Scheme.{u}`, `X.Etale`, `X.smallEtaleTopology` and
   `Etale.mk (𝟙 X)`. Verdict: exact. The Etale objects are etale X-schemes
   and their arrows are X-morphisms, not arbitrary scheme maps.
2. Formal families with arbitrary set I; index map alpha, component arrows,
   identities and composition: `FormalCoproduct.{w} X.Etale`, its fields
   `I : Type w`, `obj`, and its `Hom.f`, `Hom.φ`, `category` instance.
   Verdict: exact reuse of the dependency, without a second category.
3. Finite limits, singleton final family and componentwise fibre products:
   `semiRepresentableHasFiniteLimits` reuses
   `hasFiniteLimits_of_hasTerminal_and_pullbacks`; Mathlib's
   `isTerminalIncl` gives the singleton final object and `pullbackCone`
   uses `Function.Pullback f.f g.f`, with precisely the equal-index pairs
   and component pullbacks. Verdict: all clauses supplied by the recorded
   finite-limit dependency; no new theorem proved.
4. T-points and their action: `semiRepresentablePoints T L` is the Hom from
   `incl.obj T`, with `inclHomEquiv T L` identifying it with pairs `(j,t)`;
   `semiRepresentablePointsMap T f` composes `t ≫ f`. Verdict: exact,
   including the order of source, target and composition.
5. Covering of each target component: `IsSemiRepresentableCovering f`
   quantifies `∀ j : V.I` and indexes the arrows by
   `{i : U.I // f.f i = j}`. The `eqToHom (congrArg V.obj i.property)`
   transports only the codomain. The generated sieve belongs to the
   recorded small etale topology. I read
   `ofArrows_mem_smallEtaleTopology_iff`: its right side is the union of
   component-map ranges equal to the entire target. Verdict: exact
   jointly surjective families, without finite/nonempty restrictions.
6. Simplicial object, terms, operators, faces, degeneracies and morphisms:
   `K : SimplicialObject (FormalCoproduct.{w} X.Etale)` is the existing
   functor category; `K _⦋n⦌`, `K.map`, `K.δ`, `K.σ` and natural
   transformations are exactly the recorded simplicial-object declarations.
   The simplex category is the recorded one; no extra condition on K.
   Verdict: exact reuse.
7. Matching objects and maps in every degree:
   `semiRepresentableMatchingObject K 0` is literally `incl.obj (Etale.mk
   (𝟙 X))`; the zero map is its terminal map, obtained by reflecting
   `Over.mkIdTerminal` through `Etale.forget` and applying `isTerminalIncl`.
   At one, `semiRepresentableMatchingFan` selects the fan in
   `matching_object_one`; its map selects the existential witness with
   both face projection equations. At `n+2`,
   `semiRepresentableMatchingCone` selects the cone in
   `matching_object_succ_succ`, and its matching map selects that theorem's
   unique face-projection witness. I checked the conjunction projections
   `.choose_spec.2.2.2.exists.choose` and
   `.choose_spec.2.2.2.2.exists.choose` against the full signatures:
   these select the specified maps, not arbitrary arrows. The diagram has
   `Fin (n+3)` faces, ordered pairs i<j, and arrows d_(j-1), d_i.
   The same existential witnesses retain the limiting proof, uniqueness,
   natural tuple equivalence and projection equations. Verdict: exact.
8. T-point tuple characterization and coskeleton comparison: specialize the
   recorded tuple equivalences to `W = incl.obj T`; their equations have
   composites `x_i ≫ d_(j-1) = x_j ≫ d_i`. The imported
   `matching_object_coskeleton_one` and `matching_object_coskeleton` take
   these chosen fans/cones with their limiting proofs and the chosen maps'
   face equations, and give the unique isomorphism carrying the canonical
   degree map to the matching map. Their finite-limit hypotheses are
   supplied above; no right Kan extension instance is assumed of the user.
   Verdict: the node's claims follow from the dependency statements exactly.
9. Hypercover, all degrees including zero:
   `IsSemiRepresentableHypercover K` is
   `∀ n : ℕ, IsSemiRepresentableCovering (semiRepresentableMatchingMap K n)`.
   Zero says K_0 covers id_X, and positive degrees match the source's
   coskeleton condition by item 8. Verdict: exact; no truncation.

Edge cases: the empty target family makes item 5 vacuous, as required.
An empty source fibre covers exactly when its target component is empty,
by the range-union criterion; in particular it cannot cover a nonempty
component. Empty schemes and repeated empty-scheme components remain allowed,
with formal indices retained. Degrees zero and one are explicit branches;
every degree at least two is n+2. A zero object assumption does not apply to
this category. No characteristic or field hypothesis occurs. Both u and w
are explicitly bound and independent: w sizes formal families, not a
scheme-limit diagram. The matching boundary diagrams themselves are finite.
No missing binder, extra instance hypothesis or excluded universe case found.

Independent searches used different conceptual wording from the worker:
`msearch.py ... leanfinder "simplicial resolution on a Grothendieck site with
covering maps to coskeletons of families of representable objects"` returned
8 hits, principally cosk, Truncated.cosk and HOneHypercover; none is this
all-degree notion. `msearch.py ... loogle '"hypercover"'` returned 12 hits,
all zero-hypercover notions. Independent `rg -i` searches for hypercover,
semirepresent, semi.represent and coskeleton in Mathlib's Hypercover directory,
the source WeilConjectures and the project's lean/Sheaf found zero/one
hypercovers and the already-read matching/coskeleton dependencies, not an
existing declaration of this full notion. These dependencies are reused.
A fresh LeanSearch query is recorded below with its service result.

H5/H6/H8/H9: there is no sorry in the module, no new theorem proof, no
private notion, local instance or file-local notation. Existential data are
chosen from named dependency theorems, which is permitted rather than hollow.
Every declaration has a source and blueprint docstring. The definition node
has empty proof, so no statement proof docstring is missing. Imported
coskeleton comparisons carry the corresponding node's claims. No new nodes,
dependency replacement modules, statement correction or disputed statement
are present. The item's lean.statement agrees verbatim with the main
signature. The independent server compile completed in 1.8 seconds with exit
code 0, no errors and no warnings.

Mismatches and changes: none found. Lean and node left unchanged; appended
this independent reading and its validation evidence only.

Fresh LeanSearch: `all dimensional hypercover of an etale site with formal
families and covering boundary matching morphisms` returned UNAVAILABLE,
Internal Server Error. No absence verdict is based on this failed service.
