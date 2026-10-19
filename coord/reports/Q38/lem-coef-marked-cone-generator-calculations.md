## Worker report

Item: `lem-coef-marked-cone-generator-calculations`, Q38, 2026-10-17.
Module: `Sheaf.AlgebraicTopology.MarkedConeGeneratorCalculations`.
Main declaration: `SSet.MarkedCone.marked_cone_generator_calculations`.

I read the item, every statement-dependency node and its recorded source declaration,
the stage-2 brief and stage document, delivery-errors H, the worker role, SETUP, GOAL,
STATE, tools README, and the CompactObject example and node. No repair note exists for
this item. I opened the official HTT PDF at the source URL, Definition the project server,
Propositions the project server and the project server and the surrounding generator calculations.
The node's statement is unchanged. No new node or dependency-record repair is needed.

The module constructs actual marked cone values, then states existence of their
fully normalized enriched diagram functors and the generator and terminal calculations.
It never selects an object or map from an uncharacterized existence theorem. There
are two postponed theorems, `triangle_endpoints` and the main theorem. The former
supplies only the endpoint equalities required by the real coning-edge construction;
its source and proof are in its docstring. The main docstring follows all nine DAG
proof steps, including the two inverse-triangle calculation and arbitrary acting-edge
contraction. All theorem proofs are `sorry`.

Hypotheses and clauses, matched individually:

* All small simplicial sets and categories are in the explicitly bound universe `u`:
  `S : SSet.{u}`, `I : SCat.{u}`. Marked objects live in `Type (u+1)` with morphisms
  in `Type u`; no equality of distinct site universes, finiteness, nonemptiness, or
  local Kan assumption is introduced.
* The coefficient map is exactly
  `u : PinchedCube.rigidification.obj S ⟶ UnmarkedStraightening.oppositeCategory I`.
  `M : Marked.CartesianModelStatement.{u}` supplies the already stated marked model
  and its sharp mapping enrichment; it is universally quantified, not an additional
  mathematical restriction on S or I. `ModelObjects M` is definitionally the existing
  `Marked` type, carrying M's supplied enrichment through global instances. It does
  not create another notion of marked simplicial set.
* A marked map to S is encoded as `X : Over (Marked.sharp S)`: the target marking
  is all edges, so every underlying map is permitted. `unmarked X` forgets precisely
  the marking. `unmarkedMap` preserves the actual slice square.
* The pushout P, base object, cone point, value, and precomposition action are
  `UnmarkedStraightening.conePushout`, `baseObject`, `coneVertex`, `value`, and
  `valueAction`. These are actual enriched pushout/mapping-object constructions.
* `triangle` is the coherent realization of the triangle coning e, mapped through
  the pushout cone leg. `coningEdge` applies it to the existing interval of paths
  `{0,2} ⊆ {0,1,2}`, with only the named endpoint-equality transport. Its direction
  is from the direct cone arrow to the composite through e's target.
* `MarkedCone.value.marking` is exactly the union of all degeneracies and the edges
  `valueAction ... (coningEdge ... e, g)` for `e ∈ X.left.marking` and every
  `g : hom I (coefficientVertex ... (source e)) i` in degree 1. This is exactly
  `Iᵒᵖ(i,u(x))₁`, with the opposite indices written in I. No extra closure under
  composition is inserted.
* `Realization` contains the existing `SimplicialDiagramEnrichment`, hence the
  existing category with full enriched transformations, and a functor from the
  marked slice into that category. Its `objects` field fixes every marked value,
  `actions` fixes the entire uncurried simplicial action, and `arrows` fixes every
  component to the canonical enriched pushout map. The action is a marked map
  from the value times `sharp (hom I i j)`: all edges of the acting mapping set
  are marked, as required. These normalizations specify the intended functor,
  rather than an unrelated functor with the same weak-equivalence behavior.
* `canonicalIndex S` is the opposite of `C[S]`; `canonicalComparison S` is the
  identity through double-opposite type synonyms, on objects and mapping sets.
  Its composition proof removes the two symmetries; this is purely structure
  assembly, not a proved mathematical theorem in this stage.
* `GeneratorCalculations.boundaries` quantifies over every `n : ℕ`, including 0,
  and applies the normalized canonical functor over `Δ[n]` to the flat boundary
  inclusion. `overTarget` makes the target's underlying set the base and its
  target structure map the identity.
* `GeneratorCalculations.marking` is precisely the flat-to-sharp interval map,
  under the normalized canonical functor over `Δ[1]`.
* `GeneratorCalculations.anodyne` quantifies over `Marked.anodyneGenerators false`.
  This is all four existing generator families, with arbitrary Kan inputs in
  family (iv), without the countability restriction. The source base is exactly
  `B.underlying`. The result is `projectiveCof ∧ projectiveWeak`, namely projective
  trivial cofibration.
* The projective predicates are the intrinsic specialization of the dependency's
  characterized model classes to its existing enriched-diagram category.
  `projectiveWeak` tests `Marked.weak` on every actual enriched component.
  `projectiveCof` uses Mathlib's `MorphismProperty.llp` against objectwise maps
  that are fibrations and weak equivalences, with fibrations exactly
  `(Marked.cof ⊓ Marked.weak).rlp`. It does not replace projective cofibrations
  by objectwise cofibrations or define a competing diagram/model structure.
* The terminal-index object T is the existing `Straightening.markedPoint`, whose
  definition is the same canonical cone mapping object over `Δ[0]` with exactly
  these markings. `pointMap` reuses its canonical pushout-induced map.
* `PointCubeComparison` specifies the cone-simplex identification with its initial
  and final face equations, an enriched isomorphism from `C[Jⁿ]` to the actual
  terminal cone pushout, and its equation on the uncollapsed simplex. Its source
  and target equations identify the collapsed and cone vertices. This states the
  node's assertion that the initial face is collapsed, rather than just asserting
  an isomorphism of uncharacterized simplicial sets.
* `PointCubeComparison.quotientIso` is fixed on the existing surjective subset
  quotient by `quotient_normalization = PinchedCube.canonicalMap`. Thus the
  existing subset-cube quotient, not a newly defined Q, is used.
* `PointCalculation.simplex` gives `T((Δ[n])^flat).underlying ≅ Qⁿ`.
  `simplex_normalization` fixes its inverse to `pointCubeMap`, which is explicitly
  the quotient comparison followed by the canonical enriched collapse map.
  `simplex_natural` requires naturality for every ordinal map, not just faces.
* `PointCalculation.coend` identifies every underlying T(X) with the existing
  explicit quotient coend `UnmarkedStraightening.qRealization X.underlying`.
  `coend_generators` fixes this comparison on every simplex summand via
  `qGenerator`, `simplexMap` and `pointMap`. The coend retains all ordinal relations.
* `maximum` is a natural transformation `PinchedCube.qFunctor ⟶ stdSimplex`;
  `maximum_quotient` fixes it by the existing nerve map `J ↦ max J` after the
  surjective quotient projection, so it is the stated maximum augmentation.
* `augmentation : ∀ X, markedPoint X ⟶ X` already asserts preservation of all
  markings. `augmentation_generators` fixes its underlying map on every coend
  summand to maximum followed by the simplex map. `naturality` covers every
  marked map X → Y.
* `point_iso`, `flat_interval_iso`, and `sharp_interval_iso` are `IsIso` of this
  same marked augmentation for all three inputs named in the node. None is
  replaced by a weak equivalence or by an underlying unmarked isomorphism.

Dependency declarations read and used:

* `Sheaf.CategoryTheory.CoherentNerveComparison`: `CoherentNerveComparisonStatement`,
  `coherent_nerve_comparison`, `SCat`/the coherent-nerve conventions. The actual
  canonical colimit rigidification is the one already fixed by PinchedCube.
* `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`: `Marked`, its map category,
  `flat`, `sharp`, `product`, `CartesianModelStatement`, `tensor_adjunction`,
  `mapping_iso`, `cof`, `weak`, and the recorded marked-model theorem.
* `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`: `flatToMarked`,
  `anodyneGenerators` and its four family definitions, and the recorded lifting theorem.
* `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`:
  `SimplicialDiagramEnrichment`, its `Diagrams`, `value`, and `component`,
  `ProjectiveSimplicialModelStructure` and its objectwise class characterizations,
  and the recorded projective-model theorem. The intrinsic lifting formula avoids
  selecting a model structure from its existential theorem.
* `Sheaf.AlgebraicTopology.PinchedCubeLatching`: `rigidification`, coherent simplex
  and unit, `Q`, `J`, `x`, `y`, `qMap`, `qFunctor`, `quotientMap`, `maximumMap`,
  `canonicalMap`, `initialFace`, `pinch`, and the recorded latching theorem.
* Construction-only imports also reuse `UnmarkedStraightening` pushout/value/action/
  valueMap/coefficientVertex/qRealization/qGenerator, and
  `Straightening.simplexInclusion`, `coneTriangleInterval`, `markedPoint`,
  `markedValueMap`. Their comparison theorems are not invoked.
* The existing proof dependencies `SelectivelyMarkedTerminalCylinder` and
  `InfinityMappingComposition` are ordinary, non-public imports for stage 3.

Import-cycle note: `MappingSimplexConeFibers` already owns `coneTriangleInterval`
and `markedPoint`, so they are reused, not copied. Its theorem's DAG proof cites
this item. Its current source has no import of this item. A later proof-only
import of this item into that module must be omitted under stage 2 §3(7), since
it would create an import cycle. This module uses only its existing explicit
constructions, never its downstream mapping-simplex comparison theorem. No
mathematical dependency on that downstream theorem is introduced.

Edge cases checked:

* Empty X has no coning generators; the definition includes every degeneracy
  regardless and imposes no nonemptiness condition. The cone is still a real pushout.
* Empty I is allowed whenever the coefficient functor exists. Evaluations are then
  empty-indexed; no fabricated object or chosen vertex of I is required.
* Boundary dimension zero is included by `∀ n : ℕ`; the underlying source is
  `boundary 0 = ⊥`, not a positive-dimensional cube assumption.
* The final-horn family includes dimension 1 via the existing `finalMarkedHorn 0`.
* An empty Kan input is included in family (iv). No Countable or local Kan binder
  restricts this family or any acting mapping simplicial set.
* The terminal point and both interval markings use the same marked augmentation;
  all three conclusions assert isomorphisms in the marked category.
* Naturalities range over all simplex operators, including degeneracies and
  arbitrary marked maps. Independent universe narrowing is not used.

Searches actually run:

* `msearch.py ... leanfinder "Coherent marked cone straightening generator calculations
  projective cofibrations"`: eight hits on connected costructured-arrow cones,
  strict Segal coskeletal cones, and a Profinite extension cone; no marked cone match.
* `msearch.py ... loogle '"SSet", "anodyne"'`: twelve ordinary unmarked anodyne
  and strong-anodyne hits, not this statement.
* `msearch.py ... grep 'marked.{0,20}cone|straightening|coneStraight'`: zero hits
  in Mathlib.
* `msearch.py ... leansearch "Marked coherent cone realization projective generator
  calculations"`: eight unrelated convex-cone/projective-object hits; no match.
* `rg` for markedCone/MarkedCone/coneStraight/ConeStraight/coneGenerator/
  ConeGenerator/conePushout/coneVertex in the project, source and upstream name
  index found the existing cone construction and marked simplex-cone definitions
  listed above, but no existing full theorem. Those constructions are reused.
* Direct node-id search in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`
  found no declaration for this item.
* Final exact-name/namespace/module search in Mathlib, upstream WeilConjectures,
  project `lean/Sheaf` and `dag/lean_names_upstream.json` found no collision.

Validation: the prescribed scompile.py compiled the final module cleanly in both
sandbox and module-path form, with no warnings. Every binder and universe is
explicit (`autoImplicit false`). The only pending logical proofs are the two
named theorems above; definitions have real data. The required delivery dry run
is recorded below after completion.

Dry run: `deliver2.py Q38 lem-coef-marked-cone-generator-calculations --no-push`
printed `OK (dry run)` for commit `1d18faa69f`: compilation and preflight passed,
with only the independent second reading pending as expected. Nothing was pushed.

## Second reading by Q38

I independently reopened the item node, its five statement dependencies, the recorded
Lean declarations, the complete module, and HTT Definition the project server, Propositions
the project server, the project server, and the project server (PDF pages 168--178). The following is the
item-by-item correspondence.

* The node's objects are a small simplicial set `S`, a small simplicial category `I`,
  a simplicial functor `u : C[S] ⟶ Iᵒᵖ`, a marked object over `S`, the pushout `P_X`
  with cone vertex, and the marked values and action. In Lean these are the explicit
  binders in `unmarked`, `unmarkedMap`, `triangle`, `coningEdge`, `value`,
  `Realization`, and `action`; `u` has exactly the recorded opposite-category type.
  `Realization.objects`, `.actions`, and `.arrows` retain the values, the whole
  simplicial action, and every canonical pushout map. Verdict: all objects and no
  extra hypothesis.
* The node's marking clause is exactly the set in `value.marking`: all degeneracies
  (`Set.range (σ 0)`) and precisely `valueAction ... (coningEdge ..., g)` for a marked
  input edge and every degree-one acting simplex. The arbitrary acting edge is retained;
  no Kan, finiteness, nonemptiness, or countability condition is added. Verdict: exact.
* For the canonical index, the node's `I = C[S]ᵒᵖ` and identity coefficient map are
  rendered by `canonicalIndex` and `canonicalComparison`; the latter is the canonical
  double-opposite identity, with its composition proof. `GeneratorCalculations` then
  states the boundary maps for every `n : ℕ`, the flat-to-sharp interval map, and all
  four `Marked.anodyneGenerators false` families as projective cofibrations and weak
  equivalences. Its `projectiveCof` is the lifting class against objectwise
  fibrations-and-weak-equivalences, and `projectiveWeak` is objectwise `Marked.weak`.
  Verdict: every generator clause, including `n = 0`, is present with the same strength.
* The node's absence of a local-Kan hypothesis is reflected by no such binder in
  `Realization` or `GeneratorCalculations`; `I` is only a `SCat`. Verdict: exact.
* The terminal calculation is rendered by `PointCubeComparison` and `PointCalculation`.
  `cubes`, `simplex`, `simplex_normalization`, and `simplex_natural` give the
  normalized `Qⁿ` identifications for all ordinal maps. `coend` and
  `coend_generators` give the explicit coend and every simplex summand. `maximum` and
  `maximum_quotient` give the maximum map, while `augmentation` and
  `augmentation_generators` give the marked natural map to `X`; `naturality` covers
  every marked map. The three `IsIso` fields are exactly the point, flat interval,
  and sharp interval cases. `Straightening.markedPoint` is the existing terminal
  cone construction, whose `valueAt` is the same coherent pushout construction.
  Verdict: all terminal clauses and their normalizations are present.
* `M : Marked.CartesianModelStatement` is a supplied instance of the dependency's
  marked model data, not a new restriction on `S`, `I`, or `X`; `ModelObjects` is
  definitionally the existing `Marked` type and its category/enrichment instances are
  inherited from `M`. Verdict: no extra mathematical hypothesis.

Edge cases were checked directly in the definitions and quantifiers: empty `X` has
only degeneracies, empty `I` is permitted and is handled by empty evaluations, the
empty boundary at `n = 0` is included, the final marked horn includes its `n = 1`
case through the existing generator, empty Kan inputs are allowed, and all degeneracy
and ordinal-map naturality cases are quantified. No universe is narrowed beyond the
single explicitly bound `u` used by the dependency conventions.

I repeated the duplicate searches with `rg` over `lean/Sheaf`, the slopmaster2
`WeilConjectures` tree, Mathlib, and `dag/lean_names_upstream.json`, and ran independent
`msearch.py` queries: LeanFinder "simplicial marked straightening sends inclusions
to enriched projective cofibrations" (eight ordinary simplicial model and nerve hits),
Loogle '"SSet", "boundary"' (twelve ordinary boundary/composition hits), LeanSearch
"marked straightening cone augmentation quotient of subset poset" (eight unrelated
convex cone and colimit hits), and grep "StPlus|cone.{0,30}mark|marked.{0,30}projective"
(zero Mathlib hits). They find
only the reused cone, marked-model, and pinched-cube constructions; no declaration of
this theorem or a competing `MarkedCone` notion exists. No dependency record is
unusable, so no dependency module or new definition node is required.

No mismatch was found and no source or Lean statement was changed. The prescribed
`scompile.py` run on the module completed cleanly with no warnings.

## Maintainer review fix (H4)

The landed module `Sheaf.AlgebraicTopology.MarkedConeExternalProduct`
(lem-coef-marked-cone-external-product, landed in batch 205b1b662e shortly before this
delivery's commit) already defines, in the same namespace `SSet.MarkedCone`, the general
marked cone value `L_u(X)(i)` with exactly this node's marking: `Input`, `underlyingInput`,
`underlyingInputMap`, `edgeTriangle` and `markedValue` (degeneracies, and the acting images
`g^* ẽ` of the `{0,2} ⊆ {0,1,2}` coning edge of each marked edge, for every degree-one
`g ∈ I(u(x), i)`). The delivered `unmarked`, `unmarkedMap`, `triangle`,
`triangle_endpoints`, `coningEdge` and `value` were a second definition of the same notion.
The reviewer's replacement module imports that module and uses `Input S`,
`underlyingInput`, `underlyingInputMap` and `markedValue` in `Realization`; the six
duplicate declarations are removed. Nothing else changed; the main statement
`marked_cone_generator_calculations` is verbatim the same. The fixed module compiles
cleanly with `tools/nt_compile.py` (no error, no warning).
