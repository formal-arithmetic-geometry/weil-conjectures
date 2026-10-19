## Worker report

Module: `Sheaf.CategoryTheory.MarkedConeStraighteningQuillen`.
Main declaration: `SSet.MarkedConeStraightening.marked_cone_straightening_quillen`.
The module states the marked cone adjunction, its projective Quillen properties,
canonical substitution comparisons and point comparison. No statement correction,
new DAG node, or dependency-interface repair was needed. No statement is disputed.
All theorem proofs are postponed with source and natural-language proof docstrings;
definition data are actual constructions, never chosen from a postponed existence
assertion.

### Hypotheses and clauses

1. Small simplicial sets and simplicial categories are `SSet.{u}` and
   `CoherentNerve.SCat.{u}`. Realization is the existing
   `PinchedCube.rigidification`, the coherent-simplex colimit realization.
   The coefficient enrichment is the given `Marked.CartesianModelStatement P`;
   the theorem installs exactly `P.enrichment` and uses exactly `P.mapping_iso`.
   `Diagrams C` abbreviates the dependency's actual enriched diagram interface,
   including its full simplicial end of transformations. Local Kan is
   `CoherentNerve.IsLocallyKan C`, retained explicitly in `left_quillen`,
   `unit_weak` and `counit_weak`. The cone construction itself exists for arbitrary
   indices, as in HTT Definition the project server.
2. `φ : PinchedCube.rigidification.obj S ⟶
   UnmarkedStraightening.oppositeCategory C` is precisely the enriched functor
   in the node. A marked object over the base is `Marked.Over S`, the slice over
   `Marked.sharp S`. `MarkedCone.underlyingInput` retains its actual underlying
   structure map, rather than replacing it by an arbitrary map.
3. `cone C φ X` abbreviates the existing actual enriched pushout
   `UnmarkedStraightening.conePushout`. `ConeAdjunction.values` identifies each
   evaluated straightening value with `MarkedCone.markedValue C φ X c`.
   Its underlying object is exactly the pushout hom from the image of `c` to
   `UnmarkedStraightening.coneVertex`.
4. The marking is reused from `MarkedCone.markedValue`: degeneracies together
   with the edges obtained from a marked edge of X, its actual coherent coning
   triangle (interval `{0,2} ⊆ {0,1,2}`), and an arbitrary degree-one simplex in
   the coefficient hom. In the reused definition this is `g` in `hom C d i`,
   where `d = φ(x)`; this is exactly `Cᵒᵖ(i,φ(x))`. There is no restriction to
   nondegenerate acting simplices and no marking by arbitrary existence data.
   `ConeAdjunction.actions` identifies the uncurried enriched action with actual
   composition `UnmarkedStraightening.valueAction`. `diagramAction` uncurries
   using P's normalized sharp tensor adjunction. `ConeAdjunction.maps` similarly
   fixes the action on every input map to the actual cone pushout map.
5. `ConeAdjunction.St`, `.Un` and `.adjunction` give the functor and its right
   adjoint. `Statement.projectiveModel` supplies the projective model category.
   Its three class equalities fix fibrations and weak equivalences objectwise
   and cofibrations by lifting against projective trivial fibrations.
   `projectiveWeak` and `projectiveFib` use the dependency's `Objectwise`.
   The fibrations of M are `(Marked.cof ⊓ Marked.weak).rlp` as in P.
   `ConeAdjunction.left_quillen` preserves cofibrations and trivial cofibrations.
6. The extra equivalence hypothesis in `.unit_weak` and `.counit_weak` is exactly
   `DwyerKanEquivalence φ`, with explicit underlying enriched ordinary categories.
   `.unit_weak` quantifies over every object X and every weak equivalence
   `r : St.obj X ⟶ F` with projectively fibrant F. Its conclusion is the relative
   weak equivalence of `adjunction.homEquiv X F r`, namely the actual unit followed
   by `Un.map r`. This expresses the derived unit for any fibrant replacement,
   without assuming X fibrant or St X already fibrant. `IsProjectivelyFibrant`
   means objectwise naturally marked quasicategories, exactly fibrancy in the
   point model. `.counit_weak` asserts objectwise equivalence of the ordinary
   `adjunction.counit.app F`, for every such F. The absence of a cofibrancy
   hypothesis on X is justified explicitly by `Statement.every_object_cofibrant`,
   which asserts the cofibration from every chosen initial object to every X.
7. For every base map a, `Statement.baseChange` supplies `BaseChange.leftIso`
   (`push a ⋙ Stφ ≅ St(𝔠[a] ≫ φ)`) and `.rightIso`
   (`Unφ ⋙ pull a ≅ Un(𝔠[a] ≫ φ)`). `.left_formula` fixes their underlying
   cone hom maps to identity, and `.right_mate` fixes the right isomorphism as
   the left comparison's adjunction mate. `PushPullAdjunction.projection` fixes
   the slice adjunction by the actual second pullback projection.
8. For every enriched π, `IndexExtension` supplies actual enriched restriction:
   its objects are precomposition with π, and its full mapping simplicial set
   map commutes with every evaluation. Its left adjoint has the enriched Hom
   adjunction (`enriched_adjunction`), so it is enriched left Kan extension.
   `IndexChange.leftIso` is `Stφ ⋙ π! ≅ St(φ ≫ πᵒᵖ)`, the inverse orientation
   of the node's displayed isomorphism. `.rightIso` is exactly
   `Un(φ ≫ πᵒᵖ) ≅ π* ⋙ Unφ`. `.left_formula` fixes the transpose to
   `indexValueMap`, induced by the actual `indexConeMap` of pushouts.
   `.right_mate` fixes the right comparison to its adjunction mate.
9. Base identity and composition are explicit fields `base_identity` and
   `base_composition`. For index substitution, `indexValueMap_identity` and
   `indexValueMap_composition` state the corresponding identity/composite
   equations on the canonical transposes. Together with `IndexChange.left_formula`
   these are the identity/composition equations under the canonical enriched Kan
   extension identifications: adjunction transposition is injective, and those
   identifications are defined by the same transposes. All right comparisons
   inherit these equations from the specified mate formulas. `HEq` is used only
   for canonical endpoint transports between the same constructed simplicial
   sets or functor objects; no arbitrary replacement is substituted.
10. `toPointSlice` uses the actual terminal structure map. `point_comparison`
    supplies a natural transformation from point straightening, evaluated at the
    unique object of the terminal enriched category, to `𝟭 Marked`, and states
    `Marked.weak` for every component. The identity φ in the node is the unique
    functor between the terminal coherent realization of Δ[0] and the terminal
    index; the formulation allows any presentation of that terminal category.

### Dependency declarations used

- `Sheaf.CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.CoherentNerve.SCat`, `.hom`, `.IsLocallyKan`, `.underlying`,
  `CategoryTheory.DwyerKanEquivalence`, and the coherent-realization conventions.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked`, `SSet.Marked.CartesianModelStatement`, `.mapSharp`, `.product`,
  `.sharp`, `.weak`, `.cof`, `.IsNaturallyFibrant`, `.toPoint`, and P's enrichment,
  mapping isomorphism and tensor adjunction.
- `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`:
  `SSet.Marked.Over`, `.push`, `.pull`, `.cof`, `.weak false`.
- `Sheaf.CategoryTheory.SimplicialModelCoherentDiagrams`:
  `CategoryTheory.CoherentModelDiagrams.Diagrams`, `.eval`, `.Objectwise`,
  and the diagram interface's `functors`, `evaluation`, `action`.
- `Sheaf.AlgebraicTopology.UnmarkedStraighteningQuillen`:
  `SSet.UnmarkedStraightening.oppositeCategory`, `.conePushout`, `.baseObject`,
  `.coneVertex`, `.valueAction`, `.valueMap`, plus
  `SSet.PinchedCube.rigidification`. This already-landed node is added to stmt_deps.
- `Sheaf.AlgebraicTopology.MarkedConeExternalProduct`:
  `SSet.MarkedCone.underlyingInput`, `.underlyingInputMap`, `.markedValue`.
  This already-landed node is added to stmt_deps. The current source was read via
  `scompile.py --source Sheaf.AlgebraicTopology.MarkedConeExternalProduct` because
  it was newer than the local shared source snapshot.
- Mathlib's enriched functors, opposite enrichment, pushouts, adjunction
  transposition and `CategoryTheory.conjugateIsoEquiv` supply the generic
  constructions. Each recorded proof dependency module is imported without
  `public`; the unstated cone-generator-calculations node is documented in the
  proof plan but has no module to import yet.

### Edge cases and source check

Read HTT Theorem the project server, Definition the project server, Proposition the project server and
Proposition the project server directly in the source PDF. Checked the empty input (empty
cone mapping spaces), empty base (the unique relative input), empty index when
it admits φ, degenerate marked edges, degenerate and nondegenerate acting
1-simplices, arbitrary input markings, identity and composite substitutions,
the terminal point case, and fibrant replacements that are not chosen trivial
cofibrations. None requires an added hypothesis. In particular, projective
cofibrations are not incorrectly identified with objectwise cofibrations, and
the counit is the ordinary counit required by the node. The universe u is
explicit; diagram objects have the enlarged universe already provided by the
existing dependency interface. `autoImplicit` is disabled.

### Searches

All msearch queries used group Q29 and this item id.

- `leanfinder`: “Marked cone straightening and unstraightening Quillen equivalence
  of Cartesian marked simplicial sets and enriched projective diagrams”:
  eight results about ordinary cone category equivalences; no matching theorem.
- `loogle`: `"SSet", "Quillen"`: twelve results about ordinary simplicial-set
  Quillen generator classes; no marked straightening theorem.
- `grep`: `MarkedCone|StPlus|UnPlus|straighten|unstraighten`: no Mathlib hit.
- `leansearch`: “Marked simplicial sets straightening unstraightening Quillen
  equivalence”: eight ordinary simplicial-set model-category/topological
  realization results; no matching theorem.
- `rg` in upstream `WeilConjectures/` for
  `MarkedConeStraightening|marked_cone_straightening|StPlus|UnPlus|straighten|unstraighten`
  and for the exact node id: no hits.
- `rg` in shared `lean/Sheaf/` found the actual unmarked pushout and the specialized
  canonical-index marked construction in `MappingSimplexConeFibers`. Reading the
  external-product node's current Lean record and prescribed server source found
  the general coefficient-index marked construction, which this delivery reuses.
  No existing declaration packages this node's complete adjunction, Quillen,
  derived-unit/counit, substitution and point assertions.

### Validation

Compilation uses only the prescribed `scompile.py` wrapper, with each module
compiled separately. The required delivery preflight is run with
`deliver2.py Q29 lem-coef-marked-cone-straightening-quillen --no-push`.
Independent second reading and actual delivery are reserved for the next worker.

## Earlier second reading (a previous round; superseded)

Pending: the dispatcher assigns the independent second reading to the next
worker, who must replace this section with their findings before delivery.
This preparatory --no-push dry run does not claim an independent review.

## Second reading by Q29

I independently read the sandbox node, its complete Lean module, all six statement
 dependency nodes and the signatures actually used from their modules. I also
read the current `MarkedConeExternalProduct` source through
`scompile.py --source Sheaf.AlgebraicTopology.MarkedConeExternalProduct`.
There is no repair note for this item, no `statement_change`, and no new node or
 dependency module in this delivery. The two added statement dependencies already
exist and own the constructions reused here; they are not private replacements.

### Source and clause-by-clause match

The actual source is HTT, not a Stacks result. I read the supplied HTT text at
Theorem the project server, the fixed-data paragraph opening Section 3.2.1, Notation the project server,
Definition the project server, Proposition the project server, Corollary the project server, and Proposition
the project server with its preceding point specialization. The section fixes only a
simplicial set, simplicial category, and the displayed simplicial functor; it
assumes neither that the base is a quasicategory nor that its total objects are
fibrant. HTT actually permits arbitrary indices in the construction. The node's
local Kan hypothesis remains explicit in its model-theoretic clauses.

My statement inventory and its Lean rendering are as follows. Every verdict
below is a match.

1. **Small simplicial set S and small simplicial category C.** `S : SSet.{u}`
   and `C : SCat.{u}` use the recorded coherent-nerve infrastructure.
   `SCat = EnrichedCat.{u, u + 1, u} SSet.{u}` has small object types and
   mapping simplicial sets; it is not an ordinary category substituted for an
   enriched one. `IsLocallyKan C` means that every `hom C c d` is Kan.
2. **The coherent realization and functor to the opposite.** The binder
   `φ : PinchedCube.rigidification.obj S ⟶
   UnmarkedStraightening.oppositeCategory C` has the prescribed orientation.
   The latter is `EnrichedCat.of SSet (Cᵒᵖ)`, and the former is the existing
   realization used by the unmarked straightening dependency, not a separately
   chosen left adjoint. The local Kan condition is required in `left_quillen`,
   `unit_weak`, and `counit_weak`.
3. **Marked X with its given map to S.** `Marked.Over S` is the ordinary slice
   over `Marked.sharp S`. Thus it allows every underlying map to S and every
   marking on X. `MarkedCone.underlyingInput X = Over.mk X.hom.val` retains
   that map exactly.
4. **The pushout D_X and new cone object.** `cone C φ X` reuses
   `UnmarkedStraightening.conePushout`, the pushout attached by the actual
   realized structure map followed by φ and by the ordered right-cone inclusion.
   `baseObject` and `coneVertex` are the two actual pushout-leg images. The
   latter comes from the last vertex of `X ⋆ Δ[0]`.
5. **Each straightening value is D_X(c,*).** `ConeAdjunction.values` identifies
   every evaluated object with `MarkedCone.markedValue C φ X c`. Its underlying
   simplicial set is precisely `UnmarkedStraightening.value`, namely that hom
   object in the pushout, with the correct endpoint order.
6. **The coned marked edge and every acting 1-simplex.** The reused
   `MarkedCone.edgeTriangle` realizes the actual coned input edge. In
   `markedValue`, p has endpoint subsets `{0,2}` and `{0,1,2}`, so it specifies
   exactly the edge from the direct cone arrow to the composite cone arrow.
   The object d is fixed to φ of `δ 1 e`, the source of e. The quantified
   `g : (hom C d c) _⦋1⦌` is precisely a simplex in `Cᵒᵖ(c,φ(x))`.
   There is no nondegeneracy restriction on g. Degenerate edges are included
   explicitly as required for a marked object. The existential t is constrained
   by `HEq` to the image of this specific triangle, so it is not an arbitrary
   coning edge or an existence-based replacement construction.
7. **Composition and functoriality.** `ConeAdjunction.actions` fixes the full
   uncurried simplicial action to `valueAction`, and `maps` fixes every input
   map to `valueMap`. `diagramAction` uses P's normalized sharp tensor
   adjunction and `P.mapping_iso`. The dependency `Diagrams.functors` is an
   equivalence with actual enriched functors; `representation` and
   `representation_app` describe their full graded transformation end. This
   is not merely an ordinary functor category on the category of vertices.
8. **The right adjoint.** `ConeAdjunction.St`, `.Un`, and `.adjunction : St ⊣ Un`
   give the asserted adjoint functors. Data are existential witnesses of the
   theorem's package, not definitions chosen from an unproved existence theorem.
9. **Projective structure and left Quillen property.** `Statement.projectiveModel`
   supplies an actual `ModelCategory`. Its three class equalities characterize
   weak equivalences and fibrations objectwise and cofibrations by lifting
   against projective trivial fibrations. `projectiveFib` uses exactly the
   point model's `(Marked.cof ⊓ Marked.weak).rlp`. `left_quillen` preserves
   cofibrations and sends a cofibration which is a relative Cartesian weak
   equivalence to a projective weak equivalence. Its conjunction therefore
   preserves trivial cofibrations as well. No objectwise-cofibration shortcut
   is used.
10. **DK hypothesis and derived unit.** `unit_weak` uses the dependency's actual
    `DwyerKanEquivalence φ`, with the canonical underlying enrichments explicitly
    supplied. This is local weak homotopy equivalence plus equivalence on π₀,
    not equivalence of the ordinary underlying category. For each X and each
    weak equivalence `r : St.obj X ⟶ F` with F projectively fibrant, it asserts
    that `adjunction.homEquiv X F r` is a Cartesian weak equivalence. This is
    the unit followed by `Un.map r`, so it includes every fibrant replacement
    allowed by the node, without requiring r to be a trivial cofibration.
11. **Ordinary counit, fibrancy, and all objects cofibrant.** `counit_weak` states
    `projectiveWeak D (adjunction.counit.app F)` for every projectively fibrant
    F, with the same local Kan and DK hypotheses. `IsProjectivelyFibrant`
    means naturally marked quasicategories at every object, the exact point
    fibrancy criterion. It does not impose projective cofibrancy on F.
    `every_object_cofibrant` states the initial-map criterion for every X;
    hence the unit legitimately quantifies over every X.
12. **Base substitution, both sides.** `BaseChange.leftIso` is
    `push a ⋙ Stφ ≅ St(𝔠[a] ≫ φ)`; `rightIso` is
    `Unφ ⋙ pull a ≅ Un(𝔠[a] ≫ φ)`. `left_formula` makes its component the
    identity on the cone hom, and `right_mate` fixes the actual adjunction mate.
    The reused `push` composes the actual map to the base, and `pull` is the
    degreewise pullback with the pulled-back marking. `PushPullAdjunction`
    normalizes its Hom equivalence by the second pullback projection.
13. **Index substitution and enriched Kan extension.** `oppositeFunctor π`
    reverses exactly the hom arguments. `IndexExtension.restriction_objects`
    specifies precomposition with π, and `restriction_mapping` fixes its map
    on the full simplicial end by every evaluation. `enriched_adjunction`
    requires the Hom map induced by restriction and the actual ordinary unit
    to be an isomorphism. Thus its `left` is enriched left Kan extension.
    `IndexChange.leftIso : Stφ ⋙ π! ≅ St(φ ≫ πᵒᵖ)` is the inverse of the
    node's displayed isomorphism; `.rightIso` has exactly the displayed right
    orientation. `.left_formula` fixes the transpose to the map induced by
    the actual `indexConeMap` pushout map, and `.right_mate` fixes its mate.
14. **Identity and composite substitution.** `base_identity` and
    `base_composition` state the base equations explicitly. For indices,
    `indexValueMap_identity` and `indexValueMap_composition` state the
    identities on the canonical transposes. With `IndexChange.left_formula`
    these give the comparisons under the canonical Kan identity/composition
    identifications: both identifications are uniquely characterized by
    precisely these transposes. The mate equations give the right-hand
    coherence. `HEq` here only handles equality transports of the endpoints
    of the same cone constructions.
15. **The point comparison.** `toPointSlice` uses `Marked.toPoint` on every X.
    For terminal C, `point_comparison` gives a natural transformation from
    point straightening evaluated at c to `𝟭 Marked`, with `Marked.weak` on
    every component. The unique enriched functor to this terminal category
    includes the identity presentation in the node. Allowing every terminal
    presentation and c excludes no case and introduces no additional choice
    of coefficient theory.
16. **Coefficient model and quantifiers.** The main theorem accepts
    `P : Marked.CartesianModelStatement.{u}` and installs exactly P's
    enrichment, then asserts `Nonempty (Statement P P.mapping_iso)`.
    This is the model furnished by the recorded point-model theorem. No
    unrelated tensor, enrichment, coefficient assumption, or fibrant-base
    hypothesis is introduced. The package chooses all bases and indices
    together so that its substitutions refer to the same adjunctions.

### Edge cases and universe check

The empty marked input is allowed by `Marked.Over` and the literal cone pushout;
there is no nonempty-vertex binder. With empty base there is only the empty
underlying input. Empty C is allowed whenever φ exists (in particular for the
empty base); all objectwise conditions then have their correct empty
quantification. The point case is stated at `Δ[0]`, including arbitrary marked
X and X empty. Both degenerate and nondegenerate acting edges and input edges
are covered. No restriction on dimensions occurs. Rings, characteristics,
schemes, and their zero cases are not parameters of this node. The single
arbitrary universe u covers all the node's small simplicial sets, indices and
values together; `Marked` and its diagram-object collection live in the larger
universe provided by the dependency. No additional universe equality is imposed.
`autoImplicit` is disabled; all binders and the universe u are explicit.

### Independent searches and changes

I repeated searches with different wording from the worker:

- LeanFinder: `Cartesian model structure marked simplicial sets enriched diagrams
  cone adjunction base change` returned eight unrelated simplicial enrichment,
  realization and ordinary cone results, with no marked straightening theorem.
- Loogle: `"Marked", "Adjunction"` returned zero hits.
- LeanSearch: `Straightening unstraightening marked simplicial set cone pushout
  Quillen adjunction` returned eight results on ordinary pushouts, geometric
  realization, coskeleta and ordinary slice adjoints; none matches this node.
- The prescribed grep search for
  `unstraighten|straighten|MarkedConeStraightening|toPointSlice` returned zero
  Mathlib hits. Direct rg in Mathlib and upstream WeilConjectures found no
  marked straightening theorem. Searches of shared `lean/Sheaf` found the
  unmarked straightening and general marked cone value already reused here,
  plus specialized mapping-simplex constructions, not this package.
- I also searched Mathlib's enriched opposite API and project/upstream sources
  for enriched opposite functors. Its `forgetEnrichmentOppositeEquivalence`
  is an ordinary underlying-category equivalence, not the enriched index map
  needed here. Thus `oppositeFunctor` is not a duplicate of that declaration.
  The delivered full declaration names have no upstream-name-index match.

I found no mismatch requiring a Lean or node repair and left the correct module
and record unchanged. I added this independent reading to the report. The four
named postponed theorems all have `sorry` as their complete proof, source and
blueprint docstrings, and natural-language proofs; all are listed in the owning
node's `lean.declarations`. The main docstring reproduces all thirteen DAG proof
steps and their dependency references. Every definition contains actual data;
its structural law proofs do not postpone construction data. There are no
file-local instances, private definitions, unbound variables, or lines over 100
characters. The node's `lean.statement` is verbatim the main signature.

Validation: the prescribed scompile wrapper compiled the sole delivered module
cleanly (both its sandbox check and library-path check). Delivery preflight and
push are run below as the final delivery steps.

The required `deliver2.py Q29 lem-coef-marked-cone-straightening-quillen --no-push`
finished with `OK (dry run)`: the complete delivery passed server preflight and
compilation. The final delivery uses the same prescribed wrapper.

## Maintainer review fix (NT-cc reviewer, 2026-10-17)

One-definition-per-notion repair, no change of meaning: the delivered
`SSet.MarkedConeStraightening.oppositeFunctor` repeated, field for field, the landed
`SSet.SimplicialRightFibration.enrichedOp` (`Sheaf.CategoryTheory.SimplicialRightFibrationPresentation`,
node lem-coef-simplicial-right-fibration-presentation). The module now imports that
module publicly, opens `enrichedOp`, and uses it in `indexConeMap`, `indexConeMap_objects`,
`indexValueMap`, `indexValueMap_composition`, `IndexChange` and `Statement.indexChange`.
`oppositeFunctor` is removed from the module and from `lean.declarations`. The main
statement text is unchanged. Per-file compile of the fixed module through
`tools/nt_compile.py`: clean (no error, no warning).
