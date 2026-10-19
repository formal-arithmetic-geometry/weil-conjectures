## Worker report

Repair of the H3 return on immutable head `126aec7d6d56`. The retained returned
module was saved in `scratchpad/returned-126aec7d6d56.lean` before editing. I
compared its signature with the retained node record and compared the node with
the current shared main-branch node. The shared node has the same informal
statement, source, proof and original dependencies; the previously reviewed
addition of `lem-coef-infinity-pinch-comparison` is retained. The delivery wrapper
constructs the new commit on current `origin/newtargets-dag`; no direct Git
operation or edit of the shared repository was performed.

The module remains `lean/Sheaf/CategoryTheory/SourceAttachmentGluing.lean`, with
main declaration `SSet.Enhanced.coherent_source_attachment_gluing`. Its sole
postponed theorem is that declaration, with proof `sorry`. All helper data are
actual restrictions, projections, products, pullbacks, endpoint equations or
structures specifying coherent comparison data. No other DAG statement is
restated, and no new definition node or dependency-module repair is introduced.

### H3 repair: coherent limit and mapping-space comparison families

The returned head supplied unrelated pointwise limit comparisons and
mapping-space equivalences. Reconstruction alone had a naturality conjunct.
The additional conjunct `SourceAttachmentCoherentComparisons S κ E` now supplies
both identifications as maps of entire simplicial families, with arbitrary
parameter `T : SSet.{u}`. This parameter may have noninvertible edges. Thus the
source and target, the diagrams, and the supplied limiting cones can vary
through transformations, composable transformations, and higher simplices. The
parameter is not restricted to a set of objects or to a space.

`sourceAttachmentArrowFamily x y` is the actual pullback of `arrowEndpoints`
along `(x,y) : T ⟶ E × E`. Its fiber at a parameter vertex is the existing
`arrowMappingSpace`; the landed `right_pinch_comparison` identifies that fiber
naturally with the node's right-pinched `mappingSpace`. This is a presentation of
families of those same mapping spaces, not a replacement by Hom sets.
`SourceAttachmentFiberwiseEquivalence` requires a weak equivalence on every
strict vertex fiber and uses Mathlib's actual `pullback.map` for the comparison.

For the limit identification, `SourceAttachmentLimitFamily H` specifies a
simplicial apex family, an entire cone-arrow family and both endpoint equations.
Its `limiting` field is the existing `IsTerminal` predicate on the existing
`comma` cone category at every parameter vertex. The helper
`sourceAttachmentFamilyCone` constructs that actual vertex from the endpoint
equations. No new predicate for a different kind of limit is used.
`SourceAttachmentLimitComparisonFamily ℓ x` then gives a single comparison map
over `T`, a fiberwise weak equivalence, and `composition` with the actual supplied
cone family. Its triangle and endpoint-preserving homotopy are defined on the
whole parameter by `SourceAttachmentFamilyComposes`. In particular the triangle
witnesses cannot be picked independently at each parameter vertex. Restricting
this single map to any simplex, or pulling it back along `R ⟶ T`, restricts the
same comparison and all its triangle/homotopy data. The arbitrary parameter
includes the universal family of diagram/apex/cone data, so choosing that instance
and pulling it back gives simultaneous coherent choices for all instances.

For the displayed formula, `SourceAttachmentMappingFamily S T E` specifies two
entire diagram families and actual limiting-cone families for each target
boundary. Its `full`, `outside`, `components` and `matching` objects are the four
mapping-space families in the formula. The source products have one shared
parameter: they are arrow families in the product of the copies of `E`.
`SourceAttachmentMappingComparisonFamily` supplies the two base maps over `T`,
the comparison to the relative homotopy pullback, its parameter equation and
fiberwise weak equivalence, and its actual restriction/source-component
projection equations. `SourceAttachmentFamilyBaseMaps` characterizes both base
maps by coherent composition with the actual source and target cones and the
supplied matching-limit cone. All of those characterizations hold on whole
families, not just on vertex fibers.

The compatibility path is explicit. `sourceAttachmentRelativePath p` consists of
paths in the matching family whose projection to the parameter is constant along
the path. `sourceAttachmentRelativePullback` retains this path and both factors.
It does not admit a path that changes the parameter. The simplicial comparison
therefore retains the compatibility homotopy and every higher simplex. The field
`pullbackCompatibility` additionally requires the full equations of
`SourceAttachmentPullbackCompatibility` for every `r : R ⟶ T`: the new base maps
are the pullbacks of the same base maps, the comparison commutes with the
forgetful map `k`, both factor projections commute, and, explicitly,

```
k ≫ sourceAttachmentRelativePullbackPath pB a b =
  sourceAttachmentRelativePullbackPath (pullback.snd pB r) a' b' ≫
    (ihom Δ[1]).map (pullback.fst pB r)
```

The reindexed comparison is again over `R` and a weak equivalence on each fiber.
These equations keep the same compatibility path under base change, as the return
requires. The two pullback projections specify each reindexed base map uniquely;
the factor and path projections together specify `k`. Successive restrictions
therefore agree on all coordinates, including the higher path data.

The original pointwise conclusions and their actual-map characterizations remain
in the theorem. The new family clauses provide coherent versions of those same
identifications; they do not claim that every arbitrary choice of inverse or
composition is strictly natural. There is no added finiteness, directness, Reedy
fibrancy, nonemptiness, limit-existence or coefficient hypothesis.

### Hypothesis and clause correspondence

- Small category and universe: `{I : Type u} [Category.{u} I]`, all simplicial
  sets and parameters in `SSet.{u}`; `u` is arbitrary.
- Selected sources: `S : Set I`. The sole arrow hypothesis is `hS`, saying each
  arrow targeting a member of `S` is an `eqToHom`, including the identity-only
  endomorphism case.
- Outside category: `sourceAttachmentJ I S` is the full subcategory on `i ∉ S`.
- Boundary: `sourceAttachmentB I S s` is the outgoing `StructuredArrow` full
  subcategory whose codomain lies outside `S`; under `hS` these are exactly the
  nonidentity objects of the coslice. `sourceAttachmentT` is its codomain functor.
- Infinity category: `E : SSet.{u}` with `[Quasicategory E]`. Mathlib's nerve,
  inner-horn fillers and internal hom are reused.
- Actual source cones: the existential `κ` satisfies `IsSourceAttachmentCylinder`
  on all three edge types; `sourceAttachmentConeFamily` is the twice-curried
  actual restriction along that cylinder.
- Determination by restriction, source objects and cones: `g E` is an
  `IsFunctorEquivalence` into `sourceAttachmentData`; its three displayed
  projection equations give the actual restriction, source evaluation and cone
  arrow. The simplicial data include transformations and higher homotopies.
- Reconstruction naturality: the existing postcomposition conjunct specifies the
  data map on all three projections and requires commutation with `g`.
- Conditional limit representation: each supplied limiting `ℓ` gives `L` with
  `SourceAttachmentLimitComparison`, including weak equivalence and actual cone
  composition. The new `SourceAttachmentLimitComparisonFamily` supplies the
  coherent version varying the source, boundary diagram and supplied cone.
- Formula assumption: `ℓ s` is a cone on the actual restricted target boundary,
  and each is required to be `IsLimiting`. No independent arbitrary matching
  object is substituted: its actual apex `(ℓ s).1.1` is the matching object.
- Formula's first factor: `sourceAttachmentOutsideMaps S P Q` uses the mapping
  space between the actual restrictions of `P,Q` to `J`.
- Formula's second factor and base: `sourceAttachmentComponentMaps` and
  `sourceAttachmentMatchingMaps` are the genuine products of the indicated
  mapping spaces. Products use Mathlib's `piObj`.
- Formula's two maps: `SourceAttachmentBaseMaps` specifies restriction then
  composition with the source cone, and composition of a source component with
  the target cone, compared through the supplied limit representation. The new
  `SourceAttachmentFamilyBaseMaps` imposes these on whole varying families.
- Formula's identification: the pointwise `e` is a weak equivalence to the full
  path-model `simplicialHomotopyPullback`, with actual restriction and evaluation
  projections. The new mapping comparison family is its coherent version over
  varying `P,Q` and matching cones, with the explicit path-preserving reindexing
  equations described above.
- Equivalence detection: the last `∀ τ` is exactly equivalence on the outside
  restriction and on every selected source component, with no limit assumption.
- Naturality and homotopy pullbacks: `SourceAttachmentCoherentComparisons` and
  the reconstruction naturality clause cover the identifications. Relative
  pullbacks retain paths in spaces and their higher simplices, with both
  endpoint and path compatibility under arbitrary parameter restriction.

### Dependencies, sources and searches

I reopened the current statement and `lean` records of all three dependencies,
including the already landed pinch dependency added by the previous reader.

- `def-weil-pbc-simplicial-set`: Mathlib's `SSet` and its simplicial operators;
  the nerve and `Quasicategory` declarations already used in the returned file.
- `def-cbc-enhanced-diagrams-cones`:
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, in namespace `SSet.Enhanced`,
  supplies `mappingSpace`, `mappingSpaceMap`, `evaluation`, `constantDiagrams`,
  `comma`, `coneCategory`, `IsTerminal`, `IsLimiting`, `IsFunctorEquivalence`,
  `IsEquivalenceEdge` and `IsWeakHomotopyEquivalence`. I read their signatures and
  definitions, including the actual comma endpoint equations and right-pinched
  simplicial operators.
- `lem-coef-infinity-pinch-comparison`:
  `Sheaf.CategoryTheory.RightPinchComparison` supplies `arrowEndpoints`,
  `arrowMappingSpace`, `arrowMappingSpaceInclusion` and
  `right_pinch_comparison`. I read the full prism characterization, inverse
  homotopies, Kan assertions and naturality clause. The retained pinch helper
  selects the uniquely prescribed inclusion, as in the returned head.

The three proof-dependency nodes remain unstated; their proof-only imports remain
absent, as in the returned file. The theorem's seven-step docstring is retained
and step 6 now explains the parameterized comparison and path reindexing.

I reopened [Cisinski's book](https://cisinski.app.uni-regensburg.de/CatLR.pdf),
Propositions 7.4.2 and 7.4.11 and the proof of 7.4.11, especially the Cartesian
square of full functor infinity categories and the passage to parameterized
transformations. The broader source-attachment scope remains the DAG's recorded
degreewise generalization, not a claim that the printed finite-direct-category
proposition has arbitrary-small-category hypotheses. No Stacks tag is used.

Existing searches in the retained report and `searches.jsonl` remain applicable.
Additional searches made during this repair:

- LeanFinder via `msearch.py`: `Natural coherent families of mapping space
  comparisons over a simplicial parameter with homotopy pullback paths`. Eight
  hits, including ordinary Cech-nerve maps, path-object composition and nerve
  product comparisons; none states the required coherent comparison families.
- Loogle via `msearch.py`: `"pullback.map", "ihom"`. No hits.
- Grep via `msearch.py`: `arrowFamily|relativePath|mappingSpaceFamily` in
  `AlgebraicTopology`. No hits.
- Direct `rg` for `sourceAttachment`, this node ID, `arrowFamily` and
  `relativePath` in upstream `WeilConjectures` and project
  `lean/Sheaf/CategoryTheory`: no existing source-attachment statement; only the
  downstream finite-Reedy proof plan cites this node.
- Direct Mathlib read: `pullback.map` in `Pullback/HasPullback.lean` is exactly
  the induced map needed on parameter fibers and is reused. The existing
  `SSet.Homotopy` has domain `R ⊗ Δ[1]`; the family composition predicate fixes
  its endpoints through `fst R Δ[1]`, preserving the whole varying parameter.

### Edge cases and validation

The original edge cases remain included: empty `I`, empty `S`, all objects
selected, empty boundaries, parallel outgoing arrows, and cycles within `J`.
There is no nonempty or finite product hypothesis. Empty `E` and empty mapping
spaces remain allowed; no inhabitedness is inferred from the weak-equivalence
predicate. For empty boundaries only supplied terminal cones are used.

For the repair I additionally checked empty `T` and empty `R`, the terminal
parameter, simplex parameters `Δ[n]` in every degree, noninvertible parameter
edges, identity and iterated parameter restrictions, and varying limit apexes.
At `T = Δ[0]` the new comparisons have exactly the original mapping-space fibers
through the existing natural pinch equivalence. At `T = Δ[1]` they retain the
comparison along a coherent transformation; higher simplices retain its higher
compatibilities. The path object is relative to `T`, preventing an erroneous
path that changes the endpoints' parameter. The explicit reindexing equation
retains its entire interval-map coordinate, not merely its start and end.

No informal statement correction or `STATEMENT-DISPUTED` is needed. The node's
only changes against current main are `lean` and the retained addition to
`stmt_deps`. Every named helper is listed in `lean.declarations`, and
`lean.statement` is extracted verbatim from `theorem` through the text before
`:=`. All universes and variables are explicit under `autoImplicit false`.
There are no lines over 100 columns, no local notation, no private definitions,
and no additional theorem proofs.

The repaired file compiled with `scompile.py` in both sandbox and library modes
under the unchanged 60-second per-file limit, with no errors or non-sorry
warnings. The required `deliver2.py NJ lem-coef-infinity-source-gluing --no-push` dry run
printed `OK (dry run): commit f888fd89dc passes the preflight and compiles; nothing
pushed`. That run used the current main-branch base and checked exactly the module,
node and report. The second-reading section retained below is explicitly archived;
the fresh second reader reviews this H3 repair before delivering.

## Second reading by NJ

I read the current node record, its complete statement, proof steps, source
paragraph, and the repaired module. The source is Cisinski, *Higher Categories
and Homotopical Algebra*, Proposition 7.4.2 and Proposition 7.4.11 with proof,
printed pages 358--365. The printed propositions assume finite direct categories
and (for 7.4.11) Reedy fibrancy; the blueprint explicitly records the
degreewise arbitrary-small-category generalization used here. I therefore
checked the Lean against the node's stated generalization while retaining the
source hypotheses in this scope note.

Statement checklist, in order:

1. A small category is `{I : Type u} [Category.{u} I]`; the selected set is
   `S : Set I`, and `hS` says every arrow targeting `S` is an `eqToHom`.
   `sourceAttachmentJ` and `sourceAttachmentJIncl` render the full outside
   subcategory and its inclusion. Verdict: exact hypotheses and objects.
2. For each selected `s`, `sourceAttachmentB` is the full subcategory of
   `StructuredArrow s.1 (𝟭 I)` whose codomain is outside `S`, and
   `sourceAttachmentT` is its codomain functor to `sourceAttachmentJ`.
   Verdict: this is the outgoing coslice boundary with the identity removed
   under `hS`; parallel arrows are retained.
3. `sourceAttachmentRestrict` and `sourceAttachmentBoundary` use Mathlib's
   `nerveMap` and the recorded inclusions. Verdict: exact restriction and
   boundary diagrams.
4. `E : SSet.{u}` with `[Quasicategory E]` uses the recorded simplicial set,
   nerve, internal functor object, mapping spaces, cones and equivalences;
   no new infinity-category notion is introduced. Verdict: exact.
5. `sourceAttachmentData` stores an entire outside diagram simplex, each source
   apex simplex, and each boundary arrow simplex with both endpoint equations.
   `sourceAttachmentConeFamily` is the actual cylinder evaluation. Verdict:
   coherent cones, transformations and higher simplices are all retained.
6. The first conclusion supplies cylinders, an `IsFunctorEquivalence` `g`, its
   restriction/apex/arrow projections, and postcomposition naturality through
   an explicitly projected data map `d`. Verdict: all reconstruction clauses
   and quantifier order match the node.
7. The limit clause supplies `hB`, quantifies every boundary diagram, limiting
   cone and vertex, and gives `L` with `SourceAttachmentLimitComparison`.
   Verdict: it is conditional on the displayed limit and includes the actual
   cone composition and weak equivalence; no limit existence is assumed.
8. The mapping formula uses the actual outside factor, component product and
   supplied cone apex product. `SourceAttachmentBaseMaps` characterizes both
   maps by coherent triangles and endpoint-preserving homotopies; `e` is a weak
   equivalence with the actual restriction and source-evaluation projections.
   Verdict: exact homotopy-pullback formula, including the path coordinate.
9. `SourceAttachmentCoherentComparisons` quantifies arbitrary simplicial
   parameters, varying diagrams, endpoints and limiting cones; the comparison
   families are fiberwise weak equivalences and preserve factor, path and
   reindexing coordinates. Verdict: this is the node's naturality clause with
   all higher compatibility data retained.
10. The final `∀ τ` detects equivalences exactly by restriction to `J` and all
    selected source evaluations. Verdict: exact conclusion and quantifiers.

Edge cases checked: `S = ∅`, `I = ∅`, all objects selected, empty boundaries,
parallel outgoing arrows, cycles inside `J`, empty mapping spaces and empty
`E`, dimension-zero simplices, empty parameter `T` and reindexing parameter
`R`, terminal parameters, noninvertible parameter edges, and iterated
restrictions. No nonemptiness, finiteness, directness, Reedy, characteristic,
scheme, coefficient, or integer parameter is present or needed. The boundary
and product definitions cover empty index families without an implicit
inhabitedness assumption.

Existing-notion searches: I searched `Mathlib`, upstream
`WeilConjectures`, project `lean/Sheaf`, and the upstream name index for
`sourceAttachment`, `coherent_source_attachment_gluing`, `arrowFamily`, and
`relativePath`; none exists. LeanFinder/Loogle searches for coherent source
gluing, nerve/structured-arrow mapping comparisons, and parameterized homotopy
pullbacks found only ordinary `GlueData`, nerve primitives, and pullback
primitives. The recorded dependency declarations were opened: Mathlib's
`SSet`, `EnhancedDiagramsCones`'s `coneCategory` family, and the landed
`right_pinch_comparison`; each matches the dependency node. The Cisinski PDF
source was read directly at both cited propositions.

Mismatches found and repaired in the returned head were verified in the current
file: the boundary was changed from incoming `CostructuredArrow` to outgoing
`StructuredArrow`; arbitrary cone vertices and unrelated apex families were
replaced by actual coherent source data and supplied limiting cone apexes; the
first factor became the outside restriction mapping space; the base maps and
comparison gained their actual projections, coherent triangle conditions and
full compatibility paths; reconstruction naturality and parameterized
comparison families were added. No further mismatch remains. The current
`lean.statement` is byte-for-byte the theorem signature. The sole `sorry` is
the named target theorem, and every helper has a source and
`(blueprint: lem-coef-infinity-source-gluing)` docstring. The module compiled
through the required `scompile.py` wrapper with no errors or non-sorry warnings.

## Earlier second reading (a previous round; superseded)

Archive notice from the repair worker: the reading below is the retained independent
reading of the returned head `126aec7d6d56`, before this H3 repair. It is not a new
independent reading of the repaired coherent comparison families. A fresh second
reader must review this repair before delivery. The former claim that reconstruction
naturality alone covered the formula is superseded by the H3 repair above.

I independently opened the complete DAG statement and all seven proof steps, the
sandbox module, both statement-dependency nodes and their declarations, Mathlib's
`StructuredArrow`/`CostructuredArrow`, nerve, products, and `Quasicategory`, and the
landed `EnhancedDiagramsCones` and `RightPinchComparison` modules. The worker report
above describes the original module; the repairs and final correspondence below
supersede its claims about that original signature.

Source reading: this item has no Stacks source. I read Cisinski,
<https://cisinski.app.uni-regensburg.de/CatLR.pdf>, revision July 30, 2026,
printed pp. 358--365 (PDF pp. 373--380), particularly Proposition 7.4.2 and
Proposition 7.4.11 with its proof. The latter assumes a finite direct category and
a Reedy fibrant presheaf; its proof uses the fat-cone comparison, equivalence on
restriction fibers, and the functor-category Cartesian square. The DAG explicitly
records an agent generalization to arbitrary small categories, with a degreewise
nerve-pushout proof and separate excision/join-cone prerequisites. Accordingly the
Lean retains exactly the no-incoming-arrow hypothesis and does not silently impose
finiteness, directness, fibrations, or Reedy fibrancy. The module source paragraph
now states that scope correctly.

Object, hypothesis, and conclusion checklist:

1. Small ordinary category in any fixed sufficiently large universe:
   `{I : Type u} [Category.{u} I]`; all simplicial sets are `SSet.{u}`. Verdict:
   correct common-universe encoding, with arbitrary `u`; there is no independent
   smaller test-object universe or extra size equality between unrelated sites.
2. Selected source set and its sole arrow hypothesis: `(S : Set I)` and
   `hS : ∀ ⦃i j⦄, j ∈ S → ∀ f : i ⟶ j, ∃ h : i = j, f = eqToHom h`.
   Verdict: exactly every incoming arrow is an identity, including exclusion of
   nontrivial endomorphisms at a selected source.
3. Outside full subcategory: `sourceAttachmentJ I S` is
   `ObjectProperty.FullSubcategory (fun i ↦ i ∉ S)`;
   `sourceAttachmentJIncl` is Mathlib's inclusion. Verdict: exact.
4. Outgoing boundary and its codomain functor: `sourceAttachmentB` now uses
   `StructuredArrow s.1 (𝟭 I)`, restricted by `f.right ∉ S`;
   `sourceAttachmentT` takes `.right` on objects and morphisms. Verdict: exact
   coslice boundary under `hS`. Removing the identity is equivalent to the
   codomain being outside `S`: every arrow landing back in `S` must be that
   identity. Parallel arrows remain different objects of this boundary.
5. Infinity category and ordinary nerve: `∀ (E : SSet.{u}) [Quasicategory E]`,
   Mathlib's `nerve` and `nerveMap`, and the existing internal hom `(ihom K).obj E`.
   Verdict: exact; horn fillers and nerves have not been redefined.
6. Actual source cones and their restriction: the existential cylinder `κ s`
   satisfies `IsSourceAttachmentCylinder S s (κ s)`. Its three edge formulas are
   identity at the source, the actual outgoing arrow for a crossing edge, and
   the codomain morphism at the final end. Since the target is an ordinary nerve,
   these determine the simplicial map in every degree. `sourceAttachmentConeFamily`
   is the real twice-curried evaluation along that cylinder. Verdict: the cones
   are tied to the original diagram and its actual arrows; there is no free cone
   unrelated to the diagram.
7. Reconstruction, including transformations and higher homotopies:
   `sourceAttachmentData S E` has an entire outside-diagram simplex and, for each
   source, an apex simplex and an arrow simplex in its boundary functor object,
   with both endpoint equations in every degree. The comparison family `g E`
   satisfies `IsFunctorEquivalence (g E)` and has exactly the restriction, apex,
   and cone-arrow projections specified by the node. Verdict: full coherent
   reconstruction, not merely existence of object data or equivalence of Hom sets.
   The comma-cone encoding is the existing dependency's convention; the node's
   join-cone comparison is its recorded proof of equivalence with left join cones.
8. Naturality of reconstruction: the next conjunct quantifies every enhanced
   functor `f : E ⟶ E'` and a data map `d`, specifies all its restriction/apex/arrow
   projections, and requires `(ihom (nerve I)).map f ≫ g E' = g E ≫ d`.
   Verdict: genuine postcomposition naturality. The three jointly injective
   data projections uniquely specify `d`, so it is not an arbitrary map.
9. Conditional matching-limit representation: for every outside diagram `H`,
   source `s`, supplied cone `ℓ`, hypothesis `IsLimiting ... ℓ`, and vertex `x`,
   the theorem supplies `L : mappingSpace E x ℓ.1.1 ⟶ ...` satisfying
   `SourceAttachmentLimitComparison`. This predicate requires weak equivalence
   and composition with the actual cone arrow. Verdict: exactly the conditional
   space-valued universal property, without asserting existence of a limit.
10. Supplied matching limits of the target diagram: the mapping clause quantifies
    `ℓ s : coneCategory (sourceAttachmentBoundary S (sourceAttachmentRestrict S Q) s)`
    and requires each to be limiting. Its matching object is literally
    `(ℓ s).1.1`, used by `sourceAttachmentMatchingMaps`. Verdict: exact; no arbitrary
    vertex family `M` is substituted for these apexes.
11. First factor of the formula: `sourceAttachmentOutsideMaps S P Q` is the mapping
    space in the internal functor object on `nerve (sourceAttachmentJ I S)`, between
    the actual restriction images. Verdict: the required restricted mapping space.
12. Product factor and base: `sourceAttachmentComponentMaps` is the product of
    `mappingSpace E P_s Q_s`; `sourceAttachmentMatchingMaps` is the product of
    `mappingSpace E P_s (ℓ s).1.1`. `simplicialFamilyProduct` is now explicitly an
    abbreviation of Mathlib's existing `piObj`, with `Pi.π` projections.
    Verdict: genuine products of spaces, including empty and infinite products.
13. The two maps to the base: `SourceAttachmentBaseMaps S hB κ P Q ℓ L a b`
    requires, for every source, coherent composition of the actual source cone
    with the restricted outside transformation, or the constant-diagram image of
    the source-component map with the actual target cone. The result is compared
    through the limit comparison `L s`. `SourceAttachmentComposes` uses a simplex
    of the full triangle functor object and endpoint-preserving simplicial
    homotopies, on the entire parameter space. Verdict: both maps are specified
    by the node's composition and limit universal property, up to their proper
    coherent homotopy, not just given their source and target.
14. Displayed formula: `e` goes from the full diagram mapping space to
    `simplicialHomotopyPullback a b`, is a weak homotopy equivalence, and its two
    factor projections are required to equal actual `mappingSpaceMap` restriction
    and actual evaluation at each source. Verdict: the specified mapping-space
    identification. The homotopy pullback contains the full interval path in its
    base; the triangle/comparison conditions specify the natural homotopy classes
    of the base maps. Together with the canonical full simplicial comparison `g`,
    these are the natural mapping-space formula, rather than an unrelated weak
    equivalence of bare spaces. The limit comparison is quantified universally
    after its existence clause, so no special noncanonical comparison is assumed.
15. Equivalence detection: the final `∀ τ` asserts `IsEquivalenceEdge` precisely
    when `sourceAttachmentRestrictEdge S τ` and every source evaluation are
    equivalence edges. Verdict: exact, on all transformations, with no invertibility
    hypothesis imposed on general diagram arrows.

Mismatches repaired:

- The original boundary was `CostructuredArrow (𝟭 I) s`, i.e. incoming arrows.
  Under `hS` its proposed boundary is empty even for a source with outgoing arrows.
  Replaced it by the outgoing `StructuredArrow` and corrected both codomain fields.
- The original first conjunct supplied arbitrary cone vertices with an unconstrained
  apex family and only a tautological equality between those supplied vertices.
  It neither tied a cone to `P_s` and P's arrows nor asserted reconstruction,
  transformations, or higher homotopies. Replaced it by the fully specified
  simplicial data construction and canonical functor equivalence.
- The original first factor of the supposed homotopy pullback was the full diagram
  mapping space itself. Replaced it by the restricted outside mapping space.
- The original `M s` had no equality with the supplied limiting cone's apex.
  Removed that unrelated family; the base now uses the actual cone apexes.
- The original statement omitted representation of cones by maps to a matching
  limit. Added the conditional, explicitly compositional weak-equivalence clause.
- The original base maps `a,b` were arbitrary existential maps. Added the coherent
  triangle and fixed-endpoint homotopy characterizations of both maps, using the
  actual source cones and supplied matching limits.
- The original comparison `e` had no relation to restriction or source evaluation.
  Its factor projections are now required to be those actual maps.
- The original statement had no naturality assertion. Added naturality of the
  entire reconstruction comparison, including all cone-arrow simplices.
- Added source/blueprint references to every helper docstring and the complete
  seven-step proof plan to the theorem. Corrected the module's source-scope wording.
- Listed all helper declarations in the node's `lean.declarations`, kept its
  `lean.statement` verbatim identical to the final theorem signature, and added
  the already landed `lem-coef-infinity-pinch-comparison` to `stmt_deps`.

The informal node statement, proof, source, and targets are unchanged. There is no
`statement_change`, no new node, and no dependency-module repair. The additional
pinch dependency was opened and checked against its node and exact theorem. Its
comparison family is uniquely specified in each degree by `rightPinchPrism` after
its monomorphic arrow-space inclusion. `sourceAttachmentPinch` only names that
uniquely determined map; it does not choose an object from an uncharacterized
existence theorem. Every other new helper has real product, subtype, projection,
restriction, or exponential-adjunction data. Exactly one `sorry` remains, the
named theorem for this DAG node; no theorem has been proved in stage 2.

Edge cases checked independently:

- `S = ∅`: cylinders and source families are empty, products terminal, and the
  reconstruction is restriction to the whole category; no `Nonempty` is assumed.
- `I` empty: necessarily `S` empty, and both functor/data objects describe the
  unique empty diagram, also when `E` is empty.
- A source with empty boundary: its cone-arrow object retains its apex; the limit
  clause applies exactly when a terminal object is supplied. No terminal object
  of an arbitrary `E` is asserted to exist.
- All objects selected: `hS` leaves only identity arrows; the data are independent
  source values, with the empty boundary condition at each source.
- Parallel outgoing arrows and cycles confined to `J`: allowed by the boundary
  category and the nerve/cylinder formulation. No directness or thinness is assumed.
- Empty mapping spaces and empty `E`: neither the weak-equivalence predicate nor
  the reconstruction assumes inhabitedness. For nonempty `I`, there are no diagrams
  into empty `E`; the functor/data equivalence still has its correct empty case.
- Dimension zero: `sourceAttachmentData` imposes the actual cone-arrow endpoints,
  while all higher dimensions impose the same equations on whole simplices.
- There is no coefficient ring, characteristic, scheme, or separate integer `n`
  parameter in this node, so zero objects, empty schemes, and characteristic cases
  impose no omitted hypotheses. All dimensions and the empty shapes are covered.

Independent searches (not just the worker's search terms):

- LeanSearch: `Homotopy coherent diagram source gluing along coslice categories and
  mapping spaces` returned ordinary topological/categorical GlueData only.
- LeanFinder: `Natural transformation gives simplicial map nerve category times
  interval to nerve of another category` returned `nerveMap` and nerve-adjunction
  primitives, not the gluing statement.
- LeanFinder: `Diagram on nerve reconstructed by coherent cones at sources mapping
  Kan spaces source boundary` returned `Nerve.strictSegal`, coskeletality, and nerve
  edge primitives; none gives the coherent source-attachment result.
- Loogle: `"nerveMap", "prod"` and `"StructuredArrow", "nerve"` gave no hits.
- Grep search service: `homotopyPullback|fatJoin|sourceAttachment|varyingCone` and
  `coslice|[Ss]ource.*[Gg]lu|[Gg]lu.*[Cc]one` in AlgebraicTopology gave no hits.
- Direct `rg` of Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`, and the
  upstream name index for the declaration/helper names found no existing declaration.
  Broader searches found the existing enhanced-diagram definitions, right-pinch
  comparison, ordinary categorical products, and unrelated ordinary gluing. I
  opened those relevant declarations and reused them. No duplicate statement is
  being delivered and no missing independent definition node is required.

Validation: the final module compiles cleanly through the prescribed `scompile.py`
wrapper, as both a sandbox and library module, under the unchanged 60-second limit.
There are no errors or non-sorry warnings, unbound variables, local notation or
instances, private declarations, or lines over 100 columns. The JSON signature and
source signature were compared literally before delivery.
