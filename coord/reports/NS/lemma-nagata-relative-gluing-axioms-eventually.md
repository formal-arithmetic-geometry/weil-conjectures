## Worker report

The module states `AlgebraicGeometry.nagataRelativeGluingAxiomsEventually`, with
`sorry` as its only theorem proof. Its conclusion concerns exactly
`nagataRelativeGluingValidDatum D c hc i₀ f R P A`, the canonically transported
relative datum at the already defined selected common equality stage.
The helper `NagataRelativeGluingTransport.HasGluingAxioms` explicitly renders
this node's conclusion; it has a complete Prop-valued definition and assumes
none of the equations. It belongs to the same notion and is listed in
`lean.declarations`, as authorized by the missing-helper rule. There are no
new DAG nodes, dependency repairs, or statement changes.

Hypotheses inherited from the sole statement dependency:

- `I : Type u`, `[Preorder I]`, `[Nonempty I]`, `[IsDirected I (· ≤ ·)]`:
  the nonempty directed indexing preorder. It shares the schemes' universe.
- `D : Iᵒᵖ ⥤ Scheme.{u}`, `c : Cone D`, `hc : IsLimit c`: the inverse
  system and its limit; the affine-transition instance binds every transition.
- `i₀ : I`, `CompactSpace (D.obj (op i₀))`, and
  `QuasiSeparatedSpace (D.obj (op i₀))`: the fixed initial qcqs base stage.
- `X : Scheme.{u}`, `f : X ⟶ c.pt`, `CompactSpace c.pt`, and
  `QuasiSeparatedSpace c.pt`: the original scheme over the qcqs limit base.
- `LocallyOfFinitePresentation f`, `QuasiCompact f`, `QuasiSeparated f`:
  the original morphism of finite presentation, as in the raw-datum interface.
- `R : NagataRelativeGluingDatum D c hc i₀ f`: all fixed raw descent data,
  including the finite chart/piece indices, binary upper bounds, and auxiliary order.
- `P : NagataRelativeRawInclusions D c hc i₀ f R`: canonical inclusions,
  characterized by their projections, as prescribed by the dependency.
- `A : NagataRelativeGluingValidStageData D c hc i₀ f R P`: precisely the
  compactness and limit-equality choices for the finite open list and the
  finite-presentation, affine-cover, generator and coefficient choices for
  the finite map list. These are not assumptions of gluing at the selected stage.

Conclusion, clause by clause: inside the helper's definition, `a`/`b` are the
actual transported left/right inclusions, `g`/`h` are the transported
forward/backward maps followed by the corresponding chart inclusions, and
`w`/`v` are unions of the actual transported left/right overlap opens.
These local lets occur only in a definition, never in the theorem signature.

- Matching overlap opens includes `∀ j, w j j = ⊤` and
  `∀ j k, w j k = v k j`, the diagonal coverage and both orientations of
  the matching-open list of the valid-stage definition.
- Matching in the forward direction is
  `∀ j k z l, (g j k l).left ⁻¹ᵁ w k z = (a j k l).left ⁻¹ᵁ w j z`.
  Matching in the backward direction is
  `∀ j k z l, (h j k l).left ⁻¹ᵁ w j z = (b j k l).left ⁻¹ᵁ w k z`.
  The latter is explicitly present, although deduced in the proof by reversed
  orientation and locality on the covering intersections.
- Inverse maps are the two compositions `T.forward ≫ T.backward = 𝟙`
  and `T.backward ≫ T.forward = 𝟙` on every indexed piece.
- The next three conjuncts give forward agreement on canonical intersections
  of left pieces, backward agreement on canonical intersections of right
  pieces, and agreement of forward maps with the reversed backward maps.
  These are the actual parallel pairs prescribed by the dependency list;
  they ensure that the piecewise maps express overlap maps.
- `∀ j l, g j j l = a j j l` gives the prescribed diagonal identity.
- The final conjunct quantifies over every chart triple and all three piece
  indices. Its source is the iterated pullback of `g j k l` and `a k z m`,
  intersected with the direct piece by a pullback over chart j. Equality of
  the two resulting composites is exactly `g_kzm g_jkl = g_jzn` on the
  common domain fixed by the valid-stage definition. All maps and pullbacks
  live in `Over S`; nothing replaces the canonical domain by an arbitrary map.

Dependencies used:

- Public import `Sheaf.AlgebraicGeometry.NagataRelativeGluingValidStage`:
  `NagataRelativeGluingTransport`, `NagataRelativeRawInclusions`,
  `NagataRelativeGluingValidStageData`, `nagataRelativeGluingValidDatum`.
  Read its complete module, including the open/map relation lists and transports.
- That module publicly supplies `NagataRelativeGluingDatum` from
  `Sheaf.AlgebraicGeometry.NagataRelativeGluingDatumDescent`; read its full
  structure, raw-stage fields, and source docstring.
- Proof imports: `Sheaf.AlgebraicGeometry.RelativeFiniteAffinePresentation`
  (`RelativeFiniteAffinePresentation`), `Sheaf.Order.DirectedFiniteUpperBound`
  (`le_directedFiniteUpperBound`),
  `Sheaf.AlgebraicGeometry.NagataMorphismEqEventually`
  (`nagataMorphismEqEventually`), and
  `Sheaf.AlgebraicGeometry.NagataQCOpenEqEventually`
  (`nagataQCOpenEqEventually`). Read these signatures and docstrings.
- `lemma-nagata-relative-gluing-datum-descends` currently has neither `lean`
  nor a Mathlib match, so there is no proof module to import for it. It is
  needed only by the subsequent proof, not to type this statement; no wait
  or duplicate interface is introduced.
- Mathlib's ordinary `Over`, composition, identities, pullbacks, open suprema
  and inverse images are used, without private replacements.

Edge cases checked before writing: empty schemes and empty chart index sets
are allowed; all chart quantifiers then are vacuous. Empty overlap-piece
indices are allowed and their unions are bottom; diagonal coverage then
forces the corresponding chart to be empty, as required. No nonemptiness of
charts or overlaps is assumed. Repeated chart indices are included, including
all diagonal and inverse identities. No strict inequality excludes the
selected stage itself. Arbitrary preorder equivalences of indices are
allowed; no antisymmetry or compatibility of the auxiliary linear order with
the directed preorder is added. All common domains are actual fibre products
over the current base. No gluing construction or existence conclusion is added.

Searches for an existing declaration:

- `msearch.py ... leanfinder` query: "Finite scheme gluing overlap open
  equalities inverse identities triple cocycles hold at a selected sufficiently
  large stage". Eight hits, concerning `Scheme.Cover.gluedCover`, its cocycle
  lemmas and gluing morphisms. None asserts equations at this selected stage.
- `msearch.py ... loogle` query: `AlgebraicGeometry.Scheme.GlueData`.
  Twelve hits concerning bundled gluing data and its glued scheme/open cover.
  Read Mathlib's full `Scheme.GlueData` docstring and signature: it assumes
  gluing axioms, uses one overlap per pair, and does not assert descent to
  the chosen relative stage. Thus it cannot replace this theorem or its
  explicit predicate on the existing unbundled transported piece data.
- `msearch.py ... grep` query:
  `gluing.*eventually|cocycle.*eventually|structure GlueData`, subdirectory
  `AlgebraicGeometry`: one hit, the Mathlib `GlueData` structure above.
- `rg` of the upstream project and `lean/Sheaf` for
  `relative.*[Gg]luing|GluingAxioms|gluing_axioms`: existing raw/valid-stage
  data, unrelated blowup/relative gluing constructions, and references to
  this node; no statement of this theorem.
- `grep -rn` of the upstream project for the exact node id: no matches.
- `rg` of `dag/lean_names_upstream.json`, DAG nodes, Mathlib, upstream and
  `lean/Sheaf` for `HasGluingAxioms|nagataRelativeGluingAxiomsEventually`:
  no matches before writing.

Validation: the delivered module compiled cleanly using the prescribed
`scompile.py NS lemma-nagata-relative-gluing-axioms-eventually` server tool
(default 60-second per-file limit); no errors or warnings. Only the sandbox
contains newly written source. No source-based correction or mathematical
statement dispute was found. The theorem docstring records all four DAG
proof steps, including the backward-domain argument.

## Second reading by NS

I independently read the item's JSON and blueprint source (order 361), its sole
statement dependency's JSON and complete module (order 360), the raw-datum
structure and its component records (order 358), the finite relative affine
presentation, and the signatures/docstrings of the three eventual-equality and
upper-bound proof interfaces. I also read Stacks `limits.tex`,
`lemma-descend-finite-presentation` (01ZM), statement and proof, especially the
passage constructing the gluing datum at i5. The blueprint is the direct source;
Stacks explains its finite open-equality and morphism-equality argument. Stacks
assumes qcqs stages throughout; here the fixed qcqs stage and affine transitions
supply the needed qcqs tail, and the limit is qcqs. No Noetherian, separatedness
of f, field, or characteristic hypothesis belongs to this statement.

My object/hypothesis/conclusion checklist, matched against the actual Lean:

- A nonempty directed indexing set and an inverse system with affine transitions:
  `I : Type u`, `Preorder I`, `Nonempty I`, `IsDirected I (· ≤ ·)`,
  `D : Iᵒᵖ ⥤ Scheme.{u}`, and the instance on every `D.map t`. Correct;
  antisymmetry is unnecessary, and no auxiliary linear order is identified
  with this preorder.
- Its limit S: `c : Cone D`, `hc : IsLimit c`; S is `c.pt`. Correct;
  an arbitrary cone without its universal property is not substituted.
- Fixed qcqs initial stage: `i₀`, `CompactSpace (D.obj (op i₀))`, and
  `QuasiSeparatedSpace (D.obj (op i₀))`. Correct.
- Original finite-presentation map to the qcqs limit: `{X : Scheme.{u}}`,
  `f : X ⟶ c.pt`, the two qcqs instances on `c.pt`, and
  `LocallyOfFinitePresentation f`, `QuasiCompact f`, `QuasiSeparated f`.
  Correct; these are precisely the existing raw-datum interface's parameters.
  The qcqs limit instances express a consequence of the base assumptions.
- The fixed raw datum, with all descent choices, finite chart/piece families,
  fixed pairwise upper bounds and auxiliary order: `R : NagataRelativeGluingDatum
  D c hc i₀ f`. Correct. Its charts, overlap opens, and two maps are tied to
  the original presentation and canonical base changes by its component fields.
- Canonical raw inclusions: `P : NagataRelativeRawInclusions ... R`.
  Correct: `left_fst`, `right_fst` and over-base typing determine their two
  projections; P does not introduce arbitrary inclusions.
- All choices defining the named common stage: `A : NagataRelativeGluingValidStageData
  ... R P`. Correct: its `opens` retain compactness and equality at the limit;
  its `maps` retain the actual morphism-equality-stage choices. Neither field
  assumes the eventual gluing equations. The valid stage is the selected upper
  bound of exactly the raw stage and these equality stages.
- The datum at that exact stage: the conclusion applies `.HasGluingAxioms`
  to `nagataRelativeGluingValidDatum D c hc i₀ f R P A`. Correct: opening this
  definition shows `nagataRelativeGluingAtStage` with the named stage and
  canonical `Over.pullback` of every object and arrow, and inverse-image opens.
  There is no replacement existential stage or assertion about the raw stage.
- Matching overlap opens: in the predicate, `w` and `v` are the suprema of
  `T.leftOpen` and `T.rightOpen`. `∀ j, w j j = ⊤` gives the diagonal cover;
  `∀ j k, w j k = v k j` gives the reversed-orientation cover. Correct.
- Matching domains in both directions: the third and fourth conjuncts are
  `(g j k l).left ⁻¹ᵁ w k z = (a j k l).left ⁻¹ᵁ w j z` and
  `(h j k l).left ⁻¹ᵁ w j z = (b j k l).left ⁻¹ᵁ w k z`.
  Correct for every ordered chart triple and every relevant piece. Here
  g/h compose the actual forward/backward arrows with b/a, respectively.
- Inverse maps: the fifth conjunct states both composites equal identities
  on the actual left and right piece objects. Correct; both directions appear.
- Piecewise interpretation of the overlap maps: the next three conjuncts
  give forward agreement on left-piece intersections, backward agreement on
  right-piece intersections, and forward/reversed-backward agreement.
  Correct: each intersection is the categorical pullback of the indicated
  inclusions in `Over S`, exactly as in the dependency's map-relation list.
- Diagonal identity: `∀ j l, g j j l = a j j l`. Correct.
- All triple-overlap cocycles: the final universal quantifier ranges over
  j,k,z,l,m,n. Its first pullback forms the composite domain of g_jkl and
  g_kzm; its second pullback intersects this with the direct j,z piece.
  The left composite is the two-step map and the right composite is the
  direct map, both into chart z. Correct, with precisely the dependency's
  canonical domain and without restricting to distinct indices.

These additional piecewise/diagonal equations explicitly render the gluing
axioms already specified by the dependency's lists, rather than strengthening
this node with an unrelated property. The helper predicate has real Prop-valued
data (a conjunction), contains no postponed construction, and is correctly
listed in `lean.declarations`. No new definition node or dependency module was
introduced; H12/H13 therefore require no additional delivery review. The item
has no statement_change and needs none. The missing raw-datum-descends theorem
is a proof dependency only; its absence does not prevent stating this result.

Edge cases: the index set is nonempty by the source and a fixed i₀ is supplied;
empty charts and empty overlap families remain allowed. Empty unions are bottom,
so diagonal coverage has the appropriate empty-chart meaning. Empty schemes,
zero coordinate rings and presentations with zero generators or relations are
not excluded. There is no characteristic restriction. Universe u is bound and
arbitrary; scheme and inverse-system index universes follow the project's
convention. All finite chart/piece index types come from the existing datum.
Repeated indices, including the full diagonal, are universally quantified.
No strict inequality discards the selected stage itself.

Independent searches: `msearch.py` leanfinder query "Simultaneous descent of
identity inverse and associativity equations for finitely many transition
isomorphisms of schemes" returned eight ordinary gluing/pullback cocycle
lemmas; none asserts this selected-stage result. Loogle query
`AlgebraicGeometry.Scheme.GlueData` returned twelve hits. I opened its structure
and docstring: it assumes gluing conditions on one overlap per pair, whereas
this theorem establishes equations on the already defined transported pieces.
An independent `rg` over Mathlib AlgebraicGeometry, upstream WeilConjectures,
and this project's Sheaf modules searched `HasGluingAxioms`, the theorem name,
and cocycle/gluing with eventually/limit. It found generic relative gluing,
upstream approximation, and unrelated cohomology material, with no exact
replacement declaration or duplicate predicate.

No mismatch was found. I preserved the Lean and node record unchanged and
added this second-reading account. All variables/universes are explicitly
bound, there is no file-local notation/instance or private copy, and the only
new theorem has a whole `sorry` proof. The module and both declaration
docstrings carry the source and blueprint tag. The theorem docstring follows
all four node proof steps, including the reversed-orientation local argument
for backward domain matching. The recorded `lean.statement` is verbatim equal
to the source signature. Validation uses only the prescribed server scompile
and deliver2 preflight, with the default per-file timeout.
