## Worker report

The module `Sheaf.AlgebraicGeometry.NagataSeparatedDescentStage` defines the selected
index `AlgebraicGeometry.nagataSeparatedDescentStage`, the transition of the same witness,
the canonical base-changed model `nagataSeparatedDescentModel`, and its structure map
`nagataSeparatedDescentMap`. No data is supplied by `sorry` or selected from a
postponed existence theorem. The selection theorem is the fully proved upstream
`AlgebraicGeometry.Scheme.exists_isSeparated_pullback_snd`.

Hypothesis and clause correspondence:

- “Let X → S”: `X : Scheme.{u}`, `f : X ⟶ c.pt`; the limiting base is `c.pt`,
  with `D : Iᵒᵖ ⥤ Scheme.{u}`, `c : Cone D`, and `hc : IsLimit c`.
- “Separated”: `[IsSeparated f]`.
- “Of finite presentation”: `[LocallyOfFinitePresentation f]`, `[QuasiCompact f]`,
  `[QuasiSeparated f]`. These are the existing family’s encoding of finite presentation.
- “Start from its constructed finite-stage model”: precisely the parameters `R`, `P`,
  `A`, `G`, `B`, `E` of the landed finite-presentation descent construction. Its stage is
  `nagataRelativeGluingValidStage D c hc i₀ f R P A`; its model map is
  `nagataFinitePresentationDescentMap D c hc i₀ f R P A G B`. There is no arbitrary
  replacement model or independently supplied map to X.
- The finite-presentation model’s established properties are explicit instance inputs:
  locally of finite presentation, quasi-compact and quasi-separated for this exact map,
  and `IsIso` for `nagataFinitePresentationDescentComparison … E`. The quasi-compact,
  quasi-separated stage-base instances are also explicit, as required by the upstream
  existence theorem. The remaining diagram, starting-stage and limit-base hypotheses
  are inherited verbatim from the landed construction. No property of the selected
  later model is assumed.
- “Choose one witness from lemma-nagata-separated-descent-stage-exists”: the body calls
  `Classical.choose (Scheme.exists_isSeparated_pullback_snd hc …)` on the square supplied
  by `nagataFinitePresentationDescent_isPullback`. That square uses the inverse of the
  existing constructed comparison followed by `pullback.fst`, and the original map f.
- “Define lambda_sep … to be the index”: `unop` of that chosen cofiltered-system index.
  `nagataSeparatedDescentTransition` selects the arrow from the same existential witness,
  so its type expresses that the selected stage is later than the relative stage.
- “And X^sep … to be the model recorded by that witness”: the upstream witness records
  an index and arrow, and its separatedness predicate specifies `pullback.snd p (D.map t)`.
  Accordingly `nagataSeparatedDescentModel` is exactly `pullback p (D.map t)`, and
  `nagataSeparatedDescentMap` is exactly its second projection.
- “Eventual separatedness and comparison properties … separately below”: no such
  conclusion is made here. Those properties remain for `lemma-nagata-separated-eventually`.

The only postponed proof is the named theorem
`AlgebraicGeometry.nagataFinitePresentationDescent_isPullback`. Its complete proof plan
is in its docstring: transport the canonical cartesian square along the isomorphism
of the already constructed comparison, using `E.comparison_base` to identify the
lower projection. It has no chosen data. It is a typing/property helper for this
node, and carries this node’s blueprint reference.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.NagataFinitePresentationDescent`:
  `NagataFinitePresentationGluingData`, `NagataFinitePresentationBaseMap`,
  `NagataFinitePresentationComparisonData`, `nagataFinitePresentationDescentMap`,
  `nagataFinitePresentationDescentComparison` (full module read).
- Through that public import, `Sheaf.AlgebraicGeometry.NagataRelativeGluingValidStage`:
  `NagataRelativeRawInclusions`, `NagataRelativeGluingValidStageData`,
  `nagataRelativeGluingValidStage`, `nagataRelativeGluingValidDatum`, and
  `NagataRelativeGluingDatum` from `NagataRelativeGluingDatumDescent`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`:
  `Scheme.exists_isSeparated_pullback_snd` (exact signature, docstring, and fully proved
  body inspected). This is the existence dependency’s actual recorded declaration,
  not the unrelated one-step descent existence theorem.
- Mathlib’s `CategoryTheory.Limits.IsPullback`, `pullback`, `pullback.fst`,
  `pullback.snd`, `CategoryTheory.inv`, and `Classical.choose`/`choose_spec`.

Edge cases checked: I is nonempty and directed exactly as in the predecessor, so an
empty index system is not silently admitted. A one-index or constant system is allowed:
the selected transition may be the identity; no strict inequality is imposed. X may be
empty and the gluing chart sets may be empty; this module never selects a chart or point.
There is no characteristic or field assumption. I and all schemes share the arbitrary
universe u, so the inverse-limit universe is not made smaller than the scheme universe.
The base-change projection is to the selected stage, not to the old stage. The transition
is selected with `choose_spec` of the same existence proof as the index.

Searches made (also recorded by msearch):

- LeanFinder: “choose a later separated stage and base changed model of a finite
  presentation descent of a separated scheme morphism”: eight generic morphism-property
  hits, including `LocallyOfFinitePresentation` and its pullback projection instances;
  no selected-stage construction.
- Loogle: `AlgebraicGeometry.Scheme.exists_isSeparated_pullback_snd, Classical.choose`:
  zero hits; the public Loogle service does not index this upstream theorem.
- Mathlib grep: `separated.*[Dd]escen|[Dd]escen.*[Ss]eparated`, AlgebraicGeometry:
  zero hits.
- LeanSearch: “selected stage of separated finite presentation descent model”:
  unavailable, Internal Server Error; no verdict inferred from this service failure.
- `rg` in project Sheaf and upstream WeilConjectures for
  `nagata.*[Ss]eparated|[Ss]eparated.*[Dd]escent`: upstream existence/property theorems,
  the distinct fixed-base `nagataSeparatedStage`, and unrelated compactification results;
  no definition of this selected descent stage. Searching the item id upstream found
  no occurrence. The fixed-base module was read for the witness-selection convention.

No new nodes, dependency replacement modules, or statement correction were needed.
The launcher explicitly permits the model properties required by the upstream theorem
as binders; they express the starting model’s properties, not strengthened conclusions.
Initial local compilation was clean in 2.1 seconds under autoImplicit=false.

## Second reading by Z2

Independent reading of the sandbox node and all five declarations in
`NagataSeparatedDescentStage.lean`, against both dependency nodes and their actual
source declarations. I also read the whole landed modules
`NagataRelativeGluingDatumDescent`, `NagataRelativeGluingValidStage`, and
`NagataFinitePresentationDescent`, and the fixed-base selection module. The blueprint
source is unavailable locally, so its verbatim statement in the node is the source
text for this definition, as the launcher's brief specifies. The supporting Stacks
text was read in `/home/ubuntu/c1-stacks-review/limits.tex`: Tag 01ZM,
`lemma-descend-finite-presentation`, and Tag 01ZQ,
`lemma-descend-separated-finite-presentation`, including its standing
`situation-descent-property`. This situation assumes a directed inverse system with
affine transitions, a quasi-compact quasi-separated starting base and model, and the
specified base-change identification. It imposes no field, characteristic, reducedness,
nonemptiness of the schemes, or Noetherian hypothesis.

The node's objects, hypotheses, and definition clauses, item by item:

1. The inverse system and its limiting base S are `D : Iᵒᵖ ⥤ Scheme.{u}`,
   `c : Cone D`, and `hc : IsLimit c`; S is `c.pt`. The preorder, directedness,
   affine-transition instances, starting stage `i₀`, and quasi-compact and
   quasi-separated base instances are the same parameters used by the landed raw and
   valid gluing constructions. Verdict: the same system and base, without a new
   universe restriction or a replacement approximation.
2. X and its structure morphism are `{X : Scheme.{u}}` and `f : X ⟶ c.pt`.
   Separatedness is `[IsSeparated f]`; finite presentation is
   `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`, the
   family's existing finite-presentation convention. Verdict: matches; quasi-separatedness
   is also implied by separatedness and does not strengthen the separated case.
3. The constructed relative stage and finite-stage model retain precisely `R`, `P`,
   `A`, `G`, and `B` from the dependency modules. The old stage is
   `nagataRelativeGluingValidStage D c hc i₀ f R P A`; the model's structure map is
   `nagataFinitePresentationDescentMap D c hc i₀ f R P A G B`, with source the
   specified `G.data.glued`. Verdict: the dependency's actual glued model, not an
   unrelated existential model. `G` and `B` retain the chart, overlap, transition,
   and structure-map equations read in the predecessor module.
4. Its specified base-change comparison is
   `nagataFinitePresentationDescentComparison D c hc i₀ f R P A G B E`, where
   `E : NagataFinitePresentationComparisonData …` retains both pullback projections,
   the original chartwise comparisons, and `comparison_base`. Its `IsIso` instance,
   the three finite-presentation instances on the exact descended map, and the two
   instances on the exact relative-stage base provide the starting model properties
   needed by the recorded existence theorem. Verdict: these express the properties
   of the constructed descent model, as explicitly authorized in the launcher brief;
   no property of the selected later model is assumed.
5. “Choose one witness from lemma-nagata-separated-descent-stage-exists” is
   `Classical.choose (Scheme.exists_isSeparated_pullback_snd hc
   (nagataFinitePresentationDescent_isPullback …))`. I checked the upstream signature
   at line 3458 and its entire proof through line 3508: its witness is
   `∃ (k' : Iᵒᵖ) (t : k' ⟶ k), IsSeparated (pullback.snd p (D.map t))`
   in this application. It is fully proved, with no `sorry` in its body. The helper
   square has upper map `inv comparison ≫ pullback.fst`, left map f, right map the
   constructed descent map, and lower map the limit projection. Verdict: the correct
   recorded theorem, applied to the correct model and cartesian square.
6. “Define lambda_sep to be the index” is `nagataSeparatedDescentStage`, the `unop`
   of that first chosen witness. `nagataSeparatedDescentTransition` uses
   `Classical.choose` on `Classical.choose_spec` of the identical theorem application.
   Its target is the old relative stage and its source is the selected stage, so it
   records the later-stage relation with the correct arrow direction. Verdict: both
   components belong to the same witness, with no independent index or transition.
7. “Define X^sep to be the model recorded by that witness” is
   `nagataSeparatedDescentModel = pullback p (D.map t)` for precisely that map p and
   transition t. `nagataSeparatedDescentMap` is `pullback.snd p (D.map t)` to
   `D.obj (op (nagataSeparatedDescentStage …))`. Verdict: exactly the base-changed
   model whose projection occurs in the witness predicate, over the new base.
8. “The eventual separatedness and comparison properties are stated separately”:
   the module adds no theorem or assumed instance asserting these properties of the
   selected later model. Verdict: the definition does not silently replace the later
   property lemma or strengthen its conclusion.

Edge cases: the index system is inhabited by the starting stage and has the same
nonempty directed preorder convention as its dependencies. The construction admits a
singleton system and an identity transition; “later” is not strict. Empty schemes,
empty chart sets and empty overlap sets remain allowed: no chart or point is selected
here. The arbitrary universe u is shared by I and the schemes, with no independent
smaller test universe. There is no ring-to-field restriction, characteristic hypothesis,
or positive dimension assumption. All variables and universes are explicitly bound;
the compile also checks this with `autoImplicit=false`.

Independent searches, using different queries from the author:

- LeanFinder via msearch: “select an index and transition making the diagonal of a
  descended scheme a closed immersion”. Eight hits describe diagonals, closed
  immersions, and separatedness; none defines the selected descent stage.
- Loogle via msearch: `AlgebraicGeometry.IsSeparated,
  CategoryTheory.Limits.pullback.snd`. The two hits are the base-change separatedness
  instance and an unrelated etale-complement theorem. The instance assumes the old
  map is already separated; it does not select a later stage.
- LeanSearch via msearch: “choosing a later stage where a finite presentation model
  becomes separated”. The service returned Internal Server Error; no absence claim
  is based on that failure.
- msearch grep: `SeparatedDescent|separatedDescent|separatedStage`, no hits.
  Independently, rg over Mathlib AlgebraicGeometry, upstream `WeilConjectures`, and
  project `lean/Sheaf` for `nagataSeparatedDescent`, `selected.*separated`,
  `separated.*stage`, and `exists_isSeparated_pullback_snd` found the upstream
  existence theorems, fixed-base `nagataSeparatedStage`, and property lemmas. I read
  the fixed-base signature: it concerns a natural transformation to a fixed base
  and is a different construction. No existing declaration supplies this selection
  from this constructed finite-presentation model.

H5/H6/H8/H9: all four definitions have concrete bodies. Selection uses the proved
upstream theorem; the only local postponed proof is the named pullback-transport
theorem. Its docstring explains the canonical cartesian square, transport by the
comparison isomorphism, and the `comparison_base` equation. This postpones a property,
not the existence of chosen data. Every declaration names the source and this item's
blueprint; there are no unbound variables, private copies, file-local notation,
signature `let`/`show` terms, or lines over 100 characters. The node's
`lean.statement` is verbatim `def nagataSeparatedDescentStage : I`. No new nodes,
dependency replacement modules, or statement correction are present or needed.

No mathematical or Lean mismatch was found; the source module and node were left
unchanged. This reading adds only this report and the independent search evidence.
Local single-file compilation was clean in 2.1 seconds. I additionally invoked
`lcompile.run_set` on this single module to compile it alone with `.olean` and
`.ilean` output: clean in 2.6 seconds, below the 60-second limit including output.
No `deliver2.py` invocation was made, following the second-reader override; the
launcher handles delivery.

Launcher note (Z2): the proof of `nagataFinitePresentationDescent_isPullback` (the pullback square handed to the proved upstream theorem `Scheme.exists_isSeparated_pullback_snd`) is `sorry` in this stage-2 delivery, as the stage requires, and is landed by Z2 right after it (transport of the canonical pullback square along the comparison isomorphism), so that the selected stage and model are chosen from fully proved statements.
