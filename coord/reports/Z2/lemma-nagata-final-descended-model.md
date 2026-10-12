## Worker report

The module `Sheaf.AlgebraicGeometry.NagataFinalDescendedModelProperties` states
`AlgebraicGeometry.nagataFinalDescendedModel_properties`, with its entire proof `sorry`.
It concerns exactly the chosen stage, model, map, and explicit comparison of the landed
`def-nagata-final-descended-model`. No definition, new node, dependency replacement, or
statement correction is needed.

Hypothesis correspondence (the phrase “as in def-nagata-final-descended-model” retains
all the construction inputs of that corrected definition):

- The directed presentation is `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`, `D : Iᵒᵖ ⥤ Scheme.{u}`, `c : Cone D`, `hc : IsLimit c`,
  and the affine-transition instance. `i₀` with its compact and quasi-separated stage
  instances is the initial stage of that construction.
- The base is `c.pt`, with `[CompactSpace c.pt] [QuasiSeparatedSpace c.pt]`.
  The original morphism is `{X : Scheme.{u}} (f : X ⟶ c.pt)` (the node's Y is named X
  consistently with its dependency). Its separatedness is `[IsSeparated f]`;
  finite presentation is `[LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`.
- `R`, `P`, `A` retain the relative datum, raw inclusions, and valid stage. `G`, `B`,
  `E` retain the finite-presentation gluing datum, base map, and comparison, with
  `[IsIso (nagataFinitePresentationDescentComparison ...)]`.
- The compact and quasi-separated instances at the valid stage, and the three
  finite-presentation instances on `nagataFinitePresentationDescentMap`, are precisely
  the input properties of the selected separated-stage construction. None is an
  assumption of a property of the final selected map.
- `Q : NagataFinalBaseSystemIdentification D c` retains the supplied Noetherian
  approximation, reindexing, diagram isomorphism, and projection equations.

Conclusion correspondence:

- “The morphism Y_λ → S_λ is separated” is
  `IsSeparated (nagataFinalDescendedMap D c hc i₀ f R P A G B E Q)`.
- “Of finite presentation” is `LocallyOfFinitePresentation`, `QuasiCompact`, and
  `QuasiSeparated` of the same map. These are the established family encoding of
  finite presentation; in particular separatedness already implies quasi-separatedness.
- “S_λ is Noetherian” is `IsNoetherian (D.obj (op (nagataFinalDescendedStage ... Q)))`.
  The identification with the supplied approximation transfers Noetherianity to this
  actual stage, rather than asserting it about an unrelated stage.
- “ε is an isomorphism over S” is `IsIso (nagataFinalDescendedComparison ... Q)` and
  `nagataFinalDescendedComparison ... Q ≫ f = pullback.snd
  (nagataFinalDescendedMap ... Q) (c.π.app (op (nagataFinalDescendedStage ... Q)))`.
  The latter equality identifies its composite to S with the structure map of its
  pullback domain; it is not the tautological pullback square condition.

Dependency declarations read and used:

- Public import `Sheaf.AlgebraicGeometry.NagataFinalDescendedModel`:
  `NagataFinalBaseSystemIdentification`, `nagataFinalDescendedStage`,
  `nagataFinalDescendedModel` (through the map's domain), `nagataFinalDescendedMap`,
  `nagataFinalDescendedComparison`. The variable block is the dependency's own block.
- Proof import `Sheaf.AlgebraicGeometry.FinalNoetherianBaseSystemProperties`:
  `AlgebraicGeometry.Scheme.NoetherianApproximation.finalBaseSystem_properties`.
- Proof import `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`:
  `AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
  (recorded for lemma-nagata-separated-eventually). Its signature and docstring were
  read, as was the fully proved `Scheme.exists_isSeparated_pullback_snd` used by the
  selected definition. The existential theorem is proof material only: this statement
  names the selected model, not an arbitrary existential witness.

Edge cases checked: empty schemes are allowed; no nonempty scheme hypothesis is added.
A singleton index preorder is allowed, and no strict inequality or nonidentity transition
is assumed. An empty index is excluded exactly by the existing definition's nonempty
system and selected initial stage. Scheme and index universes are the same explicit `u`.
No assumption of Noetherianity of the limit base is made. The over-base equation has
source the selected model's pullback and target `c.pt`, including for an empty base.

Searches (msearch.py, group Z2, this item):

- leanfinder: “The selected descended scheme model is separated and of finite
  presentation over a Noetherian stage and its base change comparison is an isomorphism”.
  Eight hits, including `LocallyOfFinitePresentation` and generic descent theorems;
  none states the properties of these selected objects.
- loogle: `IsSeparated, LocallyOfFinitePresentation, IsNoetherian, IsIso`.
  Zero hits, unknown unqualified identifier `IsSeparated`.
- grep: `nagataFinalDescended|exists_isPullback_of_finitePresentation_of_isSeparated`.
  Zero Mathlib hits.
- `rg` of `nagataFinalDescended|lemma-nagata-final-descended-model` in upstream
  `WeilConjectures`: no hits. `rg` in the project's `lean/Sheaf` and DAG finds the
  selected definition and citations, but no existing selected-properties declaration.
  Upstream `exists_isPullback_of_finitePresentation_of_isSeparated` gives existence
  of a model, not these properties of the fixed model, and does not assert the
  Noetherian stage conclusion.

No statement fault or STATEMENT-DISPUTED issue was found. The module docstring contains
the two proof steps of the node, including transfer of the stage property through Q.

Additional searches: LeanSearch with “A selected separated finite presentation descent
model has a Noetherian base stage and its canonical base change comparison is an
isomorphism over the base” returned service unavailable (Internal Server Error); no
verdict was assigned to this unavailable service. Qualified Loogle query
`AlgebraicGeometry.IsSeparated, AlgebraicGeometry.LocallyOfFinitePresentation` returned
zero hits.

Validation: local compilation of the scratch copy together with the landed predecessor
succeeded cleanly: predecessor 2.6 s, this module 2.2 s, including .olean output. The
scratch copy is byte-identical to the delivery module. All scratch files are outside
the delivery's lean/ tree. The required `deliver2.py Z2
lemma-nagata-final-descended-model --no-push` was run. It stopped before preflight because
the server's Z2 compiled overlay lacks
`Sheaf/AlgebraicGeometry/NagataFinalDescendedModel.olean`. This is the newly landed
predecessor, not an error in the delivered module. Under the launcher's tool-failure
exception, the launcher performs delivery once that predecessor is available. Nothing
was pushed; the independent second reading remains to be done.


## Second reading by Z2

Independent reading of the node copy, its complete Lean module, and the landed
`NagataFinalDescendedModel` definition: PASS. No mathematical mismatch found; the
Lean and node are unchanged. This section records the second reader's own checks.

The node's object/hypothesis/conclusion checklist, expanding “as in
 def-nagata-final-descended-model”, is:

| Node item | Lean rendering and verdict |
| --- | --- |
| Quasi-compact quasi-separated base S | `c.pt`, `[CompactSpace c.pt]`, `[QuasiSeparatedSpace c.pt]`: exact. |
| Scheme Y and morphism Y → S | `{X : Scheme.{u}} (f : X ⟶ c.pt)`: exact, with harmless renaming Y to X. |
| Original morphism separated | `[IsSeparated f]`: exact. |
| Original morphism of finite presentation | `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`: exact qcqs finite-presentation encoding; the last property also follows from separatedness. |
| Directed presentation of supplied final system | `{I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]`, `D`, `c`, `hc`, affine transitions: the corrected definition's exact inputs. |
| Initial stage for the relative construction | `i₀` and its compact/quasi-separated instances: exactly the inherited relative-gluing construction, not another Noetherian assumption. |
| Retained relative datum and valid stage | `R : NagataRelativeGluingDatum ...`, `P : NagataRelativeRawInclusions ... R`, `A : NagataRelativeGluingValidStageData ... R P`: exact landed dependent records, no private datum. |
| Retained finite-presentation model and map | `G : NagataFinitePresentationGluingData (nagataRelativeGluingValidDatum ...)`, `B : NagataFinitePresentationBaseMap G`: chart and transition equations tie these to that datum. |
| Retained comparison and input properties | `E : NagataFinitePresentationComparisonData ... G B`, its comparison `IsIso`, valid-stage compact/quasi-separated instances, and the three finite-presentation instances of `nagataFinitePresentationDescentMap`: identical to the dependency's variable block. They concern the earlier model, not the conclusion's selected later model. |
| Identification with N_f = N(S) | `Q : NagataFinalBaseSystemIdentification D c`: approximation, reindexing functor, diagram isomorphism, projection equation. Exact. |
| Selected λ_Y and Y_λ_Y | `nagataFinalDescendedStage ... Q`, `nagataFinalDescendedModel ... Q`: aliases of the landed separated-stage selection and its pullback model, rather than a fresh existential witness. |
| Selected structure map separated | First conjunct `IsSeparated (nagataFinalDescendedMap ... Q)`: exact. |
| Selected structure map of finite presentation | Next three conjuncts `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated` of that same map: exact, with quasi-separatedness redundant under the first conjunct but part of the family encoding. |
| Actual selected base stage Noetherian | `IsNoetherian (D.obj (op (nagataFinalDescendedStage ... Q)))`: exact, not merely a stage of an unrelated approximation. |
| Constructed ε_Y an isomorphism | `IsIso (nagataFinalDescendedComparison ... Q)`: exact fixed comparison. |
| ε_Y over S | `nagataFinalDescendedComparison ... Q ≫ f = pullback.snd (nagataFinalDescendedMap ... Q) (c.π.app (op (nagataFinalDescendedStage ... Q)))`: exactly equality of maps from the selected base change to S. |

All objects are universally quantified in construction order; no existential choice
or altered quantifier order appears in the conclusion. The binder blocks match the
landed definition verbatim. Universe `u` is bound explicitly and shared by schemes
and index. Compilation with `autoImplicit=false` confirms no hidden unbound variable.

Source and dependency reading: the blueprint source is unavailable locally, so the
node statement serves as its verbatim source, as the launcher specifies. I read the
corrected definition's statement and `statement_change` first. Its two citers
`def-nagata-final-noetherian-compactification` and
`def-nagata-final-basechanged-compactification` still use the same selected model
and comparison; the recorded `holds: true` verdicts are consistent. There is no
statement correction to this item and no new or replacement dependency module.

I read the whole landed `NagataRelativeGluingDatumDescent` module and the signatures
and bodies of the finite-presentation, separated-stage and final-model modules.
`NagataFinitePresentationComparisonData.comparison_base` specifies the over-base
comparison. `nagataSeparatedDescentStage` and its transition choose the SAME witness
of the fully proved `Scheme.exists_isSeparated_pullback_snd`; its model and map are
`pullback` and `pullback.snd`. The final comparison is explicitly the composite of
`pullbackLeftPullbackSndIso.hom`, `pullback.congrHom.hom` for cone compatibility, and
the earlier comparison. Thus no definition's data is `sorry`, and no final data is
selected from an unproved theorem.

I read upstream `Scheme.NoetherianApproximation` (lines 208–238),
`gluedLimitComparison`, and `finalBaseSystem_properties`: Noetherianity of every
approximation stage is the existing `isNoetherian_obj` instance, and transfers
across `Q.diagramIso.app`. The approximation has a cofiltered small category;
the corrected definition explicitly supplies the directed presentation and limit
identification rather than silently treating that category as a preorder.

The Stacks .tex is also unavailable locally. I read the primary source online:
[limits.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/limits.tex),
`situation-descent-property` and `lemma-descend-separated-finite-presentation`
([Tags 081D](https://stacks.math.columbia.edu/tag/081D) and
[01ZQ](https://stacks.math.columbia.edu/tag/01ZQ)). The situation assumes affine
transitions and quasi-compact quasi-separated initial base, source and target.
Here the valid-stage base and finite-presentation model satisfy these through the
explicit instances; the source model is qcqs because its map is qcqs over that
base. No field or characteristic assumption occurs. I also read upstream
`Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`: it asserts
existence of a model, not the properties of this fixed chosen model. It is proof
material, not an exact existing replacement for the item. For the fixed witness,
separatedness comes from `Classical.choose_spec` in the actual selection; finite
presentation is preserved by base change. The theorem docstring records both node
proof steps, including comparison reassociation and Noetherianity transfer.

Edge cases: empty schemes and empty bases are admitted (no nonempty-space or
nontrivial-ring hypothesis). Empty indexing is excluded by the definition and by
the source's nonempty directed system, not newly excluded here. Singleton indices
and identity transitions are allowed; no strict later stage is required. Empty
chart/overlap families are not excluded by this theorem beyond the dependency's
own construction data. There is no numerical n or characteristic restriction;
zero rings, where represented by empty affine schemes, are not ruled out. No
Noetherianity of S is assumed. Both sides of the over-base equation still have
the same source and target in these cases.

Independent searches, using different phrasing from the first reader:

- `msearch.py ... leanfinder`: “Properties of a fixed model obtained by descending
  a separated finitely presented scheme along an inverse limit of Noetherian
  schemes” returned eight hits: generic affine-transition limit results and
  morphism properties, none about these selected objects.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsSeparated,
  AlgebraicGeometry.IsNoetherian` returned zero hits.
- `msearch.py ... grep`: `descend.*(separated|Noetherian)|finitePresentation.*isSeparated`
  returned zero hits.
- Independent `rg` of `nagataFinalDescendedModel_properties`,
  `finalDescended.*properties`, `NoetherianApproximation` and
  `exists_isSeparated_pullback_snd` in project `lean/Sheaf`, upstream
  `WeilConjectures/AlgebraicGeometry` and `AffineTransitionLimit.lean` located the
  shared definitions and generic upstream existence lemmas, with no existing
  selected-properties theorem. Mathlib `Morphisms/FinitePresentation.lean` and
  `Noetherian.lean` were searched/read to check the actual property meanings.

Mechanical checks: the node's `lean.statement` equals the signature extracted
verbatim from the file. Every line is at most 100 characters. Imports cover the
statement dependency and both recorded proof dependencies. Only the one named
theorem has `sorry`; no new definition or proof was added.

Validation: direct single-file local compilation initially reported that the
newly landed predecessor `.olean` had not reached the compiled library. I copied
that predecessor and the byte-identical delivery module into
`scratchpad/second-reading/lean/Sheaf/AlgebraicGeometry` and compiled them together
with `lcompile.py`. Both passed cleanly, including `.olean` output: predecessor
3.0 seconds, properties module 2.3 seconds, below the 60-second limit. Scratch
files are outside the delivery `lean/` tree. As explicitly instructed for this
second reader, I did not run `deliver2.py`, dry run or push. The only change is
this appended review section; the launcher handles delivery.
