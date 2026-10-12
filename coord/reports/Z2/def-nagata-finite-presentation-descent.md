## Worker report

The module `Sheaf.AlgebraicGeometry.NagataFinitePresentationDescent` defines the finite-stage
scheme as `G.data.glued`, its structure morphism as `B.map`, and epsilon_X as `E.comparison`.
All data are retained as small records with construction equations, as the group's brief
requires. There is no `sorry`, `Classical.choose`, or assertion of finite presentation or
isomorphy. The latter properties belong to lemma-nagata-finite-presentation-descends.

Hypotheses inherited from the recorded relative datum are explicit: `I : Type u`,
`[Preorder I]`, `[Nonempty I]`, `[IsDirected I (· ≤ ·)]`; `D : Iᵒᵖ ⥤ Scheme.{u}`;
`c : Cone D`, `hc : IsLimit c`; affine transition maps; a fixed initial stage `i₀` with
`CompactSpace` and `QuasiSeparatedSpace`; `f : X ⟶ c.pt`, with the limit base qcqs and
`LocallyOfFinitePresentation f`, `QuasiCompact f`, `QuasiSeparated f`. These are precisely
what the dependency's declaration takes, not new separatedness or Noetherian assumptions.
`R`, `P`, and `A` are the dependency's raw datum, canonical raw inclusions, and recorded
valid-stage choices. Its `nagataRelativeGluingValidStage` is the selected index, and
`nagataRelativeGluingValidDatum` is exactly the transported diagram being glued.

Every clause of the corrected statement is rendered as follows:

- The gluing realization is `NagataFinitePresentationGluingData T`. `data` is Mathlib's
  `Scheme.GlueData`; `index : data.J ≃ J` accounts for every chart, including an empty family.
  `chartIso` identifies its charts with the valid transported charts. `overlapIso` identifies
  the entire overlap with `(⨆ l, T.leftOpen ... l).toScheme`, not an arbitrary overlap scheme.
- `inclusion_eq` identifies the overlap inclusion with the union-open inclusion. `piece`
  and `piece_eq` specify the maps of every transported left piece into that whole overlap;
  because the overlap inclusion is monic, their composite equation determines them uniquely.
  `transition_eq` prescribes the transition on every piece using `T.forward` followed by
  `T.rightInclusion`. The left pieces cover the specified union: their inclusions are the
  canonical transported inclusions from `P`. Mathlib's `GlueData` contains the inverse and
  triple-cocycle axioms; those are construction proofs, not an assumed property of an
  arbitrary descended scheme. Reversed transitions are determined by its inverse identities.
- `NagataFinitePresentationBaseMap.map` has codomain the valid-stage base; `chart_eq`
  prescribes its composite with every glued chart inclusion. The chart cover makes this
  map unique. `nagataFinitePresentationDescent` is exactly `G.data.glued`, and
  `nagataFinitePresentationDescentMap` is exactly this map.
- `NagataFinitePresentationChartComparison.map` reassociates the successive pullbacks.
  `fst_eq` prescribes its projection to the original descended chart as the composite of
  the base-change projection to the valid chart, the projection to the raw chart, and the
  projection to the chart at its algebra-descent stage. `snd_eq` prescribes its projection
  to `c.pt`. Both equations refer to the actual descent stages of `R`, so this is not an
  arbitrary comparison. Pullback uniqueness determines the map.
- `NagataFinitePresentationComparisonData.charts` retains that construction for every
  original chart. `chartToPullback`, `chart_fst`, and `chart_snd` give the canonical maps
  into the pullback of the glued base map: the first projection is the valid chart's
  projection followed by `chartIso.inv` and `G.data.ι`, and the second is the projection to S.
- `comparison` has exactly the source `pullback B.map (c.π.app (op s))` and target `X`.
  `comparison_chart` says its restriction is the reassociation followed by
  `R.charts.chartComparison` and the original chart inclusion in X. `comparison_base`
  says it is over S. The base-changed chart cover determines this map uniquely.
  `nagataFinitePresentationDescentComparison` returns it, with the declared descended
  structure map in its domain. No alternate base-change diagram is substituted.

Dependency declarations used: in `Sheaf.AlgebraicGeometry.NagataRelativeGluingValidStage`,
`AlgebraicGeometry.NagataRelativeRawInclusions`, `NagataRelativeGluingValidStageData`,
`NagataRelativeGluingTransport`, `nagataRelativeRawChart`,
`nagataRelativeRawStage_le_validStage`, `nagataRelativeGluingValidStage`, and
`nagataRelativeGluingValidDatum`. The complete dependency file and its node record were read.
The imported raw datum's `NagataRelativeGluingDatum` supplies the original
`charts.chartComparison`, chart maps, algebra-descent stages, and original chart inclusions.
Mathlib `AlgebraicGeometry.Scheme.GlueData`, `.glued`, and `.ι` are used directly from
`Mathlib.AlgebraicGeometry.Gluing`, rather than copied. The generic GlueData's inverse and
cocycle fields and Mathlib's cover construction were read in full.

Edge cases checked before writing: an empty scheme can have an empty chart family;
`index` imposes no nonemptiness on it, and Mathlib gluing handles the empty multicoequalizer.
An empty overlap family has union bottom, so `overlapIso` forces an empty overlap. No
nonzero-ring hypothesis, characteristic restriction, separatedness hypothesis, or
Noetherian hypothesis is added. The directed index is nonempty since a stage is already
fixed, just as the dependency requires. Index types, schemes, and chart types all live in
universe u; the file has `autoImplicit=false` in the compiler and explicitly binds all
variables. Every record has at most eight fields, and both automatic record-generation
options are disabled.

Searches for an existing construction:

- `msearch.py ... leansearch "finite presentation descent glued scheme base change comparison"`:
  service unavailable, Internal Server Error; not treated as evidence of absence.
- `msearch.py ... leanfinder "finite presentation descent gluing scheme chart base change comparison"`:
  eight hits, including `Scheme.Pullback.gluing`, its transition lemmas, and
  `Scheme.LocalRepresentability.glueData`; these concern generic pullback gluing or
  representability, not the fixed valid-stage Nagata datum.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.GlueData, AlgebraicGeometry.Scheme.GlueData.glued"`:
  twelve generic gluing declarations; these are used here, but do not define the named model.
- `msearch.py ... grep "GlueData|gluedLift" AlgebraicGeometry`: generic gluing,
  normalization and representability results, none for this construction.
- `rg` in the source `WeilConjectures`, Mathlib, `dag/lean_names_upstream.json`, and
  `lean/Sheaf` for `nagataFinitePresentationDescent`, `NagataFinitePresentationGluingData`,
  `NagataFinitePresentationComparisonData`, and this blueprint id: no existing declaration.
  The broad Nagata finite-presentation search also found `nagataFinitePresentationEnvelope`,
  which was read: it approximates a finite-type morphism over a fixed base using the
  separated-stage theorem; it is a different construction. The upstream
  `Scheme.exists_isPullback_of_finitePresentation` was also read: it is an existence theorem,
  not the selected model obtained from this datum.

Validation: local compilation with `.olean` and `.ilean` output passed without errors or
warnings in 6.2 seconds, against a sandbox-compiled copy of the landed valid-stage dependency
(6.9 seconds). Nothing in either read-only checkout was changed by this compilation.
The initial single-file server compile reported that the newly landed
`NagataRelativeGluingValidStage.olean` was not yet present in the group build.

## Statement corrected

The old statement, verbatim, is preserved in `statement_change.old_statement` in the node copy:

Define

$$
X^{\mathrm{desc}}_{\lambda_{\mathrm{rel}}}
$$

by gluing the valid relative datum
$\mathsf R_{X,\lambda_{\mathrm{rel}}}$. Define

$$
\epsilon_X\colon
X^{\mathrm{desc}}_{\lambda_{\mathrm{rel}}}
\times_{S_{\lambda_{\mathrm{rel}}}}S
\longrightarrow X
$$

by gluing the chartwise base-change identifications.
The relative gluing axioms instantiate the scheme-gluing construction. Base
change preserves the affine charts and overlap maps, so the base-changed
object is canonically the gluing of the base-changed datum; chartwise
comparisons glue to $\epsilon_X$.

The corrected valid-stage dependency supplies a piece diagram, not a whole-overlap
`Scheme.GlueData`, its glued structure morphism, or the reassociation maps used by the
comparison. The correction explicitly retains these construction data with the equations
that determine their fields. It follows the item's blueprint source, order 362, and the
surrounding construction at orders 358–363, whose node text was read. As a corroborating
source, [Stacks Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM), proof of (1), constructs
compatible overlaps, glues them, and identifies the base-changed gluing with X. No unit
statement or proof route changes. `stmt_deps`, `proof`, and `proof_deps` are unchanged.
No new notion or dependency module is needed: the records are the portions of the item's
own gluing construction, in the style of the already landed raw-datum records.

Every direct citer was found by searching the DAG and checking its dependency lists:

- `def-nagata-separated-descent-stage`: holds; it still starts from the same selected
  finite-presentation model, now with its structure map explicitly retained.
- `lemma-nagata-finite-presentation-descends`: holds; finite presentation of the structure
  map and isomorphy of the recorded comparison are still subsequent assertions, not fields.
- `lemma-nagata-separated-descent-stage-exists`: holds; it still uses this model and
  comparison to express eventual separatedness at a later stage.

No citer was edited. No statement is disputed.

Final check: a single-file `lcompile.py` run also passed cleanly in 3.8 seconds.
`deliver2.py Z2 def-nagata-finite-presentation-descent --no-push` stopped at its server
compile because the group build lacks the already landed dependency
`Sheaf/AlgebraicGeometry/NagataRelativeGluingValidStage.olean`. It therefore did not reach
commit construction or preflight, and pushed nothing. This is the tool/build availability
fault covered by the launcher's final exception, not a Lean elaboration failure in this
module. The launcher must rerun the dry run once that landed dependency is available.

## Second reading by Z2

I read the corrected statement before comparing the Lean, then read the complete landed
`NagataRelativeGluingValidStage.lean` and `NagataRelativeGluingDatumDescent.lean`, their
node statements and correction records, and the neighbouring construction/property nodes.
The local Stacks checkout is absent. I therefore read the actual `limits.tex` source at
https://raw.githubusercontent.com/stacks/stacks-project/master/limits.tex,
Lemma `lemma-descend-finite-presentation`, including all three parts of its proof, and
checked [Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM).
Its last construction in proof (1) glues the descended charts and overlaps and compares
their base change with the original cover. The correction retains exactly this construction
as equation-constrained data, as the launcher requires; it does not replace it with an
unrelated witness of the existence theorem.

Here is my list of the objects, hypotheses and defining clauses, with their Lean matches.
All verdicts below are pass.

- Directed system and limit: `I : Type u`, `Preorder`, `Nonempty`, `IsDirected`,
  `D : Iᵒᵖ ⥤ Scheme.{u}`, `c : Cone D`, `hc : IsLimit c`, and the instance of
  `IsAffineHom (D.map t)` are the dependency's inputs. A preorder also permits every
  directed poset in the node. The fixed qcqs stage is `i₀`, with `CompactSpace` and
  `QuasiSeparatedSpace`. The explicit qcqs instances on `c.pt` are consequences of
  its affine projection to that stage, already required by the raw datum; they add no
  restriction. Stacks assumes every base stage qcqs; the node's tail above `i₀` is qcqs
  because its transitions to `i₀` are affine, so this construction needs no extra instance
  on every stage.
- Original finite-presentation morphism: `f : X ⟶ c.pt` with
  `LocallyOfFinitePresentation f`, `QuasiCompact f`, `QuasiSeparated f` uses exactly
  the dependency's encoding of finite presentation. There is no `IsSeparated f`.
- Fixed raw diagram, inclusions and equality choices: `R`, `P`, `A` use the landed
  `NagataRelativeGluingDatum`, `NagataRelativeRawInclusions`, and
  `NagataRelativeGluingValidStageData`, with the same system and original morphism.
  The stage `s` and transported diagram `T` are the actual
  `nagataRelativeGluingValidStage` and `nagataRelativeGluingValidDatum`, not private copies.
- Realize the entire transported diagram: `NagataFinitePresentationGluingData.data`
  is Mathlib's `Scheme.GlueData`; `index : data.J ≃ J` and `chartIso` match every
  chart. `overlapIso` identifies each whole overlap with the union of all specified
  left opens, and `inclusion_eq` fixes its inclusion. In particular a record cannot
  substitute a smaller overlap or add an extra chart.
- Retain each overlap-piece inclusion and transition: `piece`, `piece_eq`, and
  `transition_eq` give precisely the two composite equations in the node. For the
  actual transported datum the piece inclusion identifies its source with its specified
  open. Since `data.f` is an open immersion and `chartIso` is an isomorphism,
  `piece_eq` determines `piece`; the pieces cover the specified union. Consequently
  `transition_eq` determines the entire transition. Mathlib's `GlueData` supplies
  diagonal identities and the triple cocycle, and its `t_inv` gives the reversed inverse.
- Retain the glued structure map: `NagataFinitePresentationBaseMap.map` targets
  the stage base; `chart_eq` fixes its restrictions. Mathlib's glued chart cover makes
  this a uniquely specified map. `nagataFinitePresentationDescent := G.data.glued`
  and `nagataFinitePresentationDescentMap := B.map` implement both definitions literally.
- Reassociate each base-changed valid chart: `NagataFinitePresentationChartComparison.map`
  targets `(baseChangeCone D c (R.charts.chartMap j)).pt`. Its `fst_eq` uses exactly
  the successive projections valid-to-raw-to-original-stage; `snd_eq` is the limit-base
  projection. The target pullback universal property determines this map. In particular
  the equations use the actual algebra-descent stage, not just an arbitrary stage.
- Map each base-changed chart into the base-changed gluing:
  `NagataFinitePresentationComparisonData.charts`, `chartToPullback`, `chart_fst` and
  `chart_snd` retain the preceding maps and the canonical pullback lifts. The first
  projection uses `(G.chartIso a).inv ≫ G.data.ι a`; the second projects to `c.pt`.
- Glue the comparison to the original scheme: `comparison` has precisely domain
  `pullback B.map (c.π.app (op s))` and codomain `X`. `comparison_chart` composes
  reassociation with `R.charts.chartComparison` and the original chart inclusion;
  `comparison_base` says the morphism is over the limit base. The base-changed chart
  cover determines it. `nagataFinitePresentationDescentComparison := E.comparison`
  returns this map with the declared descended structure map in its type.
- The later property assertions remain later: neither finite presentation of `B.map`
  nor `IsIso E.comparison` is a field. The file contains no theorem, proof, `sorry`,
  or selection of data from an unproved existence theorem. Its seven declarations
  have the source and blueprint docstrings; there are no node proof steps to reproduce.

Edge cases: `J` and each `K j k` may be empty. The equivalence of indices introduces
no nonemptiness assumption; an empty overlap family forces its overlap to the bottom
open. Mathlib's gluing construction permits the empty cover and hence the empty scheme.
An empty directed index is already excluded by the fixed stage in the source, not by
this module. There is no field, nonzero-ring, characteristic, Noetherian, or separatedness
restriction. Zero-generator/zero-relation affine presentations are inherited without new
restrictions. All schemes, index types and overlap types use the same explicitly bound
universe `u`, as the limit convention requires. None of the signatures contains `let`,
`show`, a private declaration or local notation. All records have at most eight fields,
both automatic record-generation options are disabled, and all lines are at most 100
characters. The recorded `lean.statement` is the verbatim `def` signature in the file.

I independently repeated the searches with different descriptive terms:

- LeanSearch: `glue scheme from overlap opens and morphisms with base change identification`;
  unavailable (Internal Server Error), which is not evidence of absence.
- LeanFinder: `scheme gluing chosen finite stage overlap unions descent comparison`;
  eight generic gluing/cover hits, including `Scheme.Cover.gluedCover`,
  `Scheme.Cover.glueMorphisms` and `Scheme.GlueData.openCover_f`.
- Loogle: `"glued", "pullback"`; twelve generic gluing/pullback hits, including
  `Scheme.GlueData.vPullbackCone` and `CategoryTheory.GlueData.t'_comp_eq_pullbackSymmetry`.
- `rg` on the source `WeilConjectures`, project `lean/Sheaf`, and Nagata DAG for
  `NagataFinitePresentation`, `nagataFinitePresentationDescent`, and finite-presentation
  gluing/descent terms found no existing fixed-datum construction. I opened Mathlib's
  `Scheme.GlueData`, `.glued`, `.ι`, and the underlying `CategoryTheory.GlueData` fields
  and inverse theorem. They supply the generic construction used here. I also opened
  upstream `Scheme.exists_isPullback_of_finitePresentation` and the landed
  `nagataFinitePresentationEnvelope`: the former is an existential descent theorem,
  and the latter is a different fixed-base finite-type envelope. Neither defines this
  diagram's chosen gluing and comparison. No new definition node or dependency module
  is needed, and the delivery contains none.

I checked the correction's citer verdicts against the actual statements of
`def-nagata-separated-descent-stage` and `lemma-nagata-separated-descent-stage-exists`:
both still use the same constructed model and later separatedness witness. I also checked
`lemma-nagata-finite-presentation-descends`: it still asserts finite presentation and
isomorphy of this particular comparison. All three `holds: true` verdicts remain justified.

No mathematical or Lean mismatch was found; I left the module and node unchanged and
added this review. A single-file `lcompile.py` check passed without errors or warnings
in 3.6 seconds. To check the hard limit including artifact writing, I additionally used
`lcompile.run_set([file], timeout=60)` on this file alone: it wrote its `.olean` and
`.ilean` cleanly in 6.4 seconds. This uses the sandbox's compiled predecessor overlay,
not a modification to either read-only checkout. Per the launcher's second-reader
instruction I did not run `deliver2.py`; delivery remains the launcher's step.
