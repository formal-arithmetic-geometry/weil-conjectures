## Worker report

Item `def-nagata-relative-gluing-datum-descent`, module
`Sheaf.AlgebraicGeometry.NagataRelativeGluingDatumDescent`, main declaration
`AlgebraicGeometry.NagataRelativeGluingDatum`.

The mathematics is C1's reviewed version (head 5f64d5ed5, kept at
`refs/stage2-leftover/C1/def-nagata-relative-gluing-datum-descent`): every field of that version
is kept, with the same type. Its landing failed twice with a timeout in the library compile
although the sandbox compile took 31 s. The cause, measured on the server:

- A sandbox compile writes no `.olean`; the library compile does, and Lean then waits for the
  automatically generated injectivity (`mk.injEq`) and `sizeOf` lemmas of the records.
  Old file: 33 s without output, 181 s with output; with `genInjectivity` off 76 s; with
  `genSizeOf` off 195 s; with both off 38 s.
- The cost is not one field and not the size of a record: after cutting the records into small
  ones (at most 20 fields) the injectivity lemmas still cost 173 s, spread over the records with
  dependent choices (overlap stage 36 s, final stage 29 s, charts 18 s, algebras 11 s, ...).
  Elaboration of the definitions themselves is 8 s, kernel checking 10 s.

What changed against the C1 version:

1. The three large records chained by `extends` (`NagataRawChartData` 34 fields,
   `NagataRawOverlapStageData` 40 more, `NagataRawOverlapData` 14 more, flattened to 88) are cut
   into `NagataRawBaseData`, `NagataRawAlgebraData`, `NagataRawChartData`,
   `NagataRawOverlapOpenData`, `NagataRawOverlapStageData`, `NagataRawOverlapSchemeData`,
   `NagataRawOverlapData`, each taking the earlier records as explicit parameters.
   `NagataRawMorphismData` and `NagataRawFiniteStageData` take them as parameters;
   `NagataRelativeGluingDatum` has one field per record (`base`, `algebras`, `charts`, `opens`,
   `stages`, `schemes`, `overlaps`, `morphisms`, `raw`). Fields are unchanged; references to
   earlier fields are qualified by their record.
2. `set_option genInjectivity false` and `set_option genSizeOf false` for the file: these lemmas
   are not used by any citer and are the whole cost.
3. `attribute [instance]` on `NagataRawChartData.chartCompact` and `chartQS`, which were local
   instances of the `extends` chain and are needed to type the open descents of the next record.
4. Module format (`module`, `public import`, `@[expose] public section`).

Compile time of the module with `.olean` output on the server: 30 s (limit 60 s).

Hypotheses, clauses, dependency declarations, edge cases and searches are those of the C1 report,
reproduced below with the record names of that version (`morphisms.overlap.X` is now the field
`X` of the record that owns it).

### Field-by-field reading of the C1 version (reviewer X-5f64d passed head 5f64d5ed5)

Read the node copy, the original blueprint order-358 definition (from the server's
literature checkout), and Stacks `limits.tex`, `lemma-descend-finite-presentation`
(Tag 01ZM), including its standing affine-transition and qcqs assumptions. The blueprint
specifically constructs chosen raw data; the existing approximation theorems bypass
that construction and do not define it. The node already incorporates the passage to
the cofinal tail above the fixed qcqs stage, so no statement correction is needed.
The earlier worker report and superseded reading do not describe the equations that
were actually in the input file: several of those equations were reflexive placeholders.
This reading replaces those claims with the following field-by-field audit.

Objects, hypotheses and defining clauses, in the node's order. The table names fields
within their records: `datum.morphisms : NagataRawMorphismData`,
`datum.morphisms.overlap : NagataRawOverlapData`, whose inherited chart and overlap-stage
fields come from `NagataRawChartData` and `NagataRawOverlapStageData`. For example, the
presentation is `datum.morphisms.overlap.base`, and the selected forward output is
`(datum.morphisms.choice j k l).forward`; the final stage and raw fields are on `datum.raw : NagataRawFiniteStageData ... datum.morphisms`.
Each `datum.raw.forwardRaw` / `datum.raw.backwardRaw` entry
contains the over-base morphism as `map` and its canonical projection equation as `map_eq`.

| Node item | Lean rendering and verdict |
| --- | --- |
| Nonempty directed index set | `{I : Type u}`, `Preorder I`, `Nonempty I`, `IsDirected I (· ≤ ·)`; covers directed posets and also permits equivalent preorder indices. Pass. |
| Inverse system, affine transitions | `D : Iᵒᵖ ⥤ Scheme.{u}` and the instance on every `D.map t`. Pass. |
| Specified limit with projections | `c : Cone D`, `hc : IsLimit c`; all limit maps use `c.π`. Pass. |
| Fixed qcqs base stage | `i₀`, `CompactSpace (D.obj (op i₀))`, `QuasiSeparatedSpace ...`. Pass. |
| Finite-presentation morphism | `X`, `f : X ⟶ c.pt`, with `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`. The qcqs instances on `c.pt` follow from the affine limit projection to the specified qcqs stage, so they add no mathematical restriction. Pass. |
| Fixed finite relative affine presentation | `morphisms.overlap.base : RelativeFiniteAffinePresentation f`, using the recorded dependency rather than a private replacement. Its finite base/chart/overlap indices and scalar structures are exactly the dependency's. Pass. |
| Base charts pulled back from a finite affine cover of the original stage | `baseOpen`, `baseOpenAffine`, `baseOpenCovers`, `base_eq`, indexed by the presentation's finite `baseIndex`. Pass. |
| Actual coordinate ring system and colimit on each base chart | `rings`, `ringAtStage`, `ringTransition_le`, `ringAtStage_naturality`, `ringAtLimit`, `ringAtLimit_le`, `ringAtLimit_colimit`. The equations now identify transitions with `D.map ... .appLE` and colimit projections with `c.π ... .appLE`. Only the cofinal tail has geometric coordinate comparisons; the full ring system is an extension of that tail. Pass after repair. |
| Chart presentations and chosen finite-stage algebra descents | `relations_eq` identifies the relations with `nagataRawRelations`; `algebraDescent` is `NagataAffineFpDescent` at the exact numbers of generators and relations. `algebraBoundBase_eq`, `algebraBoundPair_eq`, `algebraBoundOrder_eq` fix the same selected upper-bound operation throughout. Pass after repair. |
| Chart algebra is the given presented algebra, with its scalar structure and generators | `chartAlgebra_scalar` now preserves the algebra map through `ringAtLimit` and `f.appLE`, for every scalar; `chartAlgebra_generator` preserves every specified presentation generator. Pass after repair. |
| Chart scheme and its structural map | `chart_eq` fixes the spectrum of the descended stage algebra; `chartMap_eq` is `nagataRawChartMap` using the actual `ringAtStage`, not an unrelated coordinate isomorphism. Pass after repair. |
| Canonical chart limit comparison | `chartComparison_fst` fixes the inverse's first projection using `beta`, `TensorProduct.includeRight`, `chartAlgebra`, and the chart's `toSpecΓ`; `chartComparison_snd` fixes the second projection to be the chart restriction of `f`. These uniquely determine the comparison by the pullback universal property. Pass after repair. |
| Descended quasi-compact overlaps | `leftOpen_eq`, `rightOpen_eq` identify the original overlap opens through the chart comparisons; `openChoice`, `rightOpenChoice` record the full arguments and the exact output of `nagataQCOpenDescent`, both for the same `j,k,l`. Pass. |
| One common overlap stage above chart and both open stages | `overlapStages_eq` gives exactly their finite set together with `i₀`; `overlapStage_eq` gives its selected upper bound. `chart_le_overlap`, `left_le_overlap`, `right_le_overlap`, `base_le_overlap` are the required finite inequalities. Pass after repair. |
| Canonical transport of both overlap opens and structural maps | `leftAtOverlap_eq`, `rightAtOverlap_eq` are inverse images under `baseChangeDiagram.map`; `leftScheme_eq` and `rightScheme_eq` identify the stored scheme objects with these open subschemes; `leftMap_eq`, `rightMap_eq` are the resulting canonical equality transports followed by the open inclusions and pullback second projections. The qcqs and finite-presentation fields are consequences of these constructions, recorded because morphism descent needs their instances. Pass after repair. |
| One canonical overlap isomorphism, both directions | `leftToChartLimit_fst/snd`, `rightToChartLimit_fst/snd` uniquely fix the canonical limit transports. `leftLimit_chart`, `rightLimit_chart` fix the embeddings into `X`; `overlapIso_canonical` is their composite through `base.basicAgree`. Its source is the left transported overlap and its target the right transported overlap for the SAME `j,k,l`. Pass after repair. |
| Descend both overlap morphisms and choose a shared later stage | In `(morphisms.choice j k l)`, `forwardChoice` descends the canonical hom from left to right; `backwardChoice` descends its inv from right to left. `forward_eq`, `backward_eq` identify the outputs with `nagataMorphismDescent`. `morphismStage_eq` and both inequalities transport these outputs to one common later stage. Keeping the intermediate output stages records all choices before that common transport. Pass after repair. |
| Finite set of all stages, raw selected upper bound | `stages_eq` is the union of the chart/open stages, common overlap stage, both morphism output stages and their common later stages. `stage_eq` is exactly `directedFiniteUpperBound i₀ boundPair boundOrder stages`; the relevant inequalities refer only to these finite choices. Pass after repair. |
| Raw charts, opens, morphisms and comparison maps over the raw base | `rawChart_eq` is the chart base change at `stage`; `rawLeftOpen_eq`, `rawRightOpen_eq` are the canonical inverse-image transports. `(forwardRaw j k l).map` and `(backwardRaw j k l).map` are bundled morphisms over `D.obj (op stage)`. Their `map_eq` fields commute with the canonical projections to their actual descent stages. Over-base compatibility and these projection equations uniquely characterize the transported morphisms. Pass after repair. |
| Fixed choice dependence; no raw inverse or cocycle equations | All presentations and lifts remain stored data. No independence, inverse relation or cocycle relation is imposed at the raw finite stage. Pass. |

Dependency audit: opened the signatures and definitions of
`RelativeFiniteAffinePresentation`, `NagataAffineFpDescent` (including its presentations,
scalar structures, beta and scheme maps), `nagataQCOpenDescent` and its specification,
`NagataMorphismDescentData` and `nagataMorphismDescent` and its specification,
`baseChangeDiagram`/`baseChangeCone`, `directedFiniteUpperBound`, and
`CommRingCat.exists_finite_data_stage`. The finite-data theorem provides the choices,
not an additional premise. The descent specification lemmas supply the existence and
properties of the recorded canonical comparisons; this definition stores their data
and equations and proves no result. No dependency record needs replacement. The
`NagataRawChartData`, `NagataRawOverlapStageData`, `NagataRawOverlapData`, and
`NagataRawMorphismData` structures and `NagataRawTwoWayMorphismChoice` /
`NagataRawMorphismTransport` entries and `NagataRawFiniteStageData` are portions of this same chosen datum, not new
source notions or dependency nodes. The final record stores the morphism-choice portion and a `NagataRawFiniteStageData`
record for precisely those choices. The morphism-choice portion stores the overlap
portion and one two-way choice per overlap; the overlap portion inherits the chart and overlap-stage portions.
Each two-way choice entry stores the proof-valued qcqs and finite-presentation witnesses
required to type the two recorded morphism descents. These are consequences of the
canonical transported-open construction; proof irrelevance identifies them with the
witnesses already stored in the overlap portion. Keeping them as fields rather than
external typeclass parameters avoids repeated instance search at every raw projection,
with no additional mathematical restriction. This keeps elaboration manageable without weakening or splitting
the delivery into extra files.

Edge cases: the empty directed index set is excluded by the source itself. Empty base,
chart and overlap families are permitted by the dependency's `Finite` indices; in that
case all their universal fields are empty families. The stage sets still retain the
original base stage and the explicitly chosen common stage. Empty schemes are allowed.
Zero generators or relations use `Fin 0`, and scalar compatibility still fixes the
constant algebra when no generator is present. The coordinate rings may be zero rings;
no field, characteristic, Noetherian or nontriviality assumption is introduced.
All schemes, ring systems and indices use arbitrary `u`; no separate smaller universe
for test objects or larger universe for a limit index is introduced. Every variable and
universe is explicitly bound, as checked with auto-implicits disabled.

Independent searches: `msearch.py` LeanSearch for "Finite presentation scheme charts
descended along an inverse limit with chosen gluing overlap maps" was unavailable
(HTTP internal error), recorded as unavailable rather than a negative verdict. Loogle
`"pullback.map"` found the existing canonical pullback map and related constructions;
it does not define the chosen raw relative datum. The Mathlib grep
`GluingDatum|gluing.*descent|descent.*gluing` in `AlgebraicGeometry` returned no hits.
Independent `rg` on Mathlib, `WeilConjectures` and project `lean/Sheaf` for raw datum,
gluing/descent in both orders, and each introduced full name found only unrelated
Picard descent and the existing approximation/gluing route. Opened the latter's
finite-presentation approximation signatures: they assert existence of models or
approximation systems and do not record this node's finite chosen lifts and transports.
There is no exact existing declaration to attach instead.

Mismatch repairs: removed all reflexive placeholder equations for ring transitions,
limit projections, chart comparisons, finite stage sets, raw maps and raw opens. Replaced
the universally greatest `overlapStage_le : ∀ s, s ≤ overlapStage` by inequalities only
for the finite selected stages. Replaced the overlap identity on a single unrelated
scheme by the left-to-right isomorphism through the shared basic open. Both right open
data and the reverse morphism descent now participate. Raw charts are base changes at
the raw stage, not unchanged spectra at the original coefficient stages. Raw maps are
over the raw base and tied to the actual descended morphisms, not arbitrary maps over
identity transitions. Removed the separate arbitrary `chartCoordinateIso` and fixed
all affine descent bound choices to the common upper-bound operation. Updated the
main docstring to spell out this construction, retaining source and blueprint tags.
No node statement or dependency was changed, and no theorem or hollow definition was
introduced. The helper definitions contain actual constructions, with no `sorry` data.

Implementation detail of the second reading: the transported overlap schemes are named
`leftScheme` and `rightScheme`, with equality fields to the actual open subschemes.
This avoids reducing the structure-sheaf construction of a nested open subscheme every
time a morphism type is elaborated. All inclusions include the corresponding `eqToHom`,
so this is precisely the same canonical diagram. The final finite-stage record is
parameterized by the earlier choices and stored as `datum.raw`; no field or equation
was discarded. Automatic constructor-injectivity and size-lemma generation is disabled
only for that auxiliary final record; its data, constructor, projections and eliminator
are unchanged. No enlarged heartbeat or compilation timeout is needed.

Validation: compiled the entire delivered module with the local `lcompile` harness,
auto-implicits disabled, and the standard 120-second limit: exit 0 in 31.8 seconds,
with no errors, warnings or `sorry` declarations. All Lean lines are at most 100
characters. The node's `lean.statement` was re-extracted verbatim from the public
`NagataRelativeGluingDatum` signature, and `lean.declarations` lists the complete
construction. `deliver2.py C1 def-nagata-relative-gluing-datum-descent --no-push` then printed
`OK (dry run)` at commit `6ebfce5e6`: server compilation and every preflight check passed.
The final push runs those checks again on the current server base.


## Second reading by Z2

Independent reader Z2-rgd (a fresh `codex exec` session that did not write the module), given
the node, its source place, the C1 version and the new module:

VERDICT: PASS

1. Field-by-field comparison preserves all 34 old chart fields, 40 overlap-stage fields, 14 overlap-comparison fields, and 14 finite-stage fields, exactly once and in order. Types agree after qualifying earlier fields by their parameter records; every qualification names the correct record. The three helper choice/transport records and helper definitions are unchanged. Structural differences are the announced record splits, replacement of inheritance and the bundled `overlap` field by parameters, and assembly through nine dependent fields in the final record.

2. Independently checked the node’s clauses: inverse system and limiting cone; fixed qcqs stage; finite-presentation morphism; finite base-stage affine cover and its pulled-back presentation; chart algebra descents with prescribed scalars and generators; descended overlap opens and their common stage; canonical overlap comparisons; both morphism descents and their common later stages; exact finite stage set `F`; `stage = u(F)`; and canonical raw chart, open, and morphism transports. All are represented.

3. No required construction is left as unconstrained data. Chart comparisons have both projection equations; overlap comparisons respect chart inclusions; the overlap isomorphism is fixed by `overlapIso_canonical`; raw morphisms are fixed by their over-base typing and transport equation. There is no `sorry` in this module. The explicitly supplied qcqs properties follow from the stated setup and constructions. Empty chart and overlap families remain permitted. `Preorder` harmlessly generalizes the stated poset setting.

4. Every declaration has a source docstring with the required blueprint tag. All lines are ≤ 100 characters. No file-local notation, private declaration, or `local instance` command occurs.

5. The global projection instances at line 246 are acceptable: they supply stored proofs for the particular `C.chart j` appearing in the goal. They introduce no recursive chart-class premise and do not provide instances for unrelated schemes.

6. Disabling `genInjectivity` and `genSizeOf` at lines 50–51 changes generated auxiliary declarations, not the records’ fields or mathematical meaning. Both options are acceptable here. The supplied single-file compiler succeeded, reporting 14.7 seconds. No files were edited.
