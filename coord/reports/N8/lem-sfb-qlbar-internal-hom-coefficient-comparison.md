## Worker report

The module [QlbarInternalHomCoefficientComparison.lean] defines the canonical evaluation
transpose `evaluationComparison` for the actual extension-of-scalars functor, and the
continuity predicate `Continuous`. It defines the small tail `fields`, the regular
coefficient complex diagram `coefficients`, and its closure cocone `coefficientCocone`.
`fieldDiagram` states the tail is filtered and final and supplies finite-free stage
modules. `coefficientModules` records that these are the actual restricted regular
field modules and that all transition and closure maps are the prescribed coefficient
inclusions. `coefficientRingColimit` states the corresponding ring-algebra colimit.
`StrictColimitFormula`/`ColimitFormula` contain the termwise colimit, stage and vertex
quasi-isomorphisms, the evaluation-normalized strict comparison, and both displayed
cocone squares. `evaluationComparison_naturality` states naturality in the contravariant
and covariant inputs. `evaluationComparison_restriction` identifies the map after
restriction with the scalar unit and `scalarHomIso`, fixing the canonical evaluation
normalization. `coefficient_colimit_formula` applies the formula to any K-flat and
strictly bounded-below representatives; `qlbar_internalHom_coefficient_comparison`
states the requested isomorphism for the node's continuity and cohomological lower-bound
hypotheses.

The main theorem renders the node's hypotheses as `(E : FiniteIntermediateField ℓ)`,
`K L : DerivedCategory (Internal (Profinite.continuousMapRingObj E) X)`,
`hK : Continuous X ℓ E K`, and `hL : ∃ b : ℤ, L.IsGE b`; the displayed conclusion is
`IsIso (evaluationComparison X (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) K L)`.
`evaluationComparison` is the transpose under
`CondensedRing.derivedTensorHomAdjunction` of the inverse canonical scalar tensorator
`CondensedRing.internalScalarTensorIso` followed by the source evaluation counit.
Thus it is the canonical map `T ⊗ᴸ RHom(K,L) → RHom(K_Ω,L_Ω)`, with no added
geometric, constructibility, perfectness, completeness, or boundedness assumptions.

`Continuous` quantifies over every coefficient-sized small category with
`SmallCategory` and `IsFiltered`, every strict complex representative `P` of `K`,
and the existing strict `SfbHomFilteredColimit.Continuous` predicate. This is the
node's “every small filtered diagram with one common termwise lower bound” condition.
The representative formula is rendered by `StrictColimitFormula`: its first conjunct is
`Nonempty (IsColimit c)`; the next conjuncts are the strict evaluation-normalized
comparison (`Normalized`), the colimit of stage comparisons, the tensor-colimit map,
stage and vertex quasi-isomorphisms, and the two exact equations for the numerator and
resolution-unit denominator. `ColimitFormula` instantiates this with the actual finite
field diagram and cocone, so no chosen finite basis occurs in any map.

The naturality theorem uses arbitrary `f : K' ⟶ K` and `g : L ⟶ L'`; its equality is
exactly contravariant precomposition followed by covariant postcomposition. The
restriction theorem uses the unit of `Mod.derivedExtendMapDerivedCategoryAdjunction`
and the uniquely determined `scalarHomIso`, so the coefficient comparison is pinned by
the scalar adjunction rather than an arbitrary isomorphism. `coefficientRingColimit`
uses the actual `completedSubfieldCocone` whiskered by `fields`; `coefficientModules`
uses `coefficientComplexDiagram` and its `mixedScalarMap` transitions, and states the
actual field-map equations on every site object and section.

Dependencies used (module and declarations):

* `Sheaf.Paper.InternalScalarTensorComparison`, declarations
  `CondensedRing.internalScalarTensorIso`, `internalScalarExtension` and
  `internalScalarTensorComparison`.
* `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison`, declaration
  `ModuleObjectRingedComparison.moduleObject_ringedSite_derived_comparison`.
* `Sheaf.Paper.DerivedInternalHomFilteredColimit` and
  `Sheaf.Paper.DerivedInternalHomFilteredColimitData`, declarations
  `SfbHomFilteredColimit.filteredColimit_comparison`,
  `derivedInternalHom_filteredColimit_comparison`, `comparison`, `homFixed`,
  `tensorFixed`, `roofDenominator`, and `Normalized`.
* `Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram`, declarations
  `coefficientComplexDiagram`, `coefficientComplexCocone`, `mixedScalarMap`,
  and `coefficientComplex_ringMap_comp`.
* `Sheaf.Paper.CompletedCondensedCoefficients`, declarations
  `completedSubfieldCocone`, `completedSubfieldInclusion`, `completedSubfieldLeg`,
  and `completedCondensedAlgebraicClosure`.
* `Sheaf.Paper.QlbarTailModuleColimit`, declarations `qlbarTailStage`,
  `qlbarTailVertex`, and `qlbar_tail_module_colimit`.
* `Sheaf.Paper.FiniteSubextensionsDirected`, `CartesianCoefficients`,
  `ProfiniteCondensedRing`, and `Colimit.Compatibility`, for the directed finite
  subextensions, finite-free assertions, condensed coefficient objects, and actual
  coefficient maps.

Edge cases checked: the tail contains `E` itself; `E = F` uses the rank-one regular
module; finite composita provide common upper bounds; the identity transition is
`Mod.mixedScalarMap_id`; arbitrary inclusion transitions compose by
`Mod.mixedScalarMap_comp`; the closure leg is the actual
`padicSubfieldRingObjToPadicAlgCl` map; rank-zero finite-free stages are allowed by the
existing finite-free stage theorem; and no representative bound is imposed on
`RHom(K,L)`. The formula uses strict bounded-below `L` representatives only where the
source theorem requires them.

Searches for an existing declaration: `msearch.py ... leanfinder "Derived internal
sheaf Hom scalar extension algebraic closure finite coefficient fields continuity"`
returned only ambient closed-category and ordinary-colimit hits; `loogle "internalHom,
AlgebraicClosure"` returned no hits; `msearch.py ... grep
"(internalHom|derivedHom).*(qlbar|padicAlgCl)|(qlbar|padicAlgCl).*(internalHom|derivedHom)"`
returned no hits; project `rg` searches for Qbar/qlbar internal Hom returned no exact
coefficient comparison. The existing declarations listed above are used directly.
No `STATEMENT-DISPUTED` or node fault was found.

## Second reading by N8

I reread the node and signatures clause by clause after compiling. The scalar map is
the actual evaluation transpose; the ring colimit and the strict three-arrow formula
are recorded separately, and the field-module identifications retain all inclusion
maps. I corrected the proof description to apply continuity to F tensor L, whose
common lower bound is available, rather than silently assuming that an arbitrary
functorial K-injective replacement I(L) has a strict lower bound. No second agent
was started, as required by the dispatcher; the maintainer supplies the independent
reading of this delivery.

The additional theorem `coefficient_comparison_roof` makes the link to the strict roof
explicit. It supplies simultaneous normalized `ScalarHomModels`, scalar tensor and Hom
adjunctions, the sectionwise identity restriction comparison `r`, its localized comparison `ρ`,
and the scalar-unit
normalized derived extension comparison `γ`. Both native-to-ringed Hom isomorphisms
carry evaluation to evaluation, via `HomTransportNormalized` (the equation already in
the recorded module-object theorem). The final equation identifies the transported
actual `evaluationComparison` with `SfbFlatHom.comparison`. The supplied
`EvaluationRoof` then gives its restricted numerator/inverse-denominator equation on
representatives, with all representative maps normalized on pure tensors. Together
with `coefficientModules` and `coefficient_colimit_formula`, this identifies the
three-arrow formula with the very map in the main theorem. The scalar-unit equality
excludes arbitrary twists of γ, and r is identity on every underlying section.
The heterogeneous equality for ρ specifies precisely the localization of r, avoiding
a silent identification of the two exact-functor localization implementations.
These are conclusions and comparison normalizations, not new hypotheses on K or L.

Further dependency declarations: `Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof`,
`CategoryTheory.SfbFlatHom.EvaluationRoof`, `comparison`, `restrictedComparison`,
`sourceMap`, `targetMap`, and `evaluationRoof`; and
`Sheaf.CategoryTheory.InternalSectionScalarAdjunction`,
`InternalAbelianSheafModule.sectionScalarMap` and `internal_section_scalar_adjunction`.
The returned-review ownership repair is documented below. No Lean definition or statement is changed.

The final transport theorem is stated for any flat condensed coefficient map and is
instantiated at `Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E`. This generality concerns
the canonical comparison construction only; the isomorphism and colimit formula retain
exactly the item's ell-adic field and continuity hypotheses. All universes and map
variables are explicitly bound. `HomTransportNormalized` only packages the evaluation
equation of the already recorded comparison theorem, and has actual Prop-valued data.


## Returned-review repair (immutable head e3ce9f8f7f60)

The saved packet first passed `deliver2.py --no-push` as e4e53c14d6b. That mechanical
success did not repair H2: the saved packet still cited theorem nodes for plain data.
The following repair changes the dependency records and report only; the reviewed Lean
file remains byte-identical. No statement correction, new hypothesis, or new Lean notion
is introduced.

Each of the five theorem-module helpers now has a definition owner, listed below.
The item's `stmt_deps` cite those owners instead of
`lem-sfb-module-object-ringed-site-derived-comparison`,
`lem-sfb-qlbar-tail-module-colimit`, `sk-prop-sfb-qlbar-colimit-x`,
`lem-sfb-hom-flat-evaluation-roof`, and
`lem-sfb-internal-section-scalar-adjunction`. All five theorem nodes remain in
`proof_deps`; the latter two are added there because they were previously only statement
dependencies. `lem-sfb-dc-hom-filtered-colimit` is dropped from `stmt_deps` and retained
in `proof_deps`: its declaration names occur only in the proof docstring. The direct
statement dependency `def-coef-hom-representative-evaluation` now owns the explicit uses
of `coefficientHomResolution` (including its irreducibility attribute).

All new definition records use `existing: true` and the published module paths. There
are no new Lean files, copied definitions, theorem choices or arbitrary maps. Their
`lean.statement` signatures are extracted verbatim starting at the declaration keyword
(as required by the gate, omitting the preceding noncomputable modifier).
The inherited ancestor is null: `blueprint_refs.py ancestor` confirms this, so each new
node preserves that provenance and prepends this item to the inherited `via` list.

The search log records actual LeanSearch, Loogle and Mathlib grep results. LeanSearch
returned eight generic module/tensor/restriction hits; Loogle returned zero hits with
unknown identifier BraidedCategory; Mathlib grep returned zero hits. Exact-name searches
of all DAG definition nodes found no owner. The upstream source has only unrelated
HomologyEvaluationRoof module imports; the project source has precisely the five
published implementations being attached here. Blueprint searches returned zero for
section scalar, tail module, evaluation roof and subfield cocone; the nine braiding hits
concern ordinary module braidings and trace pairings. In particular
`def-sfb-qlbar-x-cocone` already owns the abelian-sheaf cocone; the new ring-object owner
cites it and adds only the existing `Mon` bundling with its actual unit/multiplication.

The advisory about the `Nonempty EvaluationRoof` conjunct does not require a statement
change: it remains the reviewed witness used together with the final transport equation,
and now its data type has a definition owner while existence is a proof dependency.
The Lean imports remain byte-identical as explicitly permitted by the return: the
stage-2 contract requires imports for the stated proof dependencies, including the
general filtered comparison and coefficient/colimit tools. No advisory triggers a
change to a reviewed mathematical signature.

## New nodes

`def-sfb-native-derived-koszul-braiding` owns only the existing
`AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.internalBraiding` instance in
`Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison`. Its definition transports the
actual K-flat Koszul braiding along the native/localization monoidal equality; it
states no comparison theorem. Source: Stacks 06YL and the existing source docstring.
It cites the existing relative derived tensor-Hom node, covers every scheme and
commutative condensed coefficient, and keeps the given derived universes. Searches
above found no existing definition owner of this particular native derived instance.
The mathematical braiding itself is reused unchanged.

`def-sfb-qlbar-tail-module-objects` owns the existing `qlbarTailStage` and
`qlbarTailVertex` in `Sheaf.Paper.QlbarTailModuleColimit`. These are the actual regular
F and closure modules restricted to E, then sent through section reconstruction.
Source: the first sentence of blueprint `lem-sfb-qlbar-flat.proof.md`. The cited
coefficient-map and equivalence nodes supply every input. The case F=E uses restriction
along identity; E itself and every finite containing field are allowed. It neither
asserts a colimit nor chooses its vertex from a theorem. Searches above found only
the theorem-node listing of these helpers, so the new node attaches their definitions.

`def-sfb-qlbar-ring-object-cocone` owns `completedPointSubfieldDiagram`,
`completedPointSubfieldCocone`, `completedSubfieldCocone`, `completedSubfieldInclusion`
and `completedSubfieldLeg` in `Sheaf.Paper.CompletedCondensedCoefficients`.
Source: blueprint `def-sfb-qlbar-x-cocone.md` and the existing third-comparison helpers.
The definition bundles the existing coefficient cocone in ring objects and maps it
through the actual monoidal point pullback. It cites the existing abelian cocone node
and the point-pullback/ring-pullback nodes; it adds no colimit assertion. It includes
identity transitions and the actual closure legs, also for the empty scheme.
The searches distinguish this ring-object bundle from the already owned abelian
cocone and find no definition owner of these bundled declarations.

`def-sfb-flat-hom-evaluation-roof-data` owns the ten existing data declarations
`scalarTensor`, `comparison`, `restrictedComparison`, `representative`, `sourceMap`,
`targetMap`, `denominator`, `numerator`, `denominatorInverse`, and `EvaluationRoof`
in `Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof`.
Source: Stacks 08J9/0A95/03CZ and the existing evaluation-roof refinement of the final
blueprint Hom paragraph. Its statement names the actual evaluation transpose, the
fixed strict models, pure-tensor normalization, exact-extension comparison, denominator
and both roof equations, naturality and coefficient coherence. It defines the data
type without asserting inhabitation. All models come from the cited scalar-Hom,
representative-evaluation and strict-model/roof owners; no finite freeness, continuity,
boundedness, or unrequested coefficient flatness is imposed on the data constructors.
Identity coefficients and arbitrary complexes are included. The searches found the
published implementation and its theorem record, but no definition owner.

`def-sfb-section-scalar-map-data` owns `sectionScalarMap`, `internalScalarGenerator`,
and `scalarInternalModules` in `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`.
Source: Stacks 03EK/03CV and blueprint scalar pullback proof (1). The map is reconstructed
from the actual internal coefficient map, objectwise unchanged; the generator is the
actual tensor generator followed by the extension coequalizer projection. The sheaf
tensor and internal/sectionwise module equivalence nodes supply the inputs. No flatness
or invertibility is assumed, and identity maps are included. The searches found no
separate definition owner; the existing definitions are attached, not implemented again.

### Repair self-check by N8

I reopened the saved node, the whole consumer module, and all five published helper
modules. I checked the five owners against each explicit consumer use: internalBraiding
in HomTransportNormalized; both tail objects in coefficientModules; the ring cocone in
coefficientRingColimit; EvaluationRoof and comparison in coefficient_comparison_roof;
and sectionScalarMap in its explicit coefficient map. coefficientHomResolution is now
covered directly too. The general comparison remains proof-only. Each new signature is
verbatim from its source, every new node is directly cited, and none cites this item or
a theorem downstream of its own data. The five theorem nodes remain available for the
proof. All hypotheses and all previously checked naturality, colimit, universe and
normalization clauses stay identical; the main signature and entire Lean file are
unchanged from the saved reviewed packet.


The first repaired-packet dry run compiled the consumer and existing-declaration probe.
It found bracketed multi-citations (the gate requires each identifier in its own pair
of brackets) and two signatures with the preceding noncomputable modifier. Both record
format issues are repaired. It also rejected the required proof dependency additions:
"the item changed in proof_deps without a statement correction (proof and proof_deps
change only as far as a correction of the statement forces it)". The wrapper explicitly
permits additive proof dependency repairs, but server preflight still rejects them.
The item's statement is correct and unchanged, so no fictitious statement_change has
been added. A second dry run is used to confirm that this is the only remaining issue.


Confirmed final tool failure: after fixing all citation/signature record diagnostics,
the second repaired-packet dry run compiled both the byte-identical consumer and all
existing-declaration probes, and rejected only two consequences of the same gate bug:
(b) "the item changed in proof_deps without a statement correction (proof and proof_deps
change only as far as a correction of the statement forces it)"; (e) a missing
Statement corrected section because it incorrectly classifies this dependency-only
repair as a statement correction. The required additions are
lem-sfb-hom-flat-evaluation-roof and lem-sfb-internal-section-scalar-adjunction.
The other four theorem dependencies already occur in the unchanged base proof_deps.
Removing these two additions would violate the return's instruction to keep the
theorems in proof_deps. Changing the already accepted mathematical statement merely
to satisfy this gate would be a spurious statement correction. No tool was edited or
bypassed; the complete compiled repair is retained in this sandbox, unpushed.


## Dispatcher retry verification (2026-10-21)

As instructed, this retry first read the retained report and ran the saved packet
through `deliver2.py N8 lem-sfb-qlbar-internal-hom-coefficient-comparison --no-push`.
The wrapper compiled both Lean files (the consumer and existing-declaration probe),
staged the repaired packet, and failed server preflight with exactly the same two
remaining diagnostics:

* (b) "the item changed in proof_deps without a statement correction (proof and
  proof_deps change only as far as a correction of the statement forces it)".
* (e) "the item's statement is corrected but the report has no non-empty section
  '## Statement corrected' (old statement, what was wrong, the source place, one
  line per citer)".

A fresh comparison with the current read clone shows that statement and proof are
unchanged, no statement_change is present, no base proof dependency is removed,
and the only proof_deps additions are lem-sfb-hom-flat-evaluation-roof and
lem-sfb-internal-section-scalar-adjunction, both explicitly required by the return.
All five new definition owners are existing:true; the six flagged theorem nodes
are absent from stmt_deps, and all six remain in proof_deps. The consumer directly
cites def-coef-hom-representative-evaluation.

Read-only inspection of deliver2.py lines 132-140 confirms its explicit allowance
for additive proof dependency repairs on a maintainer return while the statement
remains verbatim. Server preflight still rejects that authorized case. Removing
the additions would undo the required repair; inventing a mathematical statement
correction would contradict the accepted statement and the stage-2 contract. No
launcher or project tool was edited, no preflight was bypassed, no upstream source
was changed, and nothing was pushed. The compiled repair packet remains intact
in the sandbox for the gate to be reconciled.


## Dispatcher retry verification (2026-10-22)

This retry first read the saved report and ran the unchanged repaired packet with
`deliver2.py N8 lem-sfb-qlbar-internal-hom-coefficient-comparison --no-push`.
Both server compiles passed (the consumer and existing-declaration probe). Preflight
again rejected exactly (b), proof_deps changed without a statement correction, and
(e), missing Statement corrected report section. Nothing was pushed.

A fresh JSON comparison with the refreshed read clone confirms that the statement
and proof are unchanged, no statement_change is present, and the only proof_deps
changes are the two additions explicitly required by the maintainer return:
lem-sfb-hom-flat-evaluation-roof and lem-sfb-internal-section-scalar-adjunction.
All six flagged theorem nodes are absent from stmt_deps and present in proof_deps;
all five existing:true definition owners are direct statement dependencies.
Read-only inspection of deliver2.py confirms that its dependency-only repair branch
explicitly permits additive proof_deps changes while the statement is unchanged.
The server preflight rejects this permitted case. No mathematical correction is
justified by this diagnostic, and removing the additions would violate the return.
The launcher tools were neither modified nor bypassed; the repair packet is retained.


## Saved-packet retry (2026-10-21T16:13:36Z)

Read the retained report first and ran the required unchanged saved-packet dry run.
The consumer and existing-declaration probe both compiled cleanly on the server.
Preflight rejected only (b), additions to proof_deps without a mathematical statement
correction, and (e), the resulting demand for a Statement corrected section.
Nothing was pushed.

Compared all node fields with the refreshed current read clone: statement, proof,
and statement_change are unchanged. The only proof_deps delta is addition of
lem-sfb-hom-flat-evaluation-roof and lem-sfb-internal-section-scalar-adjunction,
explicitly required by the immutable-head return. All six flagged theorem nodes
are absent from stmt_deps and present in proof_deps. All five existing:true
definition owners are directly cited; def-coef-hom-representative-evaluation is
also cited. The reviewed Lean SHA256 remains
6c3a9e3717969241fde6412922888403c66603384fa2afe92f9328aa6b7e7164, identical to
the retained repair-self-check.json.

Read-only diagnosis confirms deliver2.py explicitly permits additive proof_deps
repairs without changing the statement. In contrast, tools/node_fields.py
correction_fields treats any proof_deps change as a correction, and
check_statement_change rejects it when statement is unchanged. The live server
preflight reproduces exactly this contradictory refusal. No source-based statement
correction is warranted; removing the additions would violate the return. No tool
was edited, copied, bypassed or run outside the prescribed wrapper. The compiled
repair packet remains intact pending reconciliation of the preflight gate.


## Saved-packet retry (2026-10-21T16:21:56Z)

The prescribed first dry run again compiled both server files and rejected only
(b), proof_deps changed without a statement correction, and (e), the resulting
missing Statement corrected section. Nothing was pushed. The refreshed base comparison
confirms that statement, proof and statement_change are unchanged; only the two
review-required proof dependencies are added, with none removed. All five existing:true
definition owners are direct statement dependencies, all six flagged theorem nodes
are proof-only, and def-coef-hom-representative-evaluation is cited. The Lean SHA256
remains 6c3a9e3717969241fde6412922888403c66603384fa2afe92f9328aa6b7e7164.

Read-only inspection reconfirms that deliver2.py permits this additive dependency
repair while tools/node_fields.py rejects any proof_deps change without a changed
mathematical statement. No source-based statement correction is justified, and
removing either addition would violate the immutable-head return. No tool was
modified or bypassed; the repaired packet is retained.


## Saved-packet retry (2026-10-21T16:29:39Z)

The required first dry run compiled the consumer and existing-declaration probe
cleanly, then failed preflight with the same two diagnostics: (b), proof_deps
changed without a statement correction; (e), missing Statement corrected section.
The refreshed-base comparison confirms unchanged statement and proof and only the
two review-required proof dependency additions. All six flagged theorem nodes are
proof-only; all five existing:true definition owners are directly cited, together
with def-coef-hom-representative-evaluation. The consumer SHA256 remains
6c3a9e3717969241fde6412922888403c66603384fa2afe92f9328aa6b7e7164.
Read-only inspection of deliver2.py confirms additive proof dependency repairs are
permitted, while tools/node_fields.py rejects those same changes without a changed
statement. No mathematical correction is warranted, and deleting the additions
would undo the return's explicit repair. No tool was changed or bypassed and
nothing was pushed; the repaired packet is retained.


## Saved-packet retry (2026-10-21T16:36:19Z)

Read the retained report and ran the prescribed saved-packet dry run first. Both
server compiles passed. The wrapper staged the five existing:true definition owners,
the consumer node and module, and this report, but server preflight again rejected
only (b), proof_deps changed without a statement correction, and (e), the resulting
demand for a Statement corrected section. Nothing was pushed.

The refreshed-base self-check confirms that statement, proof and statement_change
are unchanged. The only proof dependency changes are the additions of
lem-sfb-hom-flat-evaluation-roof and lem-sfb-internal-section-scalar-adjunction,
both explicitly required by the immutable-head return; no proof dependency is
removed. All six flagged theorem nodes are absent from stmt_deps and present in
proof_deps. All five existing:true definition owners are directly cited, as is
def-coef-hom-representative-evaluation. The consumer SHA256 is unchanged:
6c3a9e3717969241fde6412922888403c66603384fa2afe92f9328aa6b7e7164.

Read-only inspection confirms deliver2.py explicitly allows these additive proof
dependency repairs, while tools/node_fields.py correction_fields and
check_statement_change reject any proof_deps change without a changed statement.
This is the same concrete tool refusal, not a Lean or packet-content failure.
Removing either addition would violate the maintainer return; fabricating a
mathematical statement correction would violate the accepted statement and source.
No tool was edited or bypassed, no upstream file was changed, and the complete
repair packet remains retained in the sandbox.


## Saved-packet retry (2026-10-21T16:46:54Z)

Read the saved report and ran the prescribed saved-packet dry run first. The
consumer and existing-declaration probe passed server compilation; preflight
rejected only (b), proof_deps changed without a statement correction, and (e),
the resulting demand for a Statement corrected section. Nothing was pushed.

Compared the repaired packet with the refreshed read clone. Statement, proof
and statement_change are unchanged; the only proof_deps additions are
lem-sfb-hom-flat-evaluation-roof and lem-sfb-internal-section-scalar-adjunction,
both required by the return, and no proof dependency is removed. All six
flagged theorem nodes are absent from stmt_deps and present in proof_deps;
all five existing:true definition owners and def-coef-hom-representative-evaluation
are directly cited. The consumer SHA256 still matches repair-self-check.json:
6c3a9e3717969241fde6412922888403c66603384fa2afe92f9328aa6b7e7164.

Read-only inspection of deliver2.py confirms its explicit permission for additive
proof dependency repairs without a statement correction. In tools/node_fields.py,
correction_fields includes every proof_deps delta and check_statement_change rejects
it when the statement is unchanged. The prescribed wrapper reproduces this tool
conflict. Removing the additions would undo the required repair; a fictitious
statement correction would violate the accepted statement. No tool was edited or
bypassed, and all repair work is retained in the authorized sandbox.


## Saved-packet retry (2026-10-21T16:56:37Z)

Read the retained report and ran the prescribed saved-packet dry run first.
Both server compile checks passed; preflight again rejected only (b), proof_deps
changed without a statement correction, and (e), the resulting demand for a
Statement corrected report section. Nothing was pushed.

The refreshed-base comparison confirms unchanged mathematical statement, proof
and statement_change. The only proof dependency additions are
lem-sfb-hom-flat-evaluation-roof and lem-sfb-internal-section-scalar-adjunction,
which the immutable-head return explicitly requires; none is removed. All six
flagged theorem nodes are absent from stmt_deps and present in proof_deps. All
five existing:true definition owners are directly cited, together with
def-coef-hom-representative-evaluation. The consumer SHA256 remains
6c3a9e3717969241fde6412922888403c66603384fa2afe92f9328aa6b7e7164.

Read-only inspection confirms the conflict persists: deliver2.py explicitly
permits additive proof dependency repairs for maintainer returns without a
statement correction, but tools/node_fields.py classifies every proof_deps
delta as a correction and rejects it when the statement is unchanged. Removing
the additions would undo the required repair; fabricating a statement change
would alter an accepted statement without mathematical grounds. No tool was
modified or bypassed. The complete repaired packet remains in the sandbox.


## Saved-packet retry (2026-10-21T17:02:10Z)

The required initial saved-packet dry run compiled the consumer and existing-declaration
probe on the server, then failed preflight with exactly two reasons: (b), proof_deps
changed without a statement correction; (e), the consequent missing Statement corrected
section. Nothing was pushed.

A fresh comparison with the current read clone confirms that statement and proof are
unchanged, there is no statement_change, and the only proof_deps additions are the
review-required lem-sfb-hom-flat-evaluation-roof and
lem-sfb-internal-section-scalar-adjunction. All five existing:true owners are directly
cited. The consumer SHA256 remains
6c3a9e3717969241fde6412922888403c66603384fa2afe92f9328aa6b7e7164.

Read-only inspection confirms deliver2.py explicitly permits additive proof dependency
repairs for a maintainer return, while tools/node_fields.py correction_fields and
check_statement_change reject those same additions without a changed mathematical
statement. Removing the additions would violate the return; no source-based statement
correction is warranted. No tool was edited or bypassed. The compiled repair packet
is retained in the authorized sandbox.


## Saved-packet retry (2026-10-21T17:08:32Z)

The prescribed first dry run passed both server compilation checks and failed
only preflight (b), proof_deps changed without a statement correction, and (e),
the consequent demand for a Statement corrected section. Nothing was pushed.

The read-clone node now already has the same proof_deps as the saved packet;
its only node-field differences are lean and stmt_deps. The server preflight
still diagnoses a proof_deps change against its immutable branch baseline.
The five existing:true definition owners are all direct statement dependencies,
all six flagged theorem nodes are proof-only, and the reviewed Lean SHA256 remains
6c3a9e3717969241fde6412922888403c66603384fa2afe92f9328aa6b7e7164.

Read-only inspection confirms deliver2.py permits additive proof dependency
repairs without a changed mathematical statement, whereas node_fields.py
correction_fields/check_statement_change reject that case. The wrapper reproduces
this contradictory refusal. Neither removal of the review-required dependencies
nor a fictitious statement correction is an authorized repair. No tool was edited
or bypassed; the compiled repaired packet remains in the sandbox.


## Successful saved-packet retry (2026-10-21T17:14:36Z)

The prescribed initial saved-packet dry run now passes server preflight and both
server compile checks: `OK (dry run): commit 2da826511ba`. The previous dependency-only
preflight refusal no longer occurs. The saved repair is retained without changing
the accepted mathematical statement or the Lean module.

The final self-check compares the packet with the refreshed current read clone:
only `lean` and `stmt_deps` differ on the main node; statement, proof and proof_deps
are unchanged. All six flagged theorem nodes are absent from stmt_deps and present
in proof_deps. All five existing:true definition owners are directly cited, as is
def-coef-hom-representative-evaluation. Their definition records own the actual
braiding, tail objects, ring cocone, evaluation-roof data and section scalar map.
The main recorded signature occurs verbatim in the module, and its reviewed SHA256
remains 6c3a9e3717969241fde6412922888403c66603384fa2afe92f9328aa6b7e7164.
The published owning declarations and their source docstrings were rechecked.
No project or launcher tool was changed or bypassed.
