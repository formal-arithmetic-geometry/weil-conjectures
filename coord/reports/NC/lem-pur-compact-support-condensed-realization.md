## Worker report

Group NC, item lem-pur-compact-support-condensed-realization, stage 2, 2026-10-18.
This packet retains and completes the saved reconstruction draft. Its principal
module is Sheaf.Paper.CompactSupportCondensedRealization. The final theorem asserts
existence of ComparisonFamily; its fields supply the simultaneous integral,
rational, finite-coefficient and compactification-refinement comparisons.
Definitions have actual data. Each postponed theorem is named, belongs to the
owning node, and has a source and natural-language proof in its docstring.

The hypotheses and clauses are represented as follows.

* Prime ell: `(l : ℕ) [Fact l.Prime]`. Positive prime characteristic and ell different
  from it: `(k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ l)]`. The characteristic p is `ringChar k`.
* A finite normed coefficient extension is `E : Type u` with `NormedField E`,
  `NormedAlgebra ℚ_[l] E`, and `FiniteDimensional ℚ_[l] E`. Finite embeddings are
  actual `AlgHom`s over ℚ_[l]; no extra quotient flatness is assumed.
* `CondensedERealization.Base k` is precisely the recorded separated finite-type
  k-scheme bundle. The morphism is an actual scheme morphism with
  `f.IsOver (Spec (.of k))`. `Compactification f` is the recorded geometric
  compactification, with its actual open immersion and proper structural map.
* `quotientRings` and `quotientMaps` use the recorded quotient rings at n+1 and
  their actual adjacent maps. `coefficientSequenceModules` and its ordinary
  derived category retain the small-site and coefficient universes. The index
  n=0 represents the paper's first positive quotient, not exponent zero.
* The integral category is exactly `CondensedERealization.Integral`, hence the
  recorded PbcBoundedConstructibleComplete category. Its completed-ring
  presentation is transported by `purCoefficientModel`, not redefined.
* `systemSupport` is exact geometric extension by zero followed by separately
  derived proper image on the full ringed sequence site. `strictTower` is its
  recorded coefficient restriction. `IntegralModel.towerEvaluation` and
  `.towerTransition` identify it with the strict compact-support reduction
  tower and its actual reduction arrows for every comparable pair of levels.
* `rawSupport` is literally that strict tower followed by the published total
  derived limit and the inverse completed-coefficient presentation.
  `IntegralModel.preserves`, `.linear`, `.commShift` and `.triangulated` give the
  stipulated exact R-linear integral support. `integralSupport` is its full
  subcategory restriction.
* `alpha` is a defined natural transformation: the coefficient-presentation
  counit followed by the reduction/limit adjunction counit. Its invertibility
  is `RealizationAt.alpha_isIso`; normalization of its target is
  `IntegralModel.normalized`. The dependency calculus's counit_projection
  equation identifies its evaluated adjuncts with the actual total-limit
  projections. This construction and `IsIntegralScalarSquare` live on whole
  derived semilinear systems, including their coefficient transitions.
* `CoefficientData.realization` is the recorded derived coefficient-extension
  realization. `rationalSupport` uses raw scalar localization on morphisms.
  `RealizationAt.realization` is the natural isomorphism a, with the exact
  source and target specified in the node.
* The ambient condensed support is always the archived
  `rightDerivedLowerShriekOfCompactification`, whose definition is termwise
  exact open extension followed by the separately right-derived proper image.
  `RealizationAt.field_preserves` and `omegaSupport_preserves` state preservation
  for these precise composites.
* `omegaRingMap` maps into the archived finiteIntermediateFieldValued subring.
  It never replaces the finite-valued closure sheaf by all continuous Ω-valued
  functions. `omegaMap` and `omegaScalar` retain this coefficient ring.
* `condensedProjection` is the actual proper coefficient mate followed by the
  open scalar comparison. `finiteProjection_isIso` and `omegaProjection_isIso`
  assert invertibility on exactly the bounded constructible inputs.
* `integralScalar` is the published completed integral tensor functor, with the
  canonical comparison to the strict Roos/K-flat integral scalar extension.
  `FiniteComparison.comparison` is its natural comparison with integral support.
  `.reduction` is the full-system alpha square; `.rationalization` is the square
  with a, the section-normalized `latticeScalar`, and the preceding original
  condensed coefficient projection.
* Coefficient identity and tower laws are `ComparisonFamily.scalar_identity`
  and `.scalar_composition`, using the published tensor unit and associator,
  lifted by `integralScalarId` and `integralScalarComp`.
* `systemRefinement` is the intrinsic whole-system proper/open mate and proper
  compositor. `rawRefinement` takes its actual total limit, and
  `integralRefinement` restricts this actual map to the integral full category.
  `fieldRefinement` is defined by the original open-unit transpose and the actual
  proper-image compositor. `RefinementCoherence` states invertibility and the
  alpha and a squares. `ComparisonFamily.scalar_refinement` is the integral
  scalar/refinement square. The system and condensed identity and composition
  equations are separately named helper statements.
* `IsShiftCoherent` uses the recorded integral triangulation and tensor-induced
  rational shifts. It normalizes the reduction shifts by the actual counits,
  the realization shifts by the actual scalar-extension comparisons, and states
  shift compatibility for alpha, a and the limit presentation. Rational support
  shifts are the localization of the integral comparison on every integral
  input. The functors and natural transformations already include morphism,
  identity and composition preservation as structure laws.

Dependency declarations used (module / principal declarations):

* Sheaf.NumberTheory.Padics.CoefficientExtensionFinite /
  Padic.finite_coefficientExtensionRing, coefficientExtensionRing and its maps.
* Sheaf.Paper.IntegralUniformCoefficient /
  Scheme.pbcBoundedConstructibleComplete and the unchanged underlying
  PbcIsBoundedConstructibleComplete / PbcBoundedConstructibleComplete.
* Sheaf.Paper.CoefDerivedSystemEvaluationCalculus /
  coefficientDerivedSystemEvaluationCalculus, CoefficientDerivedSystemCalculus,
  its actual reduction, adjunction, reductionEvaluation and counit_projection.
* WeilConjectures.Compactification.Refinement /
  Compactification.Refinement, Refinement.id, Refinement.comp.
* Sheaf.Paper.CompactSupportReductionTower /
  exists_compactSupportReductionTower, compactSupportRestrictedLevel and
  compactSupportRestrictedTransition.
* Sheaf.Paper.SemilinearDerivedSections /
  SemilinearSections.semilinearDerivedSections, scalar coefficientExtension.
* Sheaf.Paper.CondensedERealization /
  condensedE_realization, CondensedERealization.Data / At / Along / Exchange.
* Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing /
  continuousCoefficientRingObj and condensedRingObj, with the archived Mod
  categories and proper/open derived operations.
* WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit /
  constructibleCocone_isFilteredTwoColimit and padicAlgClRingObj.
* Sheaf.Paper.IntegralScalarExtensionUniverses /
  integralScalarExtensionOfUniverses and its representative comparison;
  PbcScalarExtension supplies pbcEmbeddingIntegralTensor, its canonical completed
  scalar comparison, pbcAmbientScalarComp and pbcEmbeddingAmbientUnit.
* Sheaf.CategoryTheory.LocalizedModuleExactForSystems /
  localizedSystemExtension, localizedSystemRestriction, localizedSystemExact
  and the section-normalized localizedSystemAdjunction.
* Sheaf.SixFunctors.SemilinearProperOpenMatePasting /
  SemilinearProperOpen.J / R / gamma / sComp / sId and their actual adjunctions.
* Sheaf.Paper.CompletedCoefficientPresentationTransport /
  purCoefficientModel, purOrdinaryCoefficientModel and the normalized purScalarModel.
* Sheaf.Paper.BasicOperationsCoefficientReduction /
  OperationScalarTransport, with its tensor-section and universal derived-counit
  normalization fields; scalarModelTransport uses this uniquely specified datum.
* Sheaf.Paper.IntegralCompactSupportCoefficientComparison /
  PurCompactSupport.tensorSquare and normalized scalar constructions.

Edge cases checked: the empty scheme and zero complexes; n=0 means exponent one;
identity coefficient maps; identity and composite refinements; arbitrary ramified
finite extensions (cofinal levels en, never an unjustified same-power flatness
claim); nontrivial clopen complement of a proper refinement; the closure ring's
finite-subfield-valued condition; whole-system naturality before evaluation;
independent object and morphism universes of the small pro-etale site. No target
statement or dependency statement is changed.

Searches: retained searches.jsonl records msearch LeanFinder on “compact support
functor comparison completed integral coefficients condensed field coefficients
realization” (only unrelated condensed/test-function results), Loogle on
“compactSupport, condensed, realization” (no matching declaration), and Mathlib
regex compactSupport.*[Cc]ondens|compact.support.*realiz|CompactSupport.*Realiz
(no match). A further LeanSearch with the same words returned only unrelated
results. rg in WeilConjectures and lean/Sheaf found the general qcqs realization,
completed coefficient and scalar-comparison APIs used above, not this combined
statement. Searching the exact item id in WeilConjectures found no implementation.
The reconstructed packet includes the main existence statement and its complete comparison interfaces.

The generic `condensedProjection_id`, `condensedProjection_comp` and
`condensedProjection_refinement` give the identity, tensor-tower and refinement
clauses for the original condensed maps, including the closure tail. The strict
`fieldMap_id`, `fieldMap_comp` and `omegaMap_comp` identify their ring maps with
the stated finite coefficient embeddings. `fieldScalar_preserves` and
`omegaScalar_preserves` supply exactly the bounded-constructible scalar inputs
for the refinement square. `condensedProjection_commShift` uses the canonical
ambient derived shifts; the integral finite comparisons and refinements inherit
their shift compatibility from the full-system alpha equations and the normalized
counits, which are faithful on the complete integral category.

The source reading includes the current main-20261015 unit proof Steps 2–3,
thm-pur-rational-and-qbar-purity proof Steps 1–2, and the explicit
pur713-def-lower-shriek-module definition. The item is an agent-formulated
prerequisite to those arguments; its source record explicitly says that it is
not literally a theorem of Bhatt–Scholze. No change to that obligation is made.

Validation is in progress; compilation and the prescribed dry-run gate will be
recorded below before delivery.

## Dependency modules

No dependency module is delivered. The saved `lem-weil-pbc-condensed-e-realization`
replacement is obsolete against the current published source: all three delivered
modules compile against the unchanged published `CondensedERealization`, whose
inferred `moduleEncoding` signature has the required site and coefficient universes.
The earlier repair history below records the prior interface issue; the final
current-source check supersedes it. The current proof, helper declarations, imports
and node metadata remain owned by the live dependency and are not delivered.

## Second reading by NC

The dispatcher forbids starting other agents. This section records a separate
self-reading against the node and current dependencies. The initial saved draft
was incomplete and had no main existence statement. Repairs retain the actual
strict tower and fixed ambient condensed composite; supply the missing comparison
and refinement interfaces; use the full-system scalar square; retain the
finite-valued closure coefficient; and expose identity/tower and shift equations.
The compiler-driven universe repair retains the small internal-module derived
category and the larger completed-module derived category, rather than equating
site universes. The two new definition nodes below were also read against the constructions and the source proof steps. Final compiler and delivery checks are recorded below.

## New nodes

def-pur-operation-scalar-transport owns the existing
`WeilConjectures.OperationScalarTransport` in the unchanged published
`Sheaf.Paper.BasicOperationsCoefficientReduction` (line 228). It defines the
ordinary and derived comparison isomorphisms, their equality on every sheafified
pure tensor, and their universal-derived-counit equation on every complex; it
asserts no existence or uniqueness. Its source is the current blueprint's basic
operations coefficient-comparison normalization and Stacks 03EK/06YY, as recorded
in that declaration's docstring. LeanSearch returned general coalgebra and module
counits; Loogle and Mathlib grep returned no match. DAG/blueprint and source
searches found this published structure but no definition node owning it. Hence
its record is `existing: true`, with no new module or duplicate definition.

def-pur-condensed-compact-support-projection defines the original condensed
proper/open coefficient projection, its actual scalar tensor adjunction, tensor
unit/associator, and the open-unit-normalized refinement arrow. The named helper
statements retain the shift, identity, tower, and refinement equations; they do not
assume that the coefficient projection is invertible. The definition uses the
archived internal-module categories and their actual proper/open functors. Its
module is Sheaf.Paper.CondensedCompactSupportProjection; the declaration names
remain in WeilConjectures.CompactSupportCondensedRealization. This is not the
moduleObjectProjectionMap (a tensor projection for one ring), or geometric-Weil
compact-support transport. The needed map changes the coefficient ring and pastes
the proper and open comparisons in the specified order.

def-pur-semilinear-compact-support-coefficient-transport defines the whole-system
coefficient restriction and its adjunction mates, including the canonical scalar
projection for the strict proper/open system. It supplies the uniquely normalized
limit/restriction comparison and reduction/scalar balancing isomorphism. Its
normalization uses actual strict-tower projections and the universal right-derived
unit on all system complexes, before coefficient evaluation. Its module is
Sheaf.Paper.SemilinearCompactSupportCoefficientTransport. This is not the existing
constant-tower limit comparison, nor SemilinearGeometryOps.coefficientMate, which
changes levels in one coefficient tower. The same-index finite-field inclusions
need not be flat; the construction uses exact coefficient restriction instead.

For both new nodes, blueprint_refs.py ancestor returned None (matching the item's
ancestor); the exact searches "compact support coefficient projection" and
"semilinear coefficient transport" each returned zero blueprint nodes. A DAG regex
search was checked against the closest nodes: def-pur-compact-support-transport,
def-sfb-module-object-projection-map, lem-pur-ringed-coefficient-projection-cocycle,
def-coef-semilinear-geometry-ops, def-coef-semilinear-geometry-base, and
lem-pur-normalized-reconstruction-adjunction-calculus. None defines these particular
canonical maps. New Mathlib searches are recorded verbatim in each new node:
LeanSearch returned eight unrelated compactly supported-map declarations;
LeanFinder returned eight profinite/discrete-condensed declarations; regex grep
returned no hits. rg of WeilConjectures and lean/Sheaf returned only the distinct
constant-tower comparison noted above. All underlying notions and operations are
imported; no second coefficient or compact-support category is introduced.

Separate self-reading of the new nodes checked every construction clause against
its module. The main theorem continues to quantify over all separated finite-type
k-schemes, all finite coefficient extensions and their embeddings, all
compactifications/refinements, and the finite-valued closure coefficient ring.
The canonical maps, normalization equations, and full-system coefficient squares
are retained verbatim under their original declaration names. No definition has
postponed data. Definitions selected from a postponed existence theorem are fixed
uniquely by the displayed section, universal-unit, or adjunction normalization.

## Resumed packet self-check

The resumed worker read the saved modules, report, current node and dependency
records, resolved stage-1 repair note, and current blueprint unit Steps 2–3 and
`pur713-def-lower-shriek-module`. The repair note is resolved and concerns stage 1;
the current reviewed proof follows ordinary derived system categories.

The saved `IsShiftCoherent` body was a diagnostic `True`, contradicting the
reported and required shift clause. Restored the saved explicit condition: the
inherited integral and tensor-localized shifts, integral triangulatedness, shift
compatibility of the two reduction/limit counits, limit presentation, alpha, the
two realization scalar extensions and a, and equality of localized integral
shift components. This changes no mathematical node statement. Condensed
refinement arrows were checked to have the bounded-constructible full category
as their actual domain, for both finite and closure coefficients.

For compiler performance, the rationalized square is now the named predicate
`IsFiniteRationalSquare`, and `ComparisonFamilyCore` holds the comparison data.
`IsScalarIdentity`, `IsScalarComposition` and `IsScalarRefinement` contain the
original quantified equations verbatim; `ComparisonFamily` extends the core with
these same three requirements. These are packaging helpers of this node, not
additional mathematical assumptions or independent notions. `rationalSupport`
also has an explicit source and target using the recorded rational category.

The scalar-presentation comparison now reuses `purScalarModel` from
Sheaf.Paper.CompletedCoefficientPresentationTransport and the published
`OperationScalarTransport` record from Sheaf.Paper.BasicOperationsCoefficientReduction.
Its ordinary tensor-section and universal derived-counit fields determine both
isomorphisms uniquely. The named existence and subsingleton statements expose
this fact; no arbitrary natural isomorphism is selected. The scalar presentation
is the composite of the published comparison and this normalized transport.
The earlier duplicate section/derived-normalization interface was removed.
The two already landed owning nodes are added to statement dependencies. A
read-only dependency traversal checked that neither addition closes a cycle.

## Repair after resumed dry run

The saved packet's dry run timed out while precompiling the unrelated
`Sheaf.Paper.CoefficientSystemDerivedComparison` side overlay. The principal
module imported `Sheaf.Paper.CompletedCoefficientPushforwardComparison` only to
remove two instances, and did not use any declaration from that module. I
removed that unused import and the two corresponding attribute commands; all
compact-support declarations and their recorded signatures are unchanged. The
main module is being rechecked with the required `scompile.py` wrapper.

## Current-source universe repair

The resumed dry run compiled the projection, semilinear transport and realization
modules individually. Its initial local pass encountered a missing published
`CompactSupportFiniteAction.olean`; automatic server confirmation rebuilt the
current source closure and reached the main file. That confirmation diagnosed
unconstrained coefficient/module universes in the inferred result of
`moduleEncoding` and its derived abbreviation, followed by downstream errors and
the file timeout. Both constructions now have explicit source and target types:
the archived internal modules and the existing `pbcModules` category, and their
respective recorded derived categories. No site universe is identified with its
morphism universe, and no new mathematical hypothesis, map or comparison is added.
The packet is being recompiled through the prescribed wrapper after this repair.
The subsequent diagnostic identifies the imported
`WeilConjectures.IntegralHom.derivedCategory` instance: its coefficient universe
occurs only under `max`, so instance search leaves that universe undetermined for
the fixed `pbcModules` category. Its instance registration is disabled in the main
module, retaining the category's existing standard localization. This also avoids
the same ambiguity when elaborating the ambient triangulated-functor field.
The first error-free timing pass isolated about 27 seconds in
`integralReductionScalar`. Its construction now explicitly uses the published
`pbcIntegralScalarInclusionIso` and groups the two ambient comparisons before
whiskering by the integral inclusion. This is the same canonical composite;
the inherited dimension and invertibility witnesses are supplied as `Fact`
instances solely for the published inclusion API. No file is split and the
60-second limit is unchanged.

## Current resumed compilation

The prescribed resumed dry run compiled the three supporting modules cleanly,
but the main module reached the 60-second limit, including server confirmation.
A scoped transparency setting is being checked on `integralReductionScalar`: both
`backward.isDefEq.respectTransparency` options are true for that definition only.
Its construction, signature and every recorded mathematical statement are unchanged.
The previous timing trace assigns 26.734 seconds to this comparison.
The follow-up wrapper run encountered a missing published
`Sheaf.Paper.AdicCoefficientDatum.olean` while recompiling the unrelated
`Sheaf.Paper.ExceptionalCoefficientComparison` overlay; its automatic current-source
confirmation reached the main module and again timed out after 60 seconds.
The scoped setting alone is therefore insufficient; an import-only diagnostic is
now checking the cost before statement elaboration. No tool or published library
source was modified.

The canonical composition now passes its ten intermediate functors explicitly to
`pasteReductionComparison`, a generic composition of its existing inclusion,
coefficient-presentation and reduction isomorphisms. This helper has actual
composition data and is listed in the owning node's `lean.declarations`; no new
mathematical notion, hypothesis or comparison is introduced. A diagnostic copy
with the built-in elaboration profiler is checking the same module body.

## Current dependency interface self-check

Compared the saved dependency repair with the full current published module.
The final dependency module differs from that source only in the explicit result
type of `moduleEncoding`. In particular all bundled-base declarations and the
chosen-adjoint and mate normalizations of the current `Data` and `Exchange`
records are retained. The main item uses its same `Base`, `At`, `Data`, integral
and rational categories, realization and scalar-extension normalizations. Its
main mathematical statement and its hypothesis/clause correspondence are unchanged.
The two diagnostics using the obsolete dependency replacement were stopped; the
prescribed dry run now checks the complete current packet.

## Timeout repair

The first resumed gate timed out while elaborating the original `IsShiftCoherent`
definition in the principal module. Its six shift witnesses and all nine compatibility
clauses are unchanged. To reduce one giant elaboration term, the exact conjunction is
now `shiftCoherentClauses`, and `ShiftCoherentWitness` stores the same six witnesses
and clause; `IsShiftCoherent` is their `Nonempty`. This is propositionally the same
witness-and-clause statement and introduces no hypothesis or postponed data. The two
helper declarations are recorded in the node's `lean.declarations`.


## Maintenance handoff 2026-10-18 (NC, ten deadline failures)

Maintenance independently reproduced the published dependency failure in
`Sheaf.Paper.CoefficientRingedSequenceSite`, then the same failure in
`Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`. The generic high-priority
`CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall` instance
requires a successor coefficient universe, which instance search cannot infer
from `max u (t + 1)`. Both server modules now disable that instance after their
options; existing coefficient-universe sheafification supplies the required
instances. The sequence-site module passes in 6.2 s; the consumer's scratch
check passes in 44.4 s, with its final published-path check underway. No
mathematical declaration, universe, hypothesis or docstring was changed.

Use the current server source via `scompile.py --source` if a shared copy lags.
Do not add copies of these two dependencies to this packet merely to repair
this diagnosed instance-selection failure. Continue the required dry run on
the saved packet and use its fresh diagnostic. Earlier main-module timeouts
and the item's remaining statement work remain distinct from this dependency
repair. The durable server handoff is
`coord/maintenance/NC-lem-pur-compact-support-condensed-realization.md`; the
maintenance report and final commit are recorded at
`/home/ubuntu/weil-launcher-all/maint/NC-lem-pur-compact-support-condensed-realization-1792319639/REPORT.md`.

Maintenance validation completed: the published consumer passes in 46.4 s.
Both dependency source repairs are in server commit
`66a202455b2663b759f3938417d6abbafba3f41c`; the durable maintenance handoff
is committed at `dc7591f5f2afdc94d53810fedd93d9089fbc70b4`. The concurrent
import-restoration job included the two source edits in the former commit;
maintenance verified their exact diffs and committed its handoff separately
under the required merge lock. See the maintenance REPORT.md for evidence.


## Current packet repair

The initial resumed dry run was started on all nine saved modules. A parallel
source check through `scompile.py --source` found that four saved dependency
copies are already published unchanged (apart from the ordering of one instance
attribute). They are archived under scratch and omitted from delivery:
CoefficientRingedSequenceSite, SemilinearSystemModels,
NormalizedConstructibleTowerLocalEffectivity and PbcUniformCompleteTriangulated.
The saved BasicOperationsCoefficientReduction replacement contained only the
OperationScalarTransport structure and omitted its owning node's theorem.
The complete published module already supplies this identical structure and its
normalizations, so its obsolete replacement and node repair are also archived.
The item imports the complete published module. The returned-review repair below
replaces the theorem dependency with a definition node owning its scalar-transport datum. Only CondensedERealization remains a dependency repair.

The saved shift clause incorrectly attempted to infer proofs of its conjuncts
while defining the proposition, then used those proof terms as propositions.
Its eight named conjuncts are now explicitly Prop-valued aliases of the same
triangulation and natural-transformation shift conditions. The ninth condition
is the unchanged equality with the rationalized integral shift. The same six
shift witnesses are quantified by ShiftCoherentWitness; no condition is assumed
or removed. Added the two missing helper docstrings. The earlier dry run was
stopped after this source check to avoid compiling obsolete replacement sources;
the repaired four-module packet is checked again below.


The current source comparison also found five restored public imports in the
published CondensedERealization module. Restored all five in the delivered
dependency repair. Against the current published source its sole remaining
difference is the explicit result type of moduleEncoding. The ongoing dry run
uses its earlier immutable payload; the final gate will check this restored
source too. No declaration or dependency statement is changed.

## Resume against current sources

The required initial dry run was started on the saved four-module packet. A fresh
`scompile.py --source Sheaf.Paper.CondensedERealization` comparison found four
additional proof imports restored in the published dependency since the saved
packet. Restored those imports in the dependency repair too. Its only declaration
difference remains the explicit result type of `moduleEncoding`; all current
normalizations, hypotheses and comparison data are preserved. The final dry run
will check this refreshed file. The item statement is unchanged.


## Current dry-run diagnostics and repairs

The initial dry run of this resumed turn completed elaboration of the main module
in 32 seconds and reported concrete missing shift instances. The current archived
bounded-constructible module has removed the former unconditional triangulation
instance for arbitrary coefficient rings, as its recorded square-zero-ring
counterexample requires. Shift stability needs no such Serre assumption:
`fieldConstructible_shiftStable` states precisely the inherited shift closure of
the existing predicate, with cohomological reindexing as its complete proof plan.
It is a helper statement of this item and is listed in `lean.declarations`.

The shift record now explicitly includes the limit, coefficient-presentation,
whole-system support, and rationalization shift structures needed to type its
original counit, alpha, scalar-extension and realization compatibility conditions.
These are existential comparison data within the conclusion, not additional
hypotheses on schemes, coefficients, complexes or compactifications. The integral
and rational shifts, all eight natural-transformation/triangulation conditions,
and the localized integral-shift equation remain. The encoding equivalence uses
both recorded additivity fields; its derived functor uses the existing termwise
derived shift instance. The system-support composite is unfolded locally only
when synthesizing its composite shift.

The dry run also exposed two omitted explicit predicate arguments to
`ObjectProperty.isoMk` in the tensor associator and unit lifts. Those constructors
now receive their actual predicate and objects. The system refinement construction
has explicit types for its open-unit transpose, proper compositor and whiskered
maps, retaining the same ordered canonical composition. No node statement or
mathematical construction is replaced. Every single-file wrapper run keeps the
60-second limit.

A fresh published-source comparison confirms that the dependency repair
`CondensedERealization.lean` still differs only in the explicit result type of
`moduleEncoding`. All current imports and every declaration are retained.

## Refinement elaboration repair, 2026-10-19

The required initial dry run reported one application type mismatch in
`systemRefinement`; all three supporting modules compiled cleanly. The main
module made `integralCoefficientCommRingSheaf` locally irreducible for elaboration
performance. This prevented the final refinement composite from identifying the
recorded coefficient-system category with the generic ringed-system presentation
used by `SemilinearProperOpen`. Its definition is now semireducible only around
this construction and is made irreducible again immediately afterward.
`pasteRefinement` performs the same whiskering, associator and proper-compositor
composition with explicit abstract functors. It contains actual composition data
and is recorded among this item's declarations. No mathematical statement,
hypothesis, coefficient ring, canonical map, or comparison order changes.

A current `scompile.py --source Sheaf.Paper.CondensedERealization` comparison
confirms that the dependency replacement differs from the published source only
in the explicit result type of `moduleEncoding`. The source and target remain
the archived internal modules and the existing `pbcModules` category.

The resumed self-reading checked the current node and blueprint Steps 2–3,
the archived lower-shriek definition, and the four delivered modules. The support
remains exact open extension followed by separately derived proper direct image;
alpha is the actual reduction/limit counit; the scalar square is a whole-system
equality; the rationalized square uses the actual coefficient projection;
closure coefficients retain the finite-subfield-valued subring. The final shift
record explicitly carries thirteen constituent shift structures and the original
eight triangulation/natural-transformation clauses plus the localized integral
shift equation. Identity/tower and refinement equations remain the canonical
tensor and proper/open mate equations. The empty scheme, zero complex, first
positive quotient, identity embedding, ramified extensions and identity/composite
refinements remain included. No statement correction is required.


## Provider-interruption resume

Checked the interrupted gate's completed result before invoking another gate: no
commit was pushed; all three supporting modules passed, and the main module timed
out. The required fresh dry run reproduced that timeout. A saved focused trace
located repeated category unfolding in the naturality proof of integralRefinement.
The same full-subcategory restriction is now constructed by liftSupportTransformation,
a generic actual lift with the identical underlying components and naturality.
This is a packaging helper of the item; the specified refinement map and all
mathematical statements remain unchanged. The first wrapper check with this helper
passed the sandbox main module in 53 seconds, then timed out at the library path;
its two unused implicit naturality-binder warnings were removed. Further checking
retains the prescribed 60-second limit and all coefficient/site universes.


## Final validation, 2026-10-19

The prescribed deliver2.py --no-push gate returned OK for commit 7f536c2694:
all four delivered modules compile and the maintainer preflight passes. The local
main-file deadline triggered current-server confirmation; that confirmation
accepted the unchanged 60-second-per-file packet. No diagnostic profiler or trace
option is present in a delivered module; the auxiliary lift's implicit binders no
longer generate warnings. The final node records include the lift helper and
verbatim principal signatures with the current UTC date.

The final self-reading compared the source's compact-support composite with the
recorded strict-system, completed and condensed constructions. Every main clause
remains as mapped above: exact R-linear completed support, the full-system alpha
counit, rational realization, finite and finite-valued closure projection, completed
integral scalar compatibility, and morphism/shift/identity/tower/refinement
coherence. The generic lift changes only elaboration of the same natural map.
Metadata and statement signatures, allowed node-field changes, explicit implicit
variables, line widths and removal of diagnostic commands were checked again.

## Returned review L repaired, 2026-10-19

The return on immutable head 695e0022fc9e identified that the item imported
`BasicOperationsCoefficientReduction` only for its plain
`OperationScalarTransport` structure, while citing the unrelated existence and
basic-operations theorem node `lem-fix-operation-reduction`. Added
`def-pur-operation-scalar-transport`, with `existing: true` on that exact unchanged
published structure, and replaced the theorem dependency by the new definition
node in the item's `stmt_deps`. The item's own `scalarModelTransport_nonempty`
and `scalarModelTransport_subsingleton` continue to supply its existence and
uniqueness obligations. No Lean module or natural-language statement changes.

The resumed initial dry run passed as a244e532ea before this metadata repair.
The self-reading of the new node matches prime/field/finite-extension/embedding
and scheme binders to the full published signature; `ordinary` and `derived`
are the two comparison isomorphisms, `tensor` quantifies over every module, test
object and pure tensor, and `counit` quantifies over every cochain complex. Identity
embeddings, zero modules/complexes and empty schemes are included. The datum
requires no noetherianity or constructibility hypothesis and adds no existence
claim. The scalar model's `.some` still uses the item's own uniquely normalized
theorem. The projection-isomorphism and shift-stability clauses remain separate
helper theorems, as noted in the return. This is the required author self-reading;
the dispatcher forbids delegation. All other independently accepted clauses and
the four Lean modules are retained byte for byte.


## Final resumed source self-check, 2026-10-19

The saved scalar-transport repair is retained: the new definition node owns the
unchanged published structure through `existing: true`, and the item cites that
node instead of `lem-fix-operation-reduction`. Its recorded signature is verbatim;
its six cited definition dependencies match the statement. The ordinary and
derived isomorphisms, every pure tensor, and every complex counit are precisely
the four published fields. No existence or uniqueness claim is added to this node.

The required current-source comparison found a subsequently landed proof of
`fieldUpperStar_isLeftAdjoint` and its helper declarations/imports in
`CondensedERealization`. Rebased this dependency replacement onto the source read
with `scompile.py --source`, preserving that proof and every current declaration
and import. Its sole difference from current published Lean is again the explicit
source/target type of `moduleEncoding`; no theorem body or statement changes.
The dependency node also retains the current non-lean metadata. The independently
accepted compact-support constructions and all other saved Lean modules are
unchanged. The final gate below checks this rebased source before push.


## Current dependency and final resumed validation

The required initial dry run compiled the saved modules, then preflight rejected
the realization replacement because the current base has a newly landed proof
of `fieldUpperStar_isLeftAdjoint` and four proved helpers. A standalone signature
check of the unchanged published `moduleEncoding` showed exactly the required
internal-module and section-module universes. The obsolete dependency replacement
and its node file are therefore omitted entirely. This is a three-module packet;
no consumer declaration needed a change. No live proof is replaced or restated.

`scompile.py` accepted every delivered module against the unchanged published
dependency: projection 31.8 seconds, semilinear transport 16.6 seconds, and main
comparison 49.4 seconds on current-server confirmation, with no errors or warnings.
The scalar-transport definition node, its exact recorded signature, the replacement
of the unrelated theorem dependency, and the edge-case self-check are retained.
No Lean dependency replacement module remains. The final dry run checks this reduced packet.

The final reduced packet passed `deliver2.py --no-push`: commit `5a7bcc614a`
passed maintainer preflight and all compiler checks. The self-check confirms the
requested owning definition node and removed theorem dependency, three unchanged
compact-support modules, no dependency replacement, and no statement correction.
