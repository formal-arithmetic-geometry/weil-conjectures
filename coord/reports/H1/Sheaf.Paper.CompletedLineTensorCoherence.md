## What changed

Filled `WeilConjectures.CompletedLineTensor.evaluation_existsUnique` and
`WeilConjectures.CompletedLineTensor.integralTwist_linear`, preserving their statements.

Evaluation is constructed from the actual Hom evaluation of each positive line power,
the braiding for negative powers, and multiplication for the zeroth power. The explicit
site tensor is compared with the monoidal tensor on pure sections. Reassociation and
evaluation give the cancellation natural isomorphism, and the trilinear universal property
proves its uniqueness. The constructions are locally irreducible after their section
formulas have been proved, to avoid repeatedly expanding sheafification comparisons.

Added the fully proved auxiliary modules
`Sheaf.Algebra.Category.ModuleCat.Sheaf.SignedLineEvaluation`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorCancellation` and
`Sheaf.Paper.ExactTensorCoefficientLinear`, and
`Sheaf.Paper.CompletedScalarIdentityUnit`. `SignedLineEvaluation` constructs the actual
native evaluation for the existing signed powers.
`SiteTensorCancellation` performs the general site-tensor
cancellation and uniqueness argument before specializing to concrete coefficients.
`ExactTensorCoefficientLinear` identifies the recorded constant-section action with the localized sheaf
action and proves linearity of any exact site tensor after deriving. The constructible
restriction then inherits linearity through its faithful inclusion. All additions to the
item's imports are proof imports. Existing statements, public imports and exported
instances are unchanged. `comparisonComplex` uses a local abstraction to avoid expensive
conversion of mapped composites; its value is definitionally equal to the previous
construction. The scalar-identity unitor construction is extracted into
`ordinaryUnitOnComplexes_exists`; `ordinaryUnit_existsUnique` retains the actual
good-complex uniqueness proof. This moves expensive cochain-model conversions into
a separate, fully proved module. The change record is
`coord/changes/completed-line-comparison-complex-elaboration.md`.
The unchanged point-normalization importer exceeded the file limit (68 seconds
against this delivery; 105 seconds against the published library). Its existing
model definitions and proved private auxiliary lemmas are extracted verbatim into
`Sheaf.Paper.PointEvaluationCompletionModels`. The original module publicly reexports
them and keeps its original final theorem statement and proof. Existing public
imports, declaration names, signatures, data bodies and attributes are retained.
The extraction separates kernel checking of the models from the final conjunction.
The unclaimed consumer `Sheaf.Paper.PointCompletedEvaluation` exceeded the limit
at 65 seconds; synchronous elaboration and a local sheafification-projection priority
are added there. Its statements, declaration bodies and exported attributes are unchanged.
Slice-site sheafification helpers are registered only
inside the evaluation proof section, so they do not affect later instance search.

## Proved and sorry left

Closed two of the ten original holes:

- `WeilConjectures.CompletedLineTensor.evaluation_existsUnique`
- `WeilConjectures.CompletedLineTensor.integralTwist_linear`

The added theorems `SheafOfModules.signedLineEvaluation_exists`,
`SheafOfModules.siteTensorCancellation` and `WeilConjectures.exactTensorCoefficientLinear`
have no holes. `WeilConjectures.CompletedLineTensor.ordinaryUnitOnComplexes_exists`
is also fully proved; it extracts an already proved construction and closes no additional
hole. `signedLinePairing` is a real construction with no postponed data.
The extracted `PointEvaluationCompletionModels` and the adapted
`PointEvaluationCompletionNormalization` have zero holes. Their already proved
statements are not additional hole closures. No new `sorry` is added and no obligation
is split off.

Eight original holes remain unchanged:

- `WeilConjectures.CompletedLineTensor.complete`
  (`lem-pur-signed-line-legacy-completeness`, also attached to the coherence node).
- `WeilConjectures.CompletedLineTensor.pairData_existsUnique`
- `WeilConjectures.CompletedLineTensor.associatorData_existsUnique`
- `WeilConjectures.CompletedLineTensor.beta_natural_evaluation`
- `WeilConjectures.CompletedLineTensor.scalar_coherence`
- `WeilConjectures.CompletedLineTensor.tower`
- `WeilConjectures.CompletedLineTensor.canonical_restriction`
- `WeilConjectures.CompletedLineTensor.rational_diagonal`

The last seven are attached to `lem-pur-completed-line-tensor-coherence`.
This is a partial proof delivery of a module with several holes.

Validation: the item, all four original auxiliary modules and the `rfl` comparison
compatibility check passed. All 21 unchanged direct importers passed. The extracted
point models, adapted point theorem and its sole direct importer are checked as well.
Temporary verification copies are removed before delivery.

## No longer needed

No original declaration, module or node is withdrawn. The point-normalization
module now obtains the completed-line, bounded-flat, total-tensor and tensor-colimit
proof dependencies through its extracted model module; these dependencies remain
needed and are not pruned. The native evaluation helper uses
`SignedLineScalarTensorTower.power_over_unit`, so it does not import the much larger
`OrdinaryLineDerivedScalarComparison` module just for a rank assertion; that node is
still retained for the untouched scalar-comparison obligations. The dependencies of
untouched proof obligations are retained. The new proofs use the existing ordinary-power
local trivialization theorem, the normalized Hom evaluation, the ordinary/site tensor comparison,
the trilinear universal property, and the recorded coefficient-action localization API.

## Where the brief, the DAG or earlier work was wrong

`Sheaf.Paper.IntegralLineTensorCompleteness` cannot be imported to prove this module's
`complete`: it already imports this module and invokes that very declaration. The
separate existing node `lem-pur-signed-line-legacy-completeness` records the outstanding
completeness obligation. This delivery leaves that obligation and its planned argument
unchanged; it does not count the circular route as a proof.

## New nodes

`lem-pur-exact-tensor-coefficient-linear` records the fully proved
`Sheaf.Paper.ExactTensorCoefficientLinear` auxiliary theorem. It separates scalar-action
localization from the constructible restriction and needs no rank-one or completeness
hypothesis. It adds zero holes and changes no existing coefficient-action interface.

`lem-pur-site-tensor-cancellation` records the fully proved
`Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorCancellation` theorem. It transports
a given pairing through the two tensor presentations and proves pure-section uniqueness.
It is strictly the cancellation part of the argument: it assumes the pairing and does not
construct the evaluation of signed powers. Generalizing the coefficient sheaf avoids
expensive repeated definitional checks in the item module. It adds zero holes.

`lem-pur-signed-line-native-evaluation` records
`Sheaf.Algebra.Category.ModuleCat.Sheaf.SignedLineEvaluation`, including its actual pairing
construction. Its fully proved theorem constructs the signed-power isomorphisms. It adds
zero holes and isolates the coefficient-independent Hom and braiding calculations.

`lem-pur-ordinary-scalar-unit-all-complexes` records the fully proved
`Sheaf.Paper.CompletedScalarIdentityUnit` construction. It supplies existence and the
normalization on every complex. The parent theorem combines this with its separate
uniqueness argument on the good-complex localization. This extraction adds zero holes
and preserves the previously proved ordinary unitor theorem.

`def-pod-point-evaluation-completion-models` records the existing point models and
proved auxiliary lemmas in their extracted module. The original point-normalization
node retains the final theorem and cites these models. This relocates existing
constructions without changing their formulas, statements or proof obligations.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
