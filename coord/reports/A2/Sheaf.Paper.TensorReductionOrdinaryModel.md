## What changed

Replaced the body of `WeilConjectures.tensorReduction_ordinaryModel` with a complete
assembly proof from the two original steps, keeping its signature, docstring and
public imports unchanged. The new proof imports
`Sheaf.Paper.TensorReductionStrictDerivedSquare` and
`Sheaf.Paper.TensorReductionStrictFiniteEquation` privately.

Added `Sheaf.CategoryTheory.SequenceComplexHomAssembly`. It reuses the existing
additive vertical-evaluation instance from
`Sheaf.CategoryTheory.SystemEvaluationTopos` and proves unique assembly of a
compatible family of finite chain maps, using the existing strict-system
equivalence. The proof lifts degree maps through a fully faithful equivalence and
verifies the differential and uniqueness equations componentwise.

Returned-delivery repair: removed the duplicate declaration
`SheafOfModules.systemSequenceEvaluationAdditive`; no replacement name is added.
The support module publicly imports `SystemEvaluationTopos` because its existing
additive instance is needed to form the mapped-complex types in the statement.
The support node now lists only the assembly theorem and records this dependency.

Added `Sheaf.Paper.TensorReductionFiniteComponents`. Its finite component is the
explicit composite of the inverse ordinary reduction/evaluation comparison,
`coefficientScalarTensorIso`, the tensor of the two forward reduction/evaluation
comparisons, and the inverse tensor/evaluation comparison.

Added `Sheaf.Paper.TensorReductionEvaluationIdentification`, which proves that generic
and canonical evaluations agree and carries that equality to complexes. Its
`tensorReductionLiteralEvaluation` abbreviation fixes the native module universe
explicitly before the equality and zero-map proofs are elaborated. Three proved
instances specialize the existing site smallness, sheafification and locally
bijective constructions to that exact universe, avoiding unconstrained maximum
universes in instance search. Added
`Sheaf.Paper.TensorReductionStrictComparison`, which uniquely assembles compatible
components and proves their equation in the canonical evaluation convention.
The mapped evaluation isomorphism has one shared irreducible definition with an
explicit finite-component equation, avoiding repeated unfolding of its large
transport term during the component proof. The finite component maps and strict
map have explicit short source/target types.
`TensorReductionFiniteComponentEquation` and `TensorReductionStrictFiniteEquation`
hold the proved transport equation and finite normalization separately: profiling
showed repeated checking of these equations dominated the two larger files, after
the evaluation transport had already been made irreducible.
Three private, proved category lemmas perform conjugation, tensor-comparison
cancellation, and final model-isomorphism cancellation abstractly.
`tensorReductionStrictMap` is chosen from a proved unique-component
characterization, rather than from an undetermined existence assertion. Its data
are fixed up to equality; the postponed assertion is horizontal compatibility.

Added `Sheaf.Paper.TensorReductionStrictDerivedSquare` for the whole-system
localization square of this already fixed strict map. The item proof uses that
square and cancels the coherent tensor-model isomorphism. No existing shared
interface or other existing module was changed.

Validation: `lcompile.py --all` compiled all eight Lean files and accepted each
under the service's 60-second Lean limit. The displayed per-file service timings
also include preparation and cache work. A diagnostic pass confirmed the target
theorem takes about 9 seconds of kernel type checking. The temporary profiler
options were removed before delivery.

## Proved and sorry left

Original holes removed: 1, in
`WeilConjectures.tensorReduction_ordinaryModel`. New holes added: 2. This is a
**decomposition**, not a net proof gain (one closed minus two added = minus one).
The item module now contains zero `sorry` tokens.

The new holes, each a public theorem with its complete natural-language proof
and source in its docstring, are:

- `WeilConjectures.tensorReductionFiniteComponents_compatible`, node
  `lem-coef-tensor-reduction-finite-components`: the degreewise quotient-transition
  equation for the explicit finite maps. It concerns ordinary complexes only and
  has no K-flatness, derived comparison, or existential chain-map conclusion.
- `WeilConjectures.tensorReductionStrictMap_derived_square`, node
  `lem-coef-tensor-reduction-strict-derived-square`: the localization square for
  the uniquely fixed strict map. It has no map construction or finite-component
  conclusion.

Fully written proofs also include
`SheafOfModules.sequenceComplexHom_existsUnique`,
`WeilConjectures.tensorReduction_evaluation_eq`,
`WeilConjectures.tensorReductionSiteSmall`,
`WeilConjectures.tensorReductionAbSheafify`,
`WeilConjectures.tensorReductionAbLocallyBijective`,
`WeilConjectures.tensorReductionSystemEvaluation_zero`,
`WeilConjectures.tensorReductionSystemFiniteComponent_eq`,
`WeilConjectures.tensorReductionStrictMap_existsUnique`,
`WeilConjectures.tensorReductionStrictMap_component`, and
`WeilConjectures.tensorReductionStrictMap_finite`.
There are no holes in definitions, axioms, or arbitrary choices of a witness of
mere unproved existence. The two new obligations are independent parts of the
original two-step argument; the combination and chain-map assembly are actual
Lean proofs, rather than an application of a renamed original theorem.

## No longer needed

The duplicate additive instance from the rejected packet is no longer declared.
Its existing declaration in `SystemEvaluationTopos` is reused. The direct public
import of `SystemRingedSequenceSite` in the new assembly module is replaced by
`SystemEvaluationTopos`, which publicly reexports it.
No existing declaration, module, node, or planned dependency is withdrawn.
The original two dependency nodes remain needed for the comparisons in the
statements and the normalization obligations. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The rejected packet duplicated the existing additive evaluation instance from
`SystemEvaluationTopos`. The repaired packet imports that module and removes the
duplicate Lean declaration and its node attachment.

No statement correction is made. The DAG's first step did not expose the strict
horizontal compatibility needed to assemble its finite components. Its second
step also needs a whole-system normalization: equality after finite derived
evaluation is not used as a faithfulness principle. The delivery makes these
obligations explicit without weakening either clause of the original theorem.

Searched Mathlib and the adopted source library for scalar tensor comparisons,
fully faithful lifting, and derived-adjunction comparisons. The closest existing
project results are `IntegralTensorTransitionCompatibility` and the normalized
integral tensor tower: they handle finite scalar tensor maps in integral tower
models, and do not directly provide the transport to these fixed ordinary
coherent reduction models. The existing simultaneous derived normalization
likewise uses its own representatives. The report does not claim that these
existing holed declarations are obstacles; both remain available dependencies of
the stated normalization proofs.

## New nodes

`lem-coef-sequence-complex-hom-assembly`: the proved unique chain-map assembly
on a general ringed sequence site; uses the existing strict-system equivalence.

`lem-coef-tensor-reduction-evaluation-identification`: the proved identity of
canonical and literal evaluation, lifted once to an isomorphism of complex
functors. This is kept separate from the finite maps to avoid repeating its
coefficient transport during type checking.

`lem-coef-tensor-reduction-finite-components`: strict quotient compatibility of
explicit finite scalar tensor maps.

`lem-coef-tensor-reduction-strict-assembly`: unique assembly and evaluation
transport, both proved from the horizontal compatibility theorem and the general assembly
API. The finite tensor cancellation has its own proved node below.

`lem-coef-tensor-reduction-strict-derived-square`: the whole coherent derived
normalization square for the map fixed by finite components.


`lem-coef-tensor-reduction-finite-component-equation`: the proved definitional
transport equation, with the shared evaluation isomorphism kept folded.

`lem-coef-tensor-reduction-strict-finite-equation`: the proved finite scalar
tensor equation, obtained by cancelling comparison isomorphisms abstractly.

No change records are needed: no existing signature or definition was changed.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
