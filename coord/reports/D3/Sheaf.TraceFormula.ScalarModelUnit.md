## What changed

Filled the proof of `WeilConjectures.scalarModelUnit`, preserving its entire signature
and all three original public imports. Added proof imports of the coherent primitive
reduction presentation, K-flat resolutions, good-complex localization, and two new
auxiliary modules: `Sheaf.TraceFormula.RoosAdjunctionTranspose` and
`Sheaf.TraceFormula.ScalarIdentityRoosAugmentation`. Updated the item's proof plan and
proof dependencies to describe the actual argument. The representative calculation
is a proved private theorem, separate from the final naturality argument.

The proof uses one coherent strict presentation throughout. It extends the system
scalar-unit formula to arbitrary complexes by a K-flat resolution, computes the
whole constant/limit adjunct in the Roos model, and identifies both cone coordinates
with the specified scalar identity augmentation. Postcomposing with an invertible
normalization factor reduces the result to the finite-free comparison formula.
Essential surjectivity of the good-complex localization and naturality give the
formula on every derived object.

## Proved and sorry left

Closed the original single hole in `WeilConjectures.scalarModelUnit`
(node `lem-trf-scalar-model-unit`). Added zero holes; split off zero holes.
There are no remaining `sorry` declarations in the delivery. The two new public
theorems `WeilConjectures.integralComparisonRoosTranspose` and
`WeilConjectures.scalarIdentityRoosAugmentation`, including all their private helpers,
are fully proved.

The final main module compiles without warnings in 26.1 seconds. Both auxiliary
modules compile without warnings (55.9 and 45.0 seconds). The unchanged direct
consumer `Sheaf.TraceFormula.CounitRealizationSubstitution` also compiled against
the proved theorem in 60.5 seconds during the compatibility probe; it is not part
of this delivery. Its temporary sandbox copy was removed. The final item preserves
all original public imports verbatim and changes no existing public interface.

No existing definition, instance, theorem signature, public import, or public attribute
was changed. The proof uses local irreducibility controls and default transparency;
the old transparency overrides were removed. All profiling options were removed.

## No longer needed

No existing module is withdrawn. The three original public imports retain the
statement's definitions and their existing public re-exports. All added proof imports
are used.

The following planned direct proof dependencies are unnecessary for this argument:

- `lem-trf-integral-cone-counit-realization`: the new strict Roos-adjunction formula
  computes the entire adjunct directly, including its shifted cone coordinate.
- `lem-pur-quotient-scalar-comparison-descent`: the scalar identity is checked on
  strict compatible families using the two explicit Roos coordinates.
- `lem-pur-derived-change-of-rings`: transport to an arbitrary object uses the
  existing good-complex localization and naturality instead.
- `lem-coef-derived-system-evaluation-calculus` remains a statement dependency but
  is not used as a separate proof step: the already proved coherent primitive
  presentation provides the stronger whole-tower equation needed here.

These are removals from this item's planned proof dependencies, not claims that the
corresponding library modules are globally unused. In particular all source-library
declarations and their imports remain present.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or definition repair was needed. The original plan mentions
finite unit projections followed by an appeal to a cone counit. The existing proved
`coherentPrimitiveReductionPresentation` already supplies the whole-tower coherence,
so no faithfulness of derived finite projections is required. The auxiliary proof
reuses the proved private `derived_transpose_ordinary` lemma from that module and the
proved two-coordinate Roos-map formulas from `IntegralAmbientOperationModels`.
The existing `coefficientConstantTowerRoosComparison` concerns a different strict
Roos model and supplies projection equations; it does not compute the full adjunct
for the specified arbitrary normalized realization model.

The newest blueprint unit `sk-thm-trace-transport` and its six steps are preserved.
The historical ancestor recorded by the item is `prop-trf-karoubi-independence`; the
new nodes retain this recorded origin through the item. The ancestor command returns
`None` because the item's `created.item` is a Lean module name, rather than a node id.
The search found no existing blueprint statement of either auxiliary formula.

## New nodes

`lem-trf-roos-adjunction-transpose`, in
`dag/nodes/sec-trace-formula/lem-trf-roos-adjunction-transpose.json`, records the
normalized derived constant/limit adjunct of an arbitrary strict compatible family.
It has no scalar realization model or scalar comparison in its statement. Its proof
uses the ordinary derived adjunction formula, naturality of the limit-to-Roos map,
and a K-injective resolution. The source is Stacks 0941,
`sites-cohomology.tex`, `lemma-derived-limit-is-ok` and its preceding discussion
in `section-derived-limits`.

`lem-trf-scalar-identity-roos-augmentation`, in
`dag/nodes/sec-trace-formula/lem-trf-scalar-identity-roos-augmentation.json`, records
only the strict chain-level tensor-unit calculation. It has no derived calculus or
realization model in its statement. The proof computes multiplication's inverse as
insertion of one and checks the unshifted and shifted cone coordinates separately.
Its sources are Bhatt--Scholze Definition 3.4.10 and Stacks 0941. Both formulas include
zero complexes and require neither completeness nor boundedness.

No change record is needed: no definition, statement or existing public interface
changes. No other existing module or node is changed.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
