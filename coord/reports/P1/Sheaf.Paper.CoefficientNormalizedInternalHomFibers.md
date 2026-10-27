## What changed

Filled `WeilConjectures.coefficientNormalizedInternalHomFibers` without changing its
signature, the existing structures, or any public import. The proof now contains
complete private calculations for closed transposes, internal composition, the
mate of a tensor projection, and horizontal transition naturality. It constructs
the actual evaluation adjunction using the singleton derived extension, rather
than comparing a second independently chosen internal-Hom package.

Added three proof imports with tensor-only obligations in their own modules:
`Sheaf.Paper.CoefficientNormalizedTensorAssociativity`,
`Sheaf.Paper.CoefficientNormalizedEvaluationProjection`, and
`Sheaf.Paper.CoefficientNormalizedTensorHorizontal`. Additional proof imports give
the semilinear definitions, singleton extension, sequence evaluation and derived
exact-functor comparisons. The generic categorical calculations follow the proved
private arguments in `RingedPullbackHomEvaluationComparison`,
`SemilinearCartesianHomEvaluation`, and `SemilinearSystemsExistence`, specialized
here to the specified coefficient structures. None of those aggregate theorems
is assumed in the new parent proof.

Updated the item's DAG proof to match this tensor-first argument. Added nodes for
the three remaining model calculations, including their sources, complete proofs
in words, actual LeanSearch/LeanFinder/Loogle/grep searches, and Lean statements.
No other existing module or node is changed. No source-library declaration is
removed or changed.

## Proved and sorry left

This is a decomposition, not a completed axiom-free proof: one original hole is
closed and three strictly narrower tensor holes are added (net -2 holes closed).

Closed: `WeilConjectures.coefficientNormalizedInternalHomFibers`
(`lem-coef-normalized-internal-hom-fibers`). Its module has zero remaining `sorry`.
Its combining proof and every private helper are complete.

Added, each with proof exactly `:= by sorry` in a separate module:

- `WeilConjectures.coefficientNormalizedTensorAssociativity`
  (`lem-coef-normalized-tensor-associativity`): associativity of the fixed reduction
  and finite tensor comparisons. No internal Hom, fiber isomorphism or transition
  assertion occurs in its conclusion.
- `WeilConjectures.coefficientNormalizedEvaluationProjection`
  (`lem-coef-normalized-evaluation-projection`): invertibility of the unit-defined
  finite-prefix tensor projection on one normalized system. It does not construct
  internal Hom or assert a Hom transition formula.
- `WeilConjectures.coefficientNormalizedTensorHorizontal`
  (`lem-coef-normalized-tensor-horizontal`): the tensor horizontal equation for
  arbitrary systems, before normalization or internal Hom.

These are all the holes in this delivery. No definition has a hole. The parent
constructs the fiber maps from the invertible mate, so its choice is determined
by the evaluated closed adjunction and its evaluation equation. The tensor
lemmas assert properties, not existence of arbitrary data.

The final all-files compile passed: the parent took 11.6 seconds and the new
modules took 2.1, 2.2 and 2.1 seconds. There were no compiler warnings. Delivery
checks provide the remaining mechanical validation. Edge-case
checks for the new assertions include index zero (a positive coefficient
quotient), equal transition indices, zero arguments and the empty site. The
formulas use actual derived quotient extension and do not assume quotient rings
are flat. The associativity proof plan uses strict system representatives before
localization and does not infer equality from finite derived evaluations.

## No longer needed

No original import is removed: the original public import
`Sheaf.Paper.CoefficientNormalizedReductionModels` remains necessary for the
unchanged public definitions and theorem statement. No module is withdrawn.

The parent no longer needs the following original aggregate proof dependencies:

- `lem-coef-semilinear-derived-sections`
  (`Sheaf.Paper.SemilinearDerivedSections`): a second complete semilinear calculus
  and comparison of its internal-Hom choices are unnecessary. Only tensor
  projection and tensor horizontal compatibility remain as model obligations.
- `lem-pur-system-level-left-extension`
  (`Sheaf.CategoryTheory.SystemLevelLeftExtension`): the full level-extension
  theory is replaced by the narrower scalar-model, tensor-coherence and singleton
  derived-extension declarations, with the adjunction transported explicitly.
- `lem-coef-ringed-pullback-hom-evaluation-comparison`
  (`Sheaf.Paper.RingedPullbackHomEvaluationComparison`): internal composition is
  proved directly by uncurrying and tensor associativity. A general ringed
  pullback-Hom package and comparisons of its fixed models are unnecessary here.

These are dependencies pruned from this node's proof, not claims that their
modules are globally unreachable. Their other consumers and public declarations
are preserved. Underlying tensor theory may still be reached through the three
new tensor nodes. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan correctly identifies the mathematics, but its aggregate
semilinear and ringed-Hom existence theorems do not directly supply the equations
for the particular R and Q fixed in this theorem. They would require substantial
comparison of separately selected scalar adjunctions and internal-Hom choices.
The new proof isolates exactly the tensor normalizations that matter, and proves
all the closed-category consequences explicitly. No false statement or broken
tool was found. No target statement, coefficient definition or normalization
hypothesis was weakened.

The current queue row assigns an ordinary proof item; no rework row or build-error
file exists in the shared snapshot. The item source is present and preserved.
The latest blueprint's General Verdier biduality unit was read; its route is kept.
Blueprint searches for tensor projection, normalized internal Hom and tensor
associativity found no node stating any of the three fixed-model obligations.

## New nodes

`lem-coef-normalized-tensor-associativity` states only associativity for the two
fixed tensor comparisons, with the strict representative argument required for
system-map equality. Its source is Stacks 07A4 together with the supplied signed
total-tensor associator models. Its Lean module is
`Sheaf.Paper.CoefficientNormalizedTensorAssociativity`.

`lem-coef-normalized-evaluation-projection` states only the finite-prefix tensor
projection isomorphism. Its proof plan identifies actual normalized models with
the existing semilinear projection inputs, then uses unit-compatible uniqueness
of left adjoints. Its sources are Zheng Construction 4.1 and Proposition 4.17(a),
and Stacks 07A4. Its Lean module is
`Sheaf.Paper.CoefficientNormalizedEvaluationProjection`.

`lem-coef-normalized-tensor-horizontal` states the tensor horizontal equality for
the actual transition adjoints. Its proof plan uses ordinary pure tensors,
Q.ordinary_unit, Q.unit_model, hE and Q.tensor_model, before closed transposition.
Its sources are Zheng Construction 4.1 and Proposition 4.17(a), and Stacks 03EK,
06YY and 07A4. Its Lean module is
`Sheaf.Paper.CoefficientNormalizedTensorHorizontal`.

No change record is required: only the assigned existing module and its own DAG
proof, together with new modules and their nodes, are changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CoefficientNormalizedEvaluationProjection": "34f0ec008c98797a3ad464d2173ca4038795610f", "Sheaf.Paper.CoefficientNormalizedInternalHomFibers": "994982a3a46b89f721d899afa62ebedec60c9b4b", "Sheaf.Paper.CoefficientNormalizedTensorAssociativity": "d95f0a893484737eff17c5b59ba4924e09556d0c", "Sheaf.Paper.CoefficientNormalizedTensorHorizontal": "565525ba4b2ce8273372364ac480f8b6ee696116"}, "results": {"Sheaf.Paper.CoefficientDerivedSystemResolutionModels": {"hash": "bb15ec923973679cc0f78d186dfa0bb723fce70c", "status": "OK"}}, "seconds": 31, "time": "2026-10-28T05:19:46+0800", "transitive": 0, "version": 1}
```

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
