## What changed

The target theorem now assembles two strictly smaller comparison packages. Added
`AdicModuleTensorComparisonCore` for tensor naturality and pure-tensor normalization,
and `AdicModuleHomComparisonCore` for Hom naturality, identity-slice evaluation, and
bidual sections. The target constructor obtains both packages and fills the seven
fields of `AdicModuleTensorHomComparison`. The two universal-property packages remain
named public theorems with source and proof descriptions, each in its own module.

## Proved and sorry left

Closed `AlgebraicGeometry.ProEtale.adicModuleTensorHomComparison` by a complete
constructor assembly. Added the strictly simpler split obligations
`AlgebraicGeometry.ProEtale.adicModuleTensorComparisonCore` and
`AlgebraicGeometry.ProEtale.adicModuleHomComparisonCore`, each still containing its
single named `sorry` and each recorded as a new DAG node. No definitions contain
`sorry`.

## No longer needed

The original target proof dependencies for the universal-property constructions are
no longer imported directly by the target proof. They remain the proof dependencies
of the two split nodes. No existing mathematical node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The target structure combines two independent universal-property arguments. Treating
it as one indivisible obligation obscures the tensor/Hom boundary. The two records are
strictly smaller: the tensor record has three fields, and the Hom record has four
fields, while the target has all seven. The target statement and all existing field
signatures are unchanged.

## New nodes

`lem-sf-adic-module-tensor-comparison-core` records the tensor comparison package and
its universal-property proof obligation; its Lean declaration is
`AdicModuleTensorComparisonCore` and theorem
`adicModuleTensorComparisonCore` in
`lean/Sheaf/SixFunctors/AdicModuleTensorComparisonCore.lean`.

`lem-sf-adic-module-hom-comparison-core` records the Hom, evaluation, and bidual
comparison package and its currying proof obligation; its Lean declaration is
`AdicModuleHomComparisonCore` and theorem `adicModuleHomComparisonCore` in
`lean/Sheaf/SixFunctors/AdicModuleHomComparisonCore.lean`.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
