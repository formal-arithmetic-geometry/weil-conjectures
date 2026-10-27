## What changed

Partial proof delivery for `Sheaf.Paper.TensorHomCoefficientTransposes`.
All public declarations and definitions retain their signatures and bodies, except
for the four theorem proofs listed below. No other module is changed.

The specialization `tensorHomCoefficientTransposes` applies the existing
`coefficient_square`. For localization, the proved private helper
`integralHomEquiv_postcompose` uses test-object naturality from
`PodHomChain.counit_formula` to identify the integral chain with postcomposition
by the existing `integralGammaIso.hom`. Mathlib `Linear.homCongr` and
`LinearEquiv.baseChange` then supply the integral, localized and E-linear
bijections. A second proved private helper, `baseChange_postcompose`, uses tensor
induction and `ScalarLocalization.composition_tmul` to prove the forward and
inverse representative formulas. Expanding `rationalGamma` gives its prescribed
pure-tensor formula.

The two transparency options formerly set to false are set to true. Local
irreducibility for the common Gamma definitions avoids expanding their large
constructions when checking the subsequent statement types. Six unused
private proof imports are removed; every public import is preserved. The node's
step 7 and proof dependency list record the shorter implemented localization
route while retaining the plans for the unchanged holes.

Validation: the localization proofs were checked in a focused compilation.
The complete delivery module compiled successfully through lcompile.py in 58.1 s
(exit code 0). The delivery tool runs the remaining preflight checks. No new
module or definition is introduced.

## Proved and sorry left

Four of the original twelve holes are closed, all in namespace
`WeilConjectures.TensorHomCoefficientTransposes`:

- `tensorHomCoefficientTransposes`
- `localized_bijection`
- `localized_representatives`
- `rationalGamma_formula`

Zero holes are added and zero statements are split off. This is a proof from
existing declarations, including the existing unfinished chain-naturality and
representing-isomorphism laws, rather than a claim that their dependencies have
been proved in this delivery.

Eight existing holes remain verbatim in the same namespace, each belonging to
node `lem-sf-tensor-hom-coefficient-transposes`:

- `coefficient_square`
- `successive_square`
- `common_stage_bijection`
- `common_stage_representatives`
- `common_stage_postcomposition`
- `equations_pass_to_fields`
- `shift_equations_pass_to_fields`
- `field_coefficient_square`

Both new private helpers are proved. There are no holes in definitions.

## No longer needed

The following private proof imports are unused by the implemented proofs and
removed from the item module:

- `Sheaf.Paper.BasicOperationsCoefficientReduction`
- `Sheaf.CategoryTheory.EvaluationTransposeCoherence`
- `Sheaf.Paper.IntegralHomReduction`
- `Sheaf.Paper.ScalarCompletionAssociator`
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`
- `Sheaf.CategoryTheory.SemilinearScalarLocalization`

The localization proof does not need the planned direct-sum proof of additivity:
postcomposition with the existing representing isomorphism is already a linear
isomorphism. The six removed modules' nodes remain dependencies of the plans for
unchanged holes, so this delivery does not withdraw any node or module or claim
they are unnecessary throughout the target closure. No source-library declaration
is removed.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or changed. Step 7's direct-sum linearity argument is
longer than necessary given the existing canonical representative construction;
test-object naturality and `Linear.homCongr` suffice. The unit's stated route is
preserved. The remaining coefficient and common-stage assertions are unfinished,
not replaced by weaker statements or renamed holes.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
