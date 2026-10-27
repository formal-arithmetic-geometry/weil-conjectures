## What changed

Replaced the sole `sorry` in
`WeilConjectures.IntegralSystemRealization.integralOpenScalarUnitSquare`
by a categorical proof. The statement and its public imports are unchanged.
Added proof imports of `Sheaf.SixFunctors.ExactLocalizationInverseMate` and
`Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`.

Private proved helpers identify the scalar-pullback unit from the normalized
geometric Hom equation, interchange the scalar and open mate unit equations,
transport ordinary unit equations through exact localization, and cancel the
finite presentation isomorphisms. The localized open restriction mate is obtained
from `exact_localization_inverse_mate`, using the existing invertibility of
`openRestrictionMap`. The final proof specializes to quotient reduction and uses
the actual finite open adjunction. No system realization model is needed.

The item's DAG proof now records these four steps and their existing declaration
owners, including the exact localization lemma. No other existing module or node
is changed.

Validation: the complete module compiled through `lcompile.py` in 20.3 seconds
with no warnings. A static comparison confirms that the original theorem
signature is preserved verbatim; the delivered Lean file contains no `sorry`.

## Proved and sorry left

Closed: `WeilConjectures.IntegralSystemRealization.integralOpenScalarUnitSquare`
(node `lem-sf-integral-open-scalar-unit-square`), the original one of one holes.
Added: zero holes. Split off: zero statements. Remaining in the delivered module:
zero `sorry` declarations. All private helpers have complete proofs.

## No longer needed

No imports removed and no modules withdrawn. The proof does not call
`integralReductionPullFiniteSquare`; its module remains required for the definition
`integralFiniteScalarPull`. It also does not use the whole-system evaluation
calculus or a finite evaluation theorem. The original direct proof dependencies
`lem-coef-derived-system-evaluation-calculus` and
`lem-weil-derived-scalar-extension-restriction-adjunction` are unnecessary for
this proof and have been removed from `proof_deps`; existing statement dependencies
are preserved. Finite reduction isomorphisms are used through naturality and
inverse cancellation, so their scalar-unit normalization need not be unfolded.
The broad nodes `lem-pur-compact-support-integral-coefficient-comparison` and
`def-pur-integral-compact-support-coefficient-data` are not proof prerequisites: the proof names the existing lower definition owners instead.
Their modules still provide the actual scalar and finite presentation definitions.
The proof does not use `PurCompactSupport.openComparison_isIso`; the scalar open
map is used only through its defining mate. No unit statement or unit proof route
is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned mathematical argument works. Its single prose step omitted the Lean
assembly for the two mate operations and finite presentation transport. These are
now proved locally rather than split into another instance of the same obligation.
The original list of proof dependencies also named the broad coefficient theorem
instead of the existing lower declaration-owner nodes; the updated proof uses
those lower owners. No statement correction, definition repair, or consumer
adaptation was necessary.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
