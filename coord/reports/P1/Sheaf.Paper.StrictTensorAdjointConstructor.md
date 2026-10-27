## What changed

Replaced the proof of `WeilConjectures.StrictQuotient.strictTensorAdjointConstructor`
in `Sheaf.Paper.StrictTensorAdjointConstructor`. Its statement, universes and public
imports are unchanged. The proof establishes tensor transitions by restriction of
the existing sheafified generator, identifies the ordinary tensor adjunct on
pure generators, and pastes the normalized scalar and tensor localization squares.
The ordinary factorization is the new, fully proved theorem
`WeilConjectures.StrictQuotient.strictTensorOrdinaryAdjunct` in
`Sheaf.Paper.StrictTensorOrdinaryAdjunct`; all other helpers are private and proved.
The existing generator helper modules already belonged to the original transitive
import closure. The item imports the new ordinary factorization only for its proof.

The node `lem-pur-strict-tensor-adjoint-constructor` records this direct proof.
No existing definition or statement is changed, and no consumer adaptation is needed.
Validation: `lcompile.py --all` accepted both modules with exit code 0, without
errors or warnings, under the unchanged per-file limit.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.StrictQuotient.strictTensorAdjointConstructor`
(node `lem-pur-strict-tensor-adjoint-constructor`).

No holes added or split off. The ordinary factorization is fully proved, and no
`sorry` remains in either delivered module.
The proof uses the already stated evaluation and finite quotient calculus APIs;
it does not claim those dependencies have no remaining holes.

## No longer needed

The planned proof dependencies `lem-pur-quotient-operation-adjoint-factorizations`
(`Sheaf.Paper.QuotientOperationAdjointFactorizations`) and
`lem-pur-derived-change-of-rings` (`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`)
are not invoked by this proof. The former packages additional geometric pullback
claims and uses coincident site universes. The latter is already reflected in the
recorded coefficient calculus. The direct proof instead uses the exact normalized
ordinary unit, derived unit, tensor comparison and evaluation comparison recorded
by `lem-coef-derived-system-evaluation-calculus`.

No original Lean import was removed: the public import of
`Sheaf.Paper.StrictQuotientExpressions` is required for the statement. No module
is withdrawn or claimed globally unnecessary. The direct helper imports
`Sheaf.Algebra.Homology.ScalarHomTensorCoherence` and
`Sheaf.CategoryTheory.RingedSiteDualityMaps` were already transitively imported.
The scalar tensor helper import is now in the ordinary factorization module; the
item uses that fully proved factorization instead of importing the helper itself.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is retained unchanged. The broad general factorization
is not directly applicable with the independent scheme and coefficient universes,
so the proof uses its elementary generator and adjunction argument through the
existing coefficient normalization APIs. The unit record `sk-def-purity-conv` has
no realized proof steps to bypass; its route is preserved.

The completed monolithic proof exceeded 60 seconds. First the restricted-scalar
section transport was made explicit, reducing kernel checking of the ordinary
factorization from about 56 to 9 seconds, and the derived diagram pasting and
ordinary cancellation were proved abstractly. The ordinary argument was then
extracted into its own fully proved module so each file can compile within the
unchanged per-file limit. No shared definition was changed.

## New nodes

`lem-pur-strict-tensor-ordinary-adjunct` records the fully proved ordinary tensor
adjunct factorization in `Sheaf.Paper.StrictTensorOrdinaryAdjunct`. It is the
ordinary generator step of the original constructor proof, strictly smaller than
the constructor (it asserts neither derived compatibility nor the whole pair of
constructor laws). Its node records the actual Mathlib searches, normalized
unit and evaluation APIs and the pure-generator argument. The source and blueprint
route are inherited from the item's tensor constructor step. It adds zero holes.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
