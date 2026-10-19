## What changed

Completed WeilConjectures.intrinsicQbarLinear_existsUnique in
lean/Sheaf/Paper/IntrinsicQbarCategory.lean, retaining the interrupted attempt's
construction. The existing StageSystem.qbarScalarHom_laws supplies all six module
laws and both composition laws. Subsingleton.elim identifies the pair preadditive
structures. Module.ext identifies each Hom module from the prescribed scalar
formula; extensionality of Linear's data and proof irrelevance give uniqueness.
All existing signatures, definitions, visibility, and imports are unchanged.
A declaration-local linter option suppresses the unused-name warning for the
existing implicitly used qInst binder; it has no effect on downstream options.
The retained module compiles against the current remote build with no diagnostics
(8.2 seconds on 2026-10-19).

## Proved and sorry left

Closed one of the two original holes:
WeilConjectures.intrinsicQbarLinear_existsUnique (node def-weil-pbc-qbar-category).
This proof uses existing stated dependencies; it does not assert that their
transitive proofs are sorry-free. Added zero holes and zero split-off theorems.

The one original hole left is WeilConjectures.intrinsicQbarScalarCompatible
(node def-weil-pbc-qbar-category). It still requires proving that the normalized
rational tensor transition is semilinear for the transported actual field inclusion.
Its existing source and complete proof in words remain in its docstring.

## No longer needed

None. Both existing public imports remain necessary for the published statements
and definitions: GeneralAlgebraicallyClosedCoefficients supplies the intrinsic
stages and pair category; PbcQbarCategory supplies the quotient scalar construction
and its laws. No dependency nodes or library modules have been pruned. Removed the
unrelated sandbox-only Test.lean scratch experiment from the delivery file set.

## Where the brief, the DAG or earlier work was wrong

The interrupted attempt's final structure equality did not close: destructing a
let-bound Linear witness did not rewrite the earlier projected-data equality as
expected. A universally quantified structure-extensionality argument fixes this.
The item's node has no numbered proof plan; the completed proof follows the existing
scalar-laws docstring and does not introduce a different mathematical route.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
