## What changed

Retained and checked the categorical part of the earlier attempt in
`lean/Sheaf/SixFunctorsBasics/BrownHypotheses.lean`. The four private helpers
`localizingClosure_isLocalizing`, `isZero_of_localizingClosure_orthogonal`,
`localizingClosure_generatingFamily`, and `brownHypothesesFor_of_compact` are complete.
They prove localizing closure, orthogonal zero-detection, generation by representatives,
and assembly of Brown's hypotheses from the structural and compactness inputs.
`Mathlib.CategoryTheory.Triangulated.Orthogonal` is a new proof-only import.

The original statement and definition are unchanged. `brownHypotheses` is marked
`STATEMENT-DISPUTED` because its compactness clause is asserted for an arbitrary
positive-characteristic base field without a cohomological-dimension condition.
The original three proof-dependency imports are retained: the unfinished theorem
has not established a replacement route for their compactness and smallness inputs.

## Proved and sorry left

Closed: none of the original one sorry. Added: zero sorries.
The remaining sorry is `CategoryTheory.brownHypotheses`
(blueprint: `sk-lem-brown-hypotheses`). This is a disputed-statement delivery,
not a completed proof or a decomposition of that theorem.

The four private helpers named above compile. In particular, generation does not
require compactness: the double orthogonal is a localizing subcategory containing
S, so a right-orthogonal object of Loc(S) has zero identity. The coproduct argument
then converts this zero-detection into `IsTriangulatedGeneratingFamily`.

Validation: the resumed required dry run passed compilation and preflight
(commit `a1b322426a`, nothing pushed), with review class CODEX because of the
disputed statement. All four retained helpers compile with the current dependencies.
The delivery repeats the compile and preflight checks.

## No longer needed

None claimed. The original direct proof imports are all retained. The earlier
report incorrectly claimed that the ambient, smallness and generation detail
modules were pruned even though `brownHypotheses` remained unproved. The generic
generation argument is available as a future replacement for the zero-detection
part of the generation detail; its compactness part is still needed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: The cohomological finiteness needed for compactness is missing
from the arbitrary-field assertion. This is already visible in the source:
`sk-def-sfb-dc-setting/_section.md` explicitly says that the base field has no
further hypothesis, whereas `sk-prop-ctf-finite-compact/`
`sk-prop-ctf-finite-compact-etale.md` assumes that finite type over that field
makes all ell-cohomological dimensions finite. That implication fails for
positive-characteristic fields of infinite ell-cohomological dimension.
The finite-coefficient proof uses this finiteness to apply Stacks Tag 0F11 to
unbounded derived global sections; it cannot be supplied by the stated scheme
hypotheses alone.

Stacks Project Lemma 59.96.2 distinguishes these two assertions: finite type
gives finite relative cohomological dimension, but its absolute bound for X
also assumes finite cohomological dimension of the base field. Reference:
https://stacks.math.columbia.edu/tag/0F0Y .

The mismatch in the existing Lean interfaces is precise:
`WeilConjectures.finiteCompactProEtale` and
`AlgebraicGeometry.ProEtale.constructible_compactness` require a
`WeilConjectures.FiniteFieldDatum`, which an arbitrary field `k` does not supply.
`AlgebraicGeometry.ProEtale.integralConstructibleCompactness` additionally takes
an explicit function of Ext bounds and a proof of those bounds.
`WeilConjectures.brownHypothesesGeneration` likewise requires `FiniteFieldDatum`.
Its algebraic-closure coefficient uses `Profinite.padicAlgClRingObj`, with
finite-subextension-valued sections, whereas `IsLocalizingAdmissibleCoefficient`
uses `Profinite.continuousMapRingObj (PadicAlgCl ell)`, with all continuous sections.
An identification of those coefficient objects is not provided by the hypotheses.
`AlgebraicGeometry.ProEtale.det_brown_hypotheses_small` also uses
`Profinite.padicAlgClRingObj`, so this mismatch affects the smallness input too.

The earlier report also grouped generation with the disputed compactness claim.
The compiled categorical argument shows that generation itself follows from the
localizing intersection and shift stability; the unresolved issue is compactness.
No counterexample has been formalized in Lean, and no false replacement lemma,
weakened statement, new axiom or additional sorry has been introduced. Resolution
requires reviewing the intended base-field/coefficient range before completing
the compactness step. No change record is needed: public statements, definitions,
visibility and public imports are unchanged.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
