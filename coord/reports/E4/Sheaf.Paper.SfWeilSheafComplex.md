## What changed

Proved `WeilConjectures.FiniteFieldDatum.geometricFiber_coefficientPrimeInvertible`
in `Sheaf.Paper.SfWeilSheafComplex`. The specified cardinality of the finite base
field gives characteristic `D.p` by Mathlib's `charP_of_card_eq_prime_pow`.
Since `l` is a distinct prime, `CharP.cast_ne_zero_of_ne_of_prime` makes its
cast a unit in the base field. Map that unit along the structure morphism
from the geometric fibre to the finite base, followed by evaluation at the
chosen point. The ring homomorphism preserves natural-number casts.

Added the proof-only import `Mathlib.Algebra.CharP.CharAndCard`.
All existing declaration signatures, visibility, and definitions are unchanged.
The proof handles the empty geometric fibre vacuously and uses no separatedness
or extra characteristic hypothesis. No DAG proof route was replaced: the
node is a definition node with empty `proof` and `proof_deps`, and the proof
implements the existing theorem's characteristic-and-invertibility argument.

Validation: server single-file compilation passed with exit code 0 and no
diagnostics (4.9 seconds on the resumed attempt). Every line is at most 100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.FiniteFieldDatum.geometricFiber_coefficientPrimeInvertible`
(node `def-weil-weil-sheaf-complex`). Added 0 holes; split off 0 theorems.
No `sorry` remains in the item or is added elsewhere.

## No longer needed

None. All four existing public imports supply the file's statements and
constructions, so none can be pruned. No planned proof dependency or module
is superseded.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The only hole is the coefficient-prime
invertibility theorem needed by the existing definitions; it admits a direct
proof from Mathlib and the recorded finite-field datum.

Searches: LeanFinder for a distinct prime being invertible in scheme residue
fields returned no direct match; Loogle located `CharP.isUnit_natCast_iff`.
The launcher grep query timed out (unavailable). Targeted source searches
found the cardinality-to-characteristic lemma, the prime nonvanishing lemma,
and `Scheme.Γevaluation`. Existing `model_characteristic` and
`finiteTorConstructible_etale_compact` provided examples of these APIs.


Resumed the earlier attempt without replacing its proof. Rechecked the unchanged
statement against current sources and recompiled successfully. The earlier
delivery attempt timed out while preparing a shared worktree; the resumed
required dry run uses the normal worktree-capacity queue.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
