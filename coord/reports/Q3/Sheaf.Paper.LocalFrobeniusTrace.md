## What changed

Filled the five theorem proofs in `Sheaf.Paper.LocalFrobeniusTrace`. Added a private
proof import of `WeilConjectures.PointCount` for the geometric characterization of
the residue-field algebra map. The four private helpers identify positive powers
of point Frobenius, compute both geometric-Frobenius projections, prove the return
equation for any fixed model point, and specialize the library's finite-field
Frobenius fixed-point theorem to a finite embedded field.

The compatibility equations follow from contravariant functoriality of Spec and
the specified structure maps. Closed-point degree positivity uses
`closedPoint_iff_residueField_trdeg_zero_and_finite` and `Module.finrank_pos`.
For extension points, the selected subfield has cardinality q^n. For closed points,
`Module.natCard_eq_pow_finrank` gives cardinality q^r. In both cases the existing
`FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq` fixes the
embedded field, and pullback uniqueness proves the semilinear return equation.

All existing signatures, definitions, visibility and public imports are preserved.
There are no new modules, new nodes, statement changes or forced adaptations.
The existing node has no numbered proof plan; these are direct proofs of the
five obligations already described in its statement and declaration docstrings.

## Proved and sorry left

Closed five original holes, all belonging to `def-weil-local-frobenius-trace`:

- `WeilConjectures.localExtensionPoint_compatible`
- `WeilConjectures.localExtensionPoint_return`
- `WeilConjectures.localClosedPointDegree_pos`
- `WeilConjectures.localClosedPoint_compatible`
- `WeilConjectures.localClosedPoint_return`

Added zero holes; split off zero statements; no sorry remains in the delivered
module. The private helpers are proved completely. This is a proof delivery,
not a decomposition. Imported project declarations retain their existing proofs
and any pre-existing upstream obligations.

## No longer needed

None. Every original public import supports the existing statements or
definitions. No node or module is withdrawn. The source library already supplies
the finite-field Frobenius calculation, so no new theory or duplicate lemma node
is needed. The unit's route and its realized nodes are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The return equation is correctly
semilinear, with the point-spectrum Frobenius on the right. Positivity handles
the n=1 and residue-degree-one boundary cases without natural-number subtraction
changing the exponent. Empty schemes give no extension or closed points and
require no special case. The earlier interrupted session left the proofs on
disk but no report or delivery receipt; this session resumed that sandbox.

On resumption, the retained report was present and the retained dry-run log
recorded a failed compile, with nothing pushed. The required fresh dry run
localized the remaining error to two redundant tactics after `congr 2` had
already closed `localPointPower_spec`. Removed those tactics. No delivery
process was active when the checks resumed. Two subsequent standalone compile
requests received no answer from the server (187 and 219 seconds); these were
server-response failures, not Lean file timeouts.

Current continuation validation: the required initial dry run received no server answer
within 195 seconds and pushed nothing. The subsequent prescribed standalone
`lcompile.py` check compiled the complete retained module successfully in 41.1
seconds (exit code 0). No Lean source changes were needed in this continuation.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
