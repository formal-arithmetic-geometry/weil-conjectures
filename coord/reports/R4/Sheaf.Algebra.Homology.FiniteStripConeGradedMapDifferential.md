## What changed

Completed `HomologicalComplex₂.finiteStripGradedMap_differential` in
`Sheaf.Algebra.Homology.FiniteStripConeGradedMapDifferential`, preserving its
signature, visibility, imports and docstring. All added helpers are private and proved.

The proof follows the existing DAG plan. On the target inclusion, Mathlib's total
complex formulas cancel the horizontal differential; the signed vertical remainder
factors through the next tail. On the source inclusion, the single complex vanishes
outside `n + 1 = p`. In that degree, `hb` and `hf` identify the augmentation terms,
and the negative source differential factors through the next tail. Independent
index variables in the source-block helper justify all degree transports.
The mapping-cone identity combines the two component calculations. Cancellation
of the evaluated filtration inclusion and the evaluated cokernel condition kill
the difference in the quotient; naturality of the quotient projection proves
commutation with the graded differential. No invertibility of the diagonal map is used.

Searches: LeanFinder returned total differential and component formulas; Loogle
(`"ιTotal", "d"`) returned no hits; the recorded grep search found the total and
mapping-cone inclusion formulas. Repository searches found no existing exact theorem.

## Proved and sorry left

Closed one hole: `HomologicalComplex₂.finiteStripGradedMap_differential`
(node `lem-sc-finite-strip-cone-graded-map-differential`). No `sorry` remains in the
item, and no holes were added. This is a complete proof, not a decomposition.
The file compiles cleanly through `lcompile.py`.

The proof covers the empty strip `r = 0` by the same zero-object argument used
outside horizontal support. Source degrees other than `n + 1 = p` use the zero
single-complex component. No nonempty strip, degree bound, or diagonal invertibility
hypothesis is introduced.

## No longer needed

None. No imports were added or removed, and the proof uses the existing DAG route.
`FiniteStripConeGradedMapIsIso` is not needed or imported, as in the original plan.
No existing node or module is newly pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The source and graded quotient calculations
require explicit degree transports and unfolding of the two quotient definitions
when applying the quotient chain-map equation; these are included in the proof.

## Second reading by R4

1. Public interface: PASS. Compared the delivered module with the repository
   version. The header, sole public import, section variables, target docstring,
   and complete theorem signature are byte for byte identical. The only changes
   are nine proved private helpers and replacement of the original target proof.
   No definition, public signature, visibility, or other module was changed;
   no change record is required.
2. Proof and axioms: PASS. Compiled the complete module with `lcompile.py`,
   without errors or warnings. Compiled a scratch copy with `#print axioms`
   for the target and each of its nine private helpers. Every result lists
   exactly `propext`, `Classical.choice`, and `Quot.sound`; none uses `sorryAx`.
   Scanned the delivered source: no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, or `extern`, and no lines exceed 100 characters.
   The lift uses the proved invertibility of a monomorphism's image factor;
   it does not select data from an unproved existence statement.
3. Split statements and edge cases: PASS. No statements were split off and
   no holes were added. Read every private helper: the quotient helper uses
   cancellation of the evaluated filtration inclusion and the cokernel
   condition; the target defect is the signed vertical differential into
   vertical degree `p + 1`; the source augmentation cancels by `hb` and `hf`.
   For `r = 0`, every target summand is zero by `hsupport`; the same argument
   handles horizontal indices below zero and at or above `r`. For
   `n + 1 != p`, the source summand is zero. For `n + 1 = p`, the explicitly
   transported augmentation terms agree and the remaining negative source
   differential factors through the next tail. These checks introduce no
   degree restriction, nonempty-strip assumption, or invertibility hypothesis.
4. Route and pruning: PASS. Independent LeanFinder search for differential
   defects factoring through the next filtration step returned generic
   homotopy-cofiber component formulas. Loogle search for cokernel projection
   composition returned no hits. Repository searches using `defect`,
   `rowInclusion`, and quotient factorization found related constructions,
   but no existing specialized theorem replacing this calculation. Mathlib's
   total differential and cone component formulas are already used directly.
   The only import, `FiniteStripConeGradedMap`, is required by the public
   statement and its explicit construction. The sole old proof dependency,
   `def-sc-finite-strip-cone-graded-map`, is used; `No longer needed` is complete.
   Read `dag/units/sk-thm-picard-duality.json`: this node is below unit level
   and not a unit realization. No unit statement, step, or `realized` entry
   is bypassed or changed.
5. DAG consistency: PASS. Read the item's node and its definition dependency
   against the Lean declarations. The existing proof records precisely the
   source/target inclusion calculation, next-tail factorization, and quotient
   chain-map argument now implemented. Its `proof_deps` is exactly the used
   definition node, and its `proof_origin` identifies that same explicit
   diagonal decomposition and parent source. No node repair or new node is
   needed; all added helpers are private and completely proved.

Second reading changed only this report by adding the independent review.
The Lean proof and DAG were retained. Confirmed holes closed:
`HomologicalComplex₂.finiteStripGradedMap_differential` (one of one original
holes). Holes added: none. Holes left in this delivery: none. Split off: zero.
