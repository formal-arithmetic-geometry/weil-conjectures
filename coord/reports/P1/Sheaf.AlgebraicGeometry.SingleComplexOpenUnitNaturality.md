## What changed

Proved `AlgebraicGeometry.singleComplexOpenComparison_unit_naturality` in
`Sheaf.AlgebraicGeometry.SingleComplexOpenUnitNaturality` without changing its signature,
visibility, imports, or existing docstrings. Three fully proved private helpers handle
conjugate Hom equivalences, the abstract restriction mate identity, and the pullback
square coherence identity. The original DAG route is retained: transpose with the
composite adjunction, use pullback associativity and equality transport naturality,
and cancel the units by the triangle identities.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.singleComplexOpenComparison_unit_naturality`
(node `lem-pc-single-complex-open-unit-naturality`).
There are no remaining sorries in the module and no holes added elsewhere.
The proof continues to use the selected derived pullback composition theorem and
adjunctions from the existing library; it does not assert that their entire dependency
closure is sorry-free. The first worker reported a successful 55.7-second compile;
the second reader reproduced successful validation through the delivery dry run
(local compilation, axiom probe, and preflight; review class AUTO).

## No longer needed

None. No imports were added or removed, and the existing proof dependency
`lem-pc-ringed-spaces-derived-pullback-composition` remains necessary.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. LeanFinder and Loogle searches found the general
mate and conjugate identities in Mathlib, but no theorem directly stating this
restriction identity. Searches of the source library and Sheaf modules found related
base-change pasting proofs; the conjugate Hom calculation follows that existing
proof pattern. Zero coefficients, empty opens, and whole opens require no extra
hypotheses: both helpers are identities for arbitrary functors and scheme morphisms.
The final conversion is written explicitly because simplifying the chosen derived
comparison families throughout the equality exceeded the single-file time limit.

## Second reading by P1

1. Compared the delivered module with the repository version. The target theorem
signature and all existing declarations are unchanged; only the proof body was changed.
2. The delivery dry run successfully compiled the final original proof, checked
its axioms, and passed preflight (AUTO). Earlier attempts timed out under the
60-second limit, but the final validation passed without raising the limit.
The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or
`extern`.
3. The three private helpers are strictly intermediate identities (conjugate Hom,
abstract restriction mate, and pullback-square coherence), rather than restatements
of the target. Their assumptions and conclusions are exactly the identities used by
the target proof. The conjugate Hom helper also occurs privately in
`DerivedBaseChangePasting` and is inaccessible through an ordinary import; retaining
this small local calculation avoids exposing or changing that module. No public
replacement for the restriction identity was found.
4. The proof follows the node route through the selected derived pullback composition
theorem, composite adjunction mates, naturality, and triangle identities. No unit
statement or realized unit step is bypassed. The proof dependency remains
`lem-pc-ringed-spaces-derived-pullback-composition`.
5. DAG and Lean agree on the target declaration and proof dependency. The public
Mates import is justified by `conjugateIsoEquiv` in the existing theorem statement.
The selected composition coherence is used explicitly for the triples p,f',g;
p,g',f; and v,t,f, exactly as the node's planned associativity calculation requires.
The unit's realized fields are unchanged, and no old proof dependency is unused.

Changed in this second reading: this report only. The temporary import visibility
edit was reverted because Mates is used in the statement. A generic private
coherence-helper variant compiled in isolation, but neither it nor explicit
unfolding repaired the full-module timeout; both experiments were reverted. No
holes were added. The sole target proof is retained pending successful validation.
