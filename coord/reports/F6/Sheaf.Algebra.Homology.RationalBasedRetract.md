## What changed

Proved `RationalBasedRetract.universal_homotopy` in the assigned module. The proof follows
all six general-retract steps of the node; the seventh, constant-complex step was already
proved and its proof is retained.

Private proved helpers establish the fixed splitting, identify kernel cycles with
boundaries using injectivity of the given homology map, and construct complements with
bijective restricted differentials. For arbitrary supplied complements, the homotopy is
the inverse differential composed with projection onto cycles along the sum of the
inclusion's range and the complement. The prescribed formula, bottom-degree vanishing,
homotopy equation and all side identities are checked explicitly. Componentwise
DFinsupp maps give the direct sums. Rational basis coordinates prove that finite-column
extension preserves compositions, sums, differences, zero, identity and index transport;
this gives all identities over every rational algebra, including the zero algebra.

Added the proof-only import `Mathlib.LinearAlgebra.Basis.VectorSpace` for unrestricted
vector-space complements. Public signatures, definitions and imports are unchanged.
No other existing module is changed.

Validation: the complete module compiled without errors or warnings in 17.0 seconds.
`#print axioms` for both public theorems returned exactly `propext`, `Classical.choice`
and `Quot.sound`. The main theorem's signature, every original public definition and
public import, and the complete constant specialization were compared with the current
source and are unchanged. The temporary axiom-print commands were removed before delivery.

## Proved and sorry left

Closed the one remaining hole: `RationalBasedRetract.universal_homotopy`
(node `lem-sfb-rational-based-retract-universal-homotopy`).

Added zero holes; zero holes remain in the module. The previously proved
`RationalBasedRetract.constant_universal_homotopy` remains proved. Every added private
helper has a complete proof. This is a proof, not a decomposition.

## No longer needed

None. Both declared dependencies remain used: the module-complex homology API for
kernel acyclicity, and the arbitrary-dimensional vector-space complement result for
cycle complements. The proof follows the existing route, so no DAG changes are needed.
No original import, node or module is pruned. A redundant explicit proof import of
`Mathlib.LinearAlgebra.Projection` was removed from the working draft because the
existing Finsupp import already provides it.

## Where the brief, the DAG or earlier work was wrong

None. No statement or definition repair, forced adaptation, new node or source-library
change was needed. The proof actually only needs injectivity of the hypothesized
homology isomorphism; it preserves the stated hypotheses verbatim.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
