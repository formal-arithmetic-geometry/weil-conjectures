## What changed

Proved `Algebra.exists_universalFirstOrderThickening_core` with its signature unchanged.
The proof uses the canonical polynomial presentation, the differential exact sequence,
and the free polynomial differential module to split the conormal differential. It
constructs the complement ideal and quotient explicitly, proves surjectivity and the
square-zero kernel, and descends the unique polynomial lift through the quotient.

Added the fully proved module `Sheaf.RingTheory.ConormalComplementPolynomialLift`,
with public theorem `Algebra.conormalComplement_polynomial_lift` and two proved
private helpers for existence and uniqueness. Existence descends the obstruction
through the differential kernel and corrects a polynomial lift by a derivation.
Uniqueness gives the square-zero ideal its quotient scalar action and proves that
the difference derivation is zero. No data is chosen from an unproved theorem.

The core has a proof-only import of the new module. Its existing public import
is unchanged. The new module publicly imports the cotangent interfaces needed by
its statement. Those interfaces also supply the projective-module and square-zero
derivation APIs, so their redundant explicit imports were removed during second reading.
The original DAG proof now records the implemented complement and quotient argument.

Both files compile cleanly using the required launcher, in import order.

## Proved and sorry left

Closed the sole original hole:
`Algebra.exists_universalFirstOrderThickening_core`
(node `lem-weil-pbc-ring-universal-first-order-thickening-core`).

The new public theorem `Algebra.conormalComplement_polynomial_lift`
(node `lem-weil-pbc-conormal-complement-polynomial-lift`) and its private helpers
`polynomialLift_exists` and `polynomialLift_unique` are fully proved from Mathlib.
No `sorry` remains in either delivered module. No hole was added or split off.
This is a proof, not a decomposition into unproved statements.

## No longer needed

No existing import or dependency module was pruned. The direct dependency
`def-weil-pbc-kahler-differentials` moved from the core node to the new polynomial-lift
node; it remains used transitively and is not pruned from the proof closure. The other
four original dependency nodes remain direct dependencies: polynomial presentation,
Jacobi-Zariski exactness, the unramified vanishing criterion, and the polynomial basis.
Second reading removed redundant sandbox-added imports:
`Mathlib.RingTheory.Extension.Cotangent.Basic` and `Mathlib.Algebra.Module.Projective`
from the core, and `Mathlib.RingTheory.Derivation.ToSquareZero` from the new module.
These removals prune no existing library module.
The earlier sandbox-only existence theorem
`Algebra.exists_universalFirstOrderThickening_core_exists` and its uncommitted node
`lem-weil-pbc-ring-universal-first-order-thickening-core-existence` were discarded.
An exploratory explicit import of `Mathlib.LinearAlgebra.Isomorphisms` was removed;
the required quotient-linear-map API is already supplied by the statement import.

## Where the brief, the DAG or earlier work was wrong

The previous attempt said uniqueness followed from surjectivity of the thickening
map. It does not: the needed input is surjectivity of the differential of the chosen
complement. The present proof explicitly constructs that complement and proves
uniqueness by factoring the difference derivation through its differential image.
The source argument was read at [Stacks 04EB](https://stacks.math.columbia.edu/tag/04EB).
No existing statement or definition was changed, and the unit route is retained.

LeanSearch was unavailable (Internal Server Error), recorded by the search launcher.
Loogle, LeanFinder and source searches supplied the Mathlib APIs. A blueprint search
for 04EB and DAG/source searches found no existing polynomial correction statement.

## New nodes

`lem-weil-pbc-conormal-complement-polynomial-lift` records the already-proved polynomial
correction result, exactly as declared in `Sheaf.RingTheory.ConormalComplementPolynomialLift`.
It is strictly a part of the argument: it takes a presentation and a complement ideal
with two differential properties, and proves a polynomial lifting property. The core
constructs that ideal, verifies those properties, constructs the quotient and proves
its kernel and universal property. The helper does not assume formal unramifiedness.
It works even when the complement does not contain the kernel square, using
`K/(K ∩ J²)`; the core separately establishes `J² ≤ K` for its square-zero quotient.

Edge cases checked against the proof: empty generator families have zero differential
module; the zero target ring forces any available square-zero test quotient to be
trivial; `I = 0` leaves a zero correction; and `K = 0` is allowed only when the
surjectivity hypothesis forces the differential target to be zero. No nontriviality,
finiteness, characteristic or nonempty-generator hypothesis was introduced.
There is no change record because no existing interface changed.


## Second reading by C1

1. **Interfaces unchanged: pass.** Compared the core with the repository using `diff`;
   its sole existing theorem signature is byte-identical, its docstring and public
   import are unchanged, and there is no definition or target change. The new helper
   is a strict component of the argument, not a renamed copy of the core.
2. **Proof and kernel checks: pass.** Read both proofs in full and compiled both modules
   locally in import order. No `sorry`, axiom, unsafe declaration, opaque declaration,
   external implementation or skipped kernel check occurs. Scratch-copy `#print axioms`
   checks cover the core, public helper and both private helpers; all show only
   `propext`, `Classical.choice`, and `Quot.sound`. The quotient, ideal and derivation
   are actual constructions; all choices use proved surjectivity or inverse theorems.
3. **New statements: pass.** No unproved statement was split off. Reviewed the fully
   proved helper against Stacks 04EB and checked empty generators, `I = 0`, `K = 0`,
   and the zero ring: the differential hypotheses remain sufficient, with no added
   nontriviality or finiteness assumption. Repeated grep, Loogle and LeanFinder searches
   using lift/derivation and relation-spanning formulations; the existing Mathlib
   square-zero derivation APIs are already used, and no full correction theorem was
   found. Source searches in both library roots found no duplicate.
4. **Route and pruning: pass after repair.** The core uses exactness, unramified
   differential vanishing and the polynomial basis to construct a complement, then
   applies the helper and descends to the quotient. This matches Stacks 04EB and is
   below the unit level. Checked `dag/units/sk-thm-p1.json` `realized`: no realized
   statement or step is bypassed or altered. Removed three redundant added imports;
   the remaining public helper import is required by its signature. Corrected the
   report to distinguish the relocated direct Kähler dependency from actual pruning.
5. **DAG agrees: pass.** The existing node changes only `proof`, `proof_deps` and
   `proof_origin`; all other fields are unchanged. Its dependency set is exactly the
   union of the proof steps' `uses`. The helper's statement, Lean record, source,
   complete verbal proof, searches, provenance, chapter and unit match its declaration.
   Its two recorded dependencies are precisely the union of its proof steps' `uses`.

Second reading changed only the three redundant imports and this report. No proof,
statement, definition or DAG repair was needed. One original hole closed, zero holes
added; no split-off unproved theorem and no existing module pruned.
