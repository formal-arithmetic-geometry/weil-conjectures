## What changed

Proved `Ring.finite_maximalIdeals_containing_nonzero` in
`lean/Sheaf/RingTheory/FiniteMaximalsOverElement.lean`, preserving its signature,
visibility and docstring. Added the proof-only import
`Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`.

The proof follows the existing two-step DAG plan. The minimal primes over
`Ideal.span {x}` are finite by
`Ideal.finite_minimalPrimes_of_isNoetherianRing`. For a maximal ideal `m` containing
`x`, `Ideal.exists_minimalPrimes_le` gives a minimal prime `p` below `m`.
Since `x` belongs to `p` and is nonzero, `p` is not the bottom ideal.
`Ring.krullDimLE_iff` converts the dimension hypothesis to `Ring.KrullDimLE 1 R`,
and `Ideal.IsPrime.isMaximal_of_ne_bot` makes `p` maximal. Thus `p = m`, and the
claimed set is a subset of the finite set of minimal primes.

Searched with LeanFinder, Loogle and the launcher's grep service, and read the
relevant Mathlib signatures. The Dedekind-domain finiteness results require
additional hypotheses, so they were not used. The two existing proof-dependency
nodes are Mathlib leaves; their recorded declarations are used directly. No new
node or change record is needed: the route and interface are unchanged.

## Proved and sorry left

Closed the sole hole: `Ring.finite_maximalIdeals_containing_nonzero`
(node `lem-sc-finite-maximals-over-element`). Holes closed: 1. Holes added: 0.
No `sorry` remains in the module, and no intermediate statements were split off.
Local single-file compilation passes without warnings; the delivery dry run also
checks the declaration's axioms.

## No longer needed

None. No existing imports were removed. Both existing Mathlib proof-dependency
nodes remain needed: `lem-sc-finite-minimal-primes-over-ideal` and
`lem-weil-pbc-prime-contains-minimal-prime`. The dimension definition node
`def-weil-pbc-krull-dimension-ring` also remains needed. No Sheaf proof dependency
module is imported, and no unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original module lacked the proof-only import
providing finiteness of minimal primes; it is now present. Mathlib already supplies
the dimension-one identification needed by step 2, so no new theorem is required.
For a unit `x`, the relevant sets are empty and the proof still applies. The
nonzero hypothesis is used precisely to exclude the bottom minimal prime.

## Second reading by H4

1. Interface: PASS. Compared the complete sandbox module with the repository
   using `diff -u`. Only the theorem proof and one plain proof-only import change.
   The existing declaration signature, visibility and docstring are byte-for-byte
   unchanged; no definition or target statement changes.
2. Proof: PASS. Independently compiled the delivered file with `lcompile.py`
   without errors or warnings. Compiled a scratch copy with `#print axioms
   Ring.finite_maximalIdeals_containing_nonzero`: exactly `propext`,
   `Classical.choice`, and `Quot.sound`. No sorry, forbidden declaration,
   or data definition is present in the delivered module.
3. Split statements: PASS (none). No new statement or hole is introduced.
   Checked the actual Mathlib signatures for finite minimal primes, existence
   below a prime, and maximality of a nonzero prime in dimension at most one.
   The nonzero assumption excludes bottom; units give an empty set, and a
   nonunit in a dimension-one domain causes no additional assumption.
4. Route and pruning: PASS. Independently searched with different wording using
   LeanFinder, Loogle and grep, and searched both library roots. No shorter
   applicable direct theorem was found; Dedekind results impose extra conditions.
   The two public imports provide the statement's Noetherian and dimension
   notions; the added minimal-prime finiteness import is plain and proof-only.
   All three old proof dependency nodes are used, so `No longer needed` is
   complete. Read `dag/units/sk-thm-curveestimate.json`: this helper is not a
   replacement for its realized statement or any unit step; the route stays.
5. Nodes: PASS. Read the item's node and both Mathlib-leaf dependency nodes.
   Its two proof steps, all three proof_deps, and document proof_origin agree
   with the Lean proof as written. No new node or metadata correction is needed.

Second reading changed only this report by adding the independent review;
no Lean proof, import, statement, or DAG repair was needed. Holes closed: 1
(`Ring.finite_maximalIdeals_containing_nonzero`); holes added: 0.
