## What changed

Proved `Ideal.associatedPrimes_fractionalPrincipalQuotient_minimal` in
`Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimesMinimal` without changing
its signature. Added the proof-only import
`Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimesHeight`.
The proof obtains height one from that existing declaration, identifies the quotient
annihilator, exhibits a nonzero numerator in the comap ideal, and applies Mathlib's
minimal-prime height criterion. Updated the item's proof, proof_deps and proof_origin
so that the DAG records the actual argument. Removed the redundant public Mathlib Height import, whose interface is used only
by the proof and already supplied by the private height sibling. Restored the original
declaration docstring. The unit's realized statements and
steps remain in use; this item realizes none of them directly.

## Proved and sorry left

Closed one hole: `Ideal.associatedPrimes_fractionalPrincipalQuotient_minimal`
(node `lem-weil-pbc-normal-domain-fractional-principal-quotient-ass-minimal`).
No sorries remain in the delivered module; no holes were added and none were split off.
This is a proof from the existing, still-unproved dependency
`Ideal.associatedPrimes_fractionalPrincipalQuotient_height`
(node `lem-weil-pbc-normal-domain-fractional-principal-quotient-ass-height`),
not an unconditional sorry-free proof of the full fractional quotient result.
Local single-file compilation passes without warnings. The delivery dry run checks
all declarations with its axiom probe.

## No longer needed

Removed the redundant explicit public import `Mathlib.RingTheory.Ideal.Height`.
The two remaining public imports provide the statement interfaces, including
minimalPrimes through AssociatedPrime.Basic. The private height sibling supplies
the height theorem and its Mathlib height lemmas. No dependency module becomes
unreachable, and no planned node was pruned: the old proof_deps list was empty.

## Where the brief, the DAG or earlier work was wrong

The item's only original proof step was a placeholder, "Strictly smaller component
of the parent argument via numerator reduction", and recorded no dependencies.
The formal proof needs the existing height-one sibling. It is now recorded explicitly;
that module does not import this item, as checked by import_direction.py.
No statement or definition was changed and no forced adaptation was needed.

The referenced local Stacks source is absent on this machine, so the source was read
at https://stacks.math.columbia.edu/tag/031T (clause (3) and its proof). The parent
module's docstring supplies the numerator-based variant implemented here.
Edge cases: if J is the whole ring (including unit fractions or A a field), its
quotient has no associated primes, so the universal conclusion is vacuous. The proof
requires no properness assumption on J; p.IsPrime and J ≤ p already force it whenever
an associated prime is supplied. A nonzero fraction always has a nonzero numerator,
so the zero ideal cannot occur. Universes and all original binders are unchanged.

Searches: LeanFinder returned the minimal-prime height criterion; Loogle confirmed
IsFractionRing.div_surjective. Searches of Mathlib Height, AssociatedPrime.Basic,
Ideal.Colon and the two project roots found the annihilator and height lemmas and
identified the existing height-one sibling. No new node was necessary.

## Second reading by J3

1. PASS: compared the delivered Lean file with the repository using diff. The
   sole theorem signature (including universes, binders and visibility) is byte
   for byte unchanged. No definitions or other modules are delivered. The node
   diff changes only proof, proof_deps and proof_origin. Public import removal
   is documented in the change record named below.
2. PASS: local compilation has no errors or warnings. A scratch copy with
   `#print axioms Ideal.associatedPrimes_fractionalPrincipalQuotient_minimal`
   reports propext, Classical.choice, Quot.sound and sorryAx, as expected from
   the existing unproved height sibling. No local sorry, axiom, unsafe, opaque,
   implemented_by, extern, hollow definition or arbitrary data choice occurs.
3. PASS: no statement was split off, no new node or hole was added. Checked the
   existing height dependency against Stacks Tag 031T(3), and considered fields,
   unit fractions and the whole-ideal quotient: these give no associated primes.
   The numerator argument excludes J = bottom for every nonzero fraction.
4. PASS: searched independently with msearch grep for minimalPrimes/height and
   height/eq_bot, and searched both Lean roots for fractional quotient results.
   Mathlib's height criterion is the direct route once height one is known;
   no existing unconditional fractional-quotient theorem provides a shortcut.
   Removed the redundant public Height import. The original proof_deps was empty,
   so the pruning list is complete. Read sk-thm-p1.realized: this item is not a
   realization of a unit statement or step, and the unit route is unchanged.
   Compiled the original sole direct importer, FractionalPrincipalQuotientAssociatedPrimes,
   against the delivered module in a scratch overlay; it passes unchanged.
5. PASS: the node's four proof steps describe exactly the Lean proof, and
   proof_deps is their uses union, consisting solely of the existing height node.
   proof_origin identifies the source and the numerator/minimality reduction.
   No new nodes require validation.

Second reading changed the redundant public Height import and restored the original
API docstring; the proof itself needed no repair. Updated the report accordingly.
Import visibility change record:
`coord/changes/FractionalPrincipalQuotientAssociatedPrimesMinimalImports.md`.
