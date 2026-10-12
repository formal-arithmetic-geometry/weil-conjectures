## What changed

Replaced the rejected `PopescuLiftCore` attempt with the source's induction on positive list
length. The item now proves `Algebra.canBePopescuResolved_of_quotient_eighth_powers` by
`Nat.le_induction`: use the one-element case at the base, and use the tail quotient lemma
followed by the one-element case at the successor. The successor assembly and transport of
both annihilator conditions are real Lean in the item. A proved private helper transports
the conditions by the linear equivalence of quotients by equal ideals.

`Sheaf.RingTheory.PopescuLiftInduction` defines the induction claim and the compatible
quotient-resolution premise; both definitions are explicit predicates without any witness
choice. The target signature and its public imports are unchanged.

## Proved and sorry left

Closed the item's one hole, `Algebra.canBePopescuResolved_of_quotient_eighth_powers`.
Added exactly two holes: `Algebra.popescuEighthPowerLifting_one` in
`Sheaf.RingTheory.PopescuLiftOne` (node `lem-weil-pbc-popescu-lift-one`) and
`Algebra.popescuEighthPowerLifting_tail` in `Sheaf.RingTheory.PopescuLiftSuccessor`
(node `lem-weil-pbc-popescu-lift-successor`). The latter concludes only resolvability
of the first quotient, assuming lifting for the shorter tail. It never asserts
resolvability of the original problem. This is a decomposition, not a proof free of
sorry; one hole closed and two added gives net minus one before closure accounting.
The rejected old core and its hole have been removed from the sandbox delivery.

## No longer needed

Removed the rejected sandbox-only `Sheaf.RingTheory.PopescuLiftCore` and node
`lem-weil-pbc-popescu-lift-core`; these never belonged to the accepted library.
Removed direct proof imports of `Sheaf.RingTheory.PopescuDesingularizeLiftingApply`,
`Sheaf.RingTheory.SingularIdeal`, and `Sheaf.RingTheory.StrictlyStandardBaseChange` from
the item. Desingularization remains needed for the new base case, and strict standard
base change remains needed for the tail's planned proof. No original planned mathematical
node can be declared globally unnecessary: their work is retained below the two new holes.
No unit-level statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier core asserted the entire target without its real hypotheses. It was invalid,
and adding localization data would not repair that defect. The replacement uses precisely
the source's one-element case and induction paragraph (Stacks 07F8, lemma-lift-solution).
The tail proof identifies successive quotients and transports all data before applying the
induction hypothesis; those are the difficult remaining details, and the new docstring
records them. Quotient scalar structures prevented naive rewriting of the first annihilator
hypotheses; the item instead uses an algebra equivalence and its linear equivalence.

Checked the edge cases of the new statements: the base has exactly one element; the tail
requires n >= 1, so there is a first element and a nonempty shorter tail. Zero rings,
zero elements, and repeated elements are permitted with the original annihilator and
standardness assumptions. The induction predicates exactly retain the quotient finite
presentation witness, compatible map, prime pullback equation, and resolution premise.

Searches ran through msearch: LeanSearch was unavailable (HTTP 500); LeanFinder returned
formal-smooth lifting results requiring additional smoothness hypotheses; grep found
Gabriel-Popescu results unrelated to desingularization. Searches in both library roots and
the blueprint found no existing lifting induction interface. No fabricated search is recorded.

## New nodes

`def-weil-pbc-popescu-lift-induction` records the explicit predicates in
`Sheaf.RingTheory.PopescuLiftInduction`.
`lem-weil-pbc-popescu-lift-one` records the one-element lifting obligation in
`Sheaf.RingTheory.PopescuLiftOne`.
`lem-weil-pbc-popescu-lift-successor` records the first-quotient tail obligation in
`Sheaf.RingTheory.PopescuLiftSuccessor`.
The original item's proof and dependencies now follow the Lean induction assembly.

## Second reading by X3

1. I compared `PopescuLiftSolution.lean` with the repository version. The target theorem's
   signature is byte-for-byte unchanged; only its proof imports and body changed. The three
   additional modules are new split-off declarations and do not alter an existing interface.
2. I compiled all four delivered modules with `lcompile.py --all`; they compile cleanly. A
   search found no forbidden commands. The only remaining `sorry`s are the two named split-off
   theorems, each public, documented with its source and blueprint node. The private transport
   helper is a real proof. The target proof has no `sorry`. Scratch `#print axioms` checks
   give only `propext`, `Classical.choice`, and `Quot.sound` for the two predicates; the
   target and the two split-off theorems additionally use the expected `sorryAx`.
3. I checked the split-off statements against their DAG records and source paragraph. The
   induction predicate preserves the finite-presentation witness, quotient map compatibility,
   prime pullback, and resolution premise. The one-element theorem is exactly `P(1)`. The tail
   theorem concludes only the first quotient resolution and assumes `n ≥ 1` and `P(n)`, so it
   is strictly smaller than the target and is not a restatement. Zero rings, zero list entries,
   and repeated entries remain allowed by the signatures.
4. The proof follows the unit route: `Nat.le_induction`, the one-element case, and the tail
   quotient case. The quotient annihilator transport uses an algebra quotient equivalence and
   a linear equivalence preserving and reflecting scalar multiplication and zero. The old
   rejected core and its import-only dependencies are pruned; no unit step is bypassed.
5. The DAG `proof` and `proof_deps` now match the imports and applications in the target proof;
   the three new nodes contain the corresponding source, proof plan, searches, and Lean records.
   No existing declaration or target statement was changed.

I corrected stale numbered-step references in the two new proof plans and added the
finite-presentation universe transport to the one-element node (already in its Lean docstring).
I added the axiom-check results and independent search results to this report. Lean was unchanged.

Independent searches: LeanFinder for "desingularization resolution finite presentation quotient
by regular sequence" returned only standard-smoothness, localization, and finite-presentation
lemmas, none proving either obligation. Mathlib grep for desingularization and quotient
annihilators found only unrelated annihilator-quotient identities. Searches of both project
library roots found the existing general lifting item and its callers, no duplicate of either
new induction obligation.
