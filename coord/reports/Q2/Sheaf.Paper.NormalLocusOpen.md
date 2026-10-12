## What changed

Replaced the first worker's `NormalLocusOpenAux` and its zero-locus existence
statement: that statement is equivalent to the whole item and was not a strict
reduction. It is not delivered.

The unchanged `AlgebraicGeometry.normal_locus_isOpen` now constructs the finite
set of non-normal associated primes of `R/fR`, proves non-normality is stable
under specialization using Mathlib localization lemmas, identifies the complement
with their finite union of zero loci, and proves that union closed.

Added the proof-only imports `Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness`
and `Sheaf.Paper.NormalLocusAssociatedPrime`. The new module states only the
associated-prime witness step from Stacks Tag 0332. All five existing public
imports remain byte-for-byte unchanged. No existing statement or definition changed.

## Proved and sorry left

Closed the original textual hole in `AlgebraicGeometry.normal_locus_isOpen`
(node `lem-weil-pbc-normal-locus-open`), conditional on the following strictly
algebraic step. Added exactly one named hole:
`AlgebraicGeometry.exists_nonNormal_associatedPrime_le`
(node `lem-weil-pbc-normal-locus-associated-prime`). Its whole proof is `by sorry`.
There are no other delivered holes, and no definitions are added.

This is a decomposition: one original hole closed and one new hole added,
net zero, not a completed proof of the item. Both declarations' axiom probes
show exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.

## No longer needed

Removed these six proof imports from the item:
- `Sheaf.RingTheory.Depth`
- `Sheaf.RingTheory.DepthLeDimAssociatedPrime`
- `Sheaf.RingTheory.DepthQuotSMulTop`
- `Sheaf.RingTheory.NonzerodivisorIfMaximalNotAssociated`
- `Sheaf.RingTheory.SerreConditions`
- `Sheaf.RingTheory.SerreCriterionNormal`

They belong to the remaining algebraic witness argument, not to the completed
finite-union and specialization assembly. The new node retains those algebraic
proof-plan dependencies. No module is asserted to be globally pruned: other
imports may still reach it, and future proof-plan import regeneration may
restore it below the new node.

Every old direct proof dependency removed from the item's node is listed below.
Definitions used in the signature remain recorded as statement dependencies;
the witness node retains the relevant algebraic dependencies. The remaining
old direct proof dependencies (localization of localization, localization of
normal domains, and finiteness of associated primes) are used by the new proof.

- `def-weil-pbc-localization-at-prime`
- `lem-weil-pbc-localization-noetherian`
- `def-weil-ring-localization-away`
- `def-weil-pbc-normal-ring`
- `def-weil-pbc-noetherian-ring`
- `lem-weil-pbc-primes-of-localization`
- `lem-weil-pbc-localize-localization-at-prime`
- `lem-weil-pbc-serre-criterion-normal`
- `def-weil-pbc-serre-conditions-rk-sk`
- `def-weil-regular-scheme`
- `def-weil-pbc-depth`
- `def-weil-pbc-krull-dimension-ring`
- `lem-weil-pbc-depth-le-dim-associated-prime`
- `def-weil-finitely-generated-module`
- `lem-weil-pbc-depth-drops-by-one`
- `lem-weil-pbc-nonzerodivisor-if-maximal-not-associated`
- `def-weil-pbc-regular-sequence`
- `def-weil-pbc-module-localization`
- `lem-weil-pbc-noetherian-associated-prime-from-localization`
- `def-weil-affine-spectrum`

## Where the brief, the DAG or earlier work was wrong

The first worker called zero-locus existence a strictly lower theorem, but on
an affine spectrum it is equivalent to the closed-complement/openness target.
A genuine algebraic intermediate replaces it. The old report also called the
item proved without acknowledging its new hole. The counts above explicitly
record decomposition.

The original nine-step route remains the route of the proof: Steps 4--8 are
isolated as the witness theorem, Step 3 is proved directly by localization,
and Step 9 is proved with Mathlib finiteness and topology. The item's node is
not in any statement/step of `dag/units/sk-thm-p1.json`'s `realized` fields;
none of those fields or unit/chapter steps is changed or bypassed.

## New nodes

`lem-weil-pbc-normal-locus-associated-prime`:
`AlgebraicGeometry.exists_nonNormal_associatedPrime_le`, in
`Sheaf.Paper.NormalLocusAssociatedPrime`. Its source is Stacks Tag 0332,
proof, Cases I and II; five docstring proof steps and the matching node
spell out the argument without a topology conclusion. Lean Finder and
Loogle returned related localization facts, not a matching witness theorem;
Mathlib grep located `associatedPrimes.finite`, used in the item.
LeanSearch returned HTTP Internal Server Error and is recorded as unavailable.
All four searches ran via `msearch.py` and are logged in `searches.jsonl`.
Searches of `lean/Sheaf`, `lean/WeilConjectures/Mathlib/RingTheory`, and the
source checkout found no duplicate witness statement.

## Second reading by Q2

1. Compared the delivered item with the repository using `diff -u` and
   checked its full theorem signature byte-for-byte with a string comparison.
   Verdict: unchanged existing signature, visibility, docstring, and public
   imports; only proof imports and the theorem proof change. The removed
   auxiliary was never in the repository; its replacement is a new declaration.
2. Compiled both delivered modules in import order using `lcompile.py --all`,
   without errors or warnings. Compiled scratch copies with `#print axioms`
   for both declarations: only the three permitted axioms and `sorryAx`,
   accounted for by the witness theorem. Text inspection found one named
   theorem hole, no forbidden commands, no definitions or arbitrary witness
   data, and no lines longer than 100 characters. Verdict: valid conditional
   proof and fully disclosed decomposition.
3. Read Stacks Tag 0332 at https://stacks.math.columbia.edu/tag/0332 because
   this machine has no local `literature/stacks-project/algebra.tex`.
   Checked the witness statement against its Cases I and II. For a field,
   or a normal domain, there are no non-normal input primes, so the statement
   is vacuous. If f is a unit, the normality assumption again leaves no
   input prime. For a non-normal prime the nonzero f enters q, allowing
   depth drop; zero f is explicitly excluded. A normal prime associated to
   R/fR is deliberately excluded from E, preventing a spurious nonempty
   complement in a normal domain. Verdict: true sourced algebraic step,
   strictly part of the argument, and no existing match found by the searches
   above. Closing its Serre/depth/localization assembly is substantial work,
   rather than a remaining proof closable in a few minutes.
4. Proved the finite-set construction and both inclusions of the closed
   complement directly, using Mathlib for finiteness and specialization.
   Removed six unused proof imports and listed every superseded old direct
   dependency. Checked the unit's realized statements and steps remain intact.
   Verdict: the original finite-associated-prime route is retained with a real
   reduction, and only signature-required imports are public in the new module.
5. Read both final node records against the Lean. The item's proof/dependencies
   describe the actual witness, finiteness, specialization, and finite-union
   proof. The new node has source, five complete proof steps, union of uses,
   correct creation and blueprint records, actual logged searches, and a Lean
   statement copied verbatim from its module. Verdict: records agree.

Changed in this second reading: removed the equivalent zero-locus auxiliary;
introduced the associated-prime witness; wrote the finite-union and
specialization proofs; pruned six direct proof imports; corrected both DAG
records and the progress accounting.
