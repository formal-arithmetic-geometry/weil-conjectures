## What changed

Kept the existing signature of `Algebra.exists_popescu_separable_preparation` byte for byte.
Replaced the first worker's conjunction-reordering proof with a genuine reduction: obtain
polynomial construction data before choosing parameters, apply the existing
`Ideal.exists_generators_with_controlled_annihilators` at exponent `8 * c`, define the
polynomial evaluation with `MvPolynomial.aeval`, specialize the universal construction,
and prove prime membership and the quotient/scalar-action identifications.

The new proof-only module `Sheaf.RingTheory.PopescuSeparablePreparationCore` states only
the receiving-ring-independent polynomial construction and its universal evaluation property.
It has no regular-local, dimension, prime, parameter-generation or annihilator conclusion.
Its one remaining theorem has a source and complete construction proof in its docstring.
There are no new definitions or choices of data in definitions.

## Proved and sorry left

Closed: `Algebra.exists_popescu_separable_preparation` (one original hole).
Added: `Algebra.exists_popescu_separable_preparation_core` (one named hole), node
`lem-weil-pbc-popescu-separable-preparation-core` in the new core module.
The target module contains no `sorry`. The existing controlled-generator theorem remains
open in its own unchanged module. This is a decomposition, not a completed proof:
one hole closed, one added, net zero. Axiom checks on scratch copies of both delivered
modules report only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.

## No longer needed

No module is pruned from the import closure. The target's direct proof-only imports
`Sheaf.RingTheory.ImprovePresentation`, `Sheaf.RingTheory.SingularIdealLocalizationSmooth`,
and `Sheaf.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower` move to the core
construction module; all remain needed by that construction's proof plan.
`Sheaf.RingTheory.ExistsGeneratorsWithControlledAnnihilators` is retained in the target.
Every existing public import is unchanged.

The old target proof dependencies no longer used directly are:
`lem-weil-pbc-finite-type-algebra-noetherian`, `def-weil-pbc-singular-ideal`,
`lem-weil-pbc-singular-ideal-localization-smooth`, `lem-weil-pbc-polynomial-ring-smooth`,
`lem-weil-pbc-smooth-ring-map-base-change-composition`,
`lem-weil-pbc-smooth-ring-map-principal-localization`,
`lem-weil-pbc-smooth-ring-map-local-on-cover`, `lem-weil-pbc-improve-presentation`,
`lem-weil-pbc-finite-type-noetherian-finite-presentation`,
`lem-weil-pbc-smooth-free-differentials-strictly-standard-power`, and
`def-weil-pbc-popescu-resolution`. They remain transitive dependencies of the core
construction node. The target directly uses that node and
`lem-weil-pbc-popescu-find-sequence`.

The first worker's augmentation module/node are absent from the delivery; they never
existed in the repository baseline. Its obsolete proof-only change record was removed;
there is no change to any existing statement or definition requiring a change record.

## Where the brief, the DAG or earlier work was wrong

The first worker's revised core repeated all hypotheses and all conclusions of the target,
merely swapping the last two conjuncts. That was a restatement, not a valid reduction.
Its docstring still claimed to omit the strict-standard and annihilator clauses even
though its signature included both, and the target node had not been updated to its proof.
The old report incorrectly claimed construction imports could be discarded despite the
remaining construction hole needing them. The obsolete change record still referred to
an augmentation theorem no longer delivered.

Read the source at the local literature mirror's `smoothing.tex`, proof of Lemma 07FE
(lines 2368 onward). The repaired construction uses generators of H_{A/k} and membership
in its extension itself, as required by the existing corrected parent statement; the
source's H_{A/R} notation and later use of its radical are not silently substituted.

## New nodes

`dag/nodes/sec-proper-base-change/lem-weil-pbc-popescu-separable-preparation-core.json`
is new relative to the repository. It describes the independent quotient/retract
construction, records its actual signature, complete source-based proof steps, statement
and proof dependencies, origin, creation metadata, blueprint link, and three required search categories
through `msearch.py`: LeanSearch (service unavailable, recorded without a negative verdict),
Loogle/LeanFinder (both run successfully), and grep. The existing parent node is updated only
in its stage-3 proof/proof-dependency/origin fields. No change record is needed.

## Forced adaptations

None.

## Second reading by F1

1. Compared the target module with the repository using `diff` and a byte comparison of
   the declaration signature. Verdict: identical existing signature and public imports;
   no existing definition or declaration changed outside the target proof.
2. Compiled both files through `lcompile.py` in import order. Inspected all source for
   forbidden declarations and holes. Scratch `#print axioms` checks on both declarations
   showed only the standard axioms and `sorryAx` from the explicitly open construction
   and existing controlled-generator theorem. Verdict: a genuine reduction, with one
   named sourced hole and no hollow definition or data selected in a definition.
3. Read the new construction from its source, including the fixed quotient, smooth
   principal cover, improve-presentation retraction, common strict-standard exponent,
   and universal evaluation. Checked d = 0 (empty strict-standard and parameter families),
   n = 1, zero receiving ring, and empty singular-ideal generator family (zero
   localizations at X_i). None needs a new assumption. Unlike the original restatement,
   this lemma does not assert the local parameter or annihilator result. Repeated real
   LeanFinder, Loogle and grep searches, and recorded LeanSearch service unavailability with different terms, plus rg of the upstream and
   Sheaf library: existing evaluation, strict-standard-power and controlled-generator
   ingredients are used or retained; no existing theorem provides the universal
   polynomial quotient/retract construction. Verdict: true and strictly a part of the
   argument, but its construction proof remains open; not counted as net proof progress.
4. Kept the source's construction-before-parameter-selection route. Read
   `dag/units/sk-thm-p1.json`: this item is not any unit statement or realized step.
   All original construction dependencies remain reachable through the core node;
   there is no unit-level bypass and no closure pruning. Verdict: route preserved.
5. Checked parent and core node proof steps, dependencies, origin, declaration names,
   signatures, and new-node metadata against the delivered code. Verdict: synchronized;
   parent proof uses the construction and existing controlled-generator theorem, while
   the core retains the source's construction dependencies without a parent cycle.

Changed: replaced the restatement with the independent universal construction, rewrote
its docstring and node, proved the actual generator/prime/annihilator reduction in the
target, retained required construction imports, updated the parent node, removed the
obsolete change record, and corrected the report's progress accounting.
