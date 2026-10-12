## What changed

The existing signature and visibility of `RingTheory.derivation_extends_finite_type_extension`
are unchanged. Its proof combines `RingTheory.exists_derivation_away_transport` with
`RingTheory.exists_derivation_of_finiteType_away_extension` in two new modules. The second
reader proved both helpers, so the delivery is now a proof, not a decomposition with holes.

The transport proof uses the proved localization clause of
`Derivation.exists_completion_and_unique_localization` and explicitly conjugates its result
by the canonical ring isomorphism. The finite-type proof clears denominators of the derivative
values on generators directly, uses algebra-adjoin induction including the coefficient case,
and restricts using unique preimages under the injective localization map. Both helpers retain
the original injectivity parameter, renamed `_hinj` because their proofs do not need it.

Removed unrelated public imports from the two new modules. Their public imports now provide
only the types in their signatures; the transport helper imports CompletionAndLocalization
privately for its proof. Updated all three DAG proofs, dependency unions, proof origins, and
the two new signature records. No definition, existing signature, or unit record was changed.

## Proved and sorry left

Closed the original hole:
- `RingTheory.derivation_extends_finite_type_extension`
  (node `lem-weil-pbc-derivation-extends-finite-type-extension`).

Also closed both holes inherited from the first worker's proposed decomposition:
- `RingTheory.exists_derivation_away_transport`
  (node `lem-weil-pbc-derivation-away-transport`).
- `RingTheory.exists_derivation_of_finiteType_away_extension`
  (node `lem-weil-pbc-derivation-away-finite-type-core`).

Holes added against the repository baseline: zero. Holes left in any delivered module: zero.
The item has one original hole and it is fully proved; both new intermediate declarations are
also fully proved. Explicit `#print axioms` for all three declarations shows exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

Removed the direct proof-only import `Sheaf.RingTheory.Derivation.CompletionAndLocalization`
from the item; it is used in the transport helper and remains in the transitive closure.
Removed `Sheaf.Algebra.CharpolyLocallyFree` from both new modules, removed
`Sheaf.Algebra.FiniteTypeLiftNilpotent` from the finite-type helper, and removed its unused
CompletionAndLocalization import. Those were unnecessary imports introduced by the first worker.

The old direct `proof_deps` were `def-weil-pbc-finite-type-algebra` and
`lem-weil-pbc-derivation-extends`. They are no longer direct proof dependencies of the item:
the item uses the two helper nodes instead. Both old dependencies are still needed transitively:
the finite-type helper uses `Algebra.FiniteType.out` and the transport helper uses the proved
localization theorem. No pre-existing node or module is pruned from the target import closure.

## Where the brief, the DAG or earlier work was wrong

The first worker's reduction was mathematically valid, but both helper proofs were missing,
the helper docstrings lacked a source and complete proof, their public imports included
unrelated modules, and the item's node still described the original six-step proof rather
than its actual two-helper reduction. The finite-type helper's node erroneously described
localization transport. These faults are repaired.

The source's explicit quotient-rule computation on generators is unnecessary below the unit
level: one can clear the denominators of the localized derivative values themselves. This
variant preserves the localization-then-restriction argument without changing any unit step.

WANTED: literature/stacks-project/more-algebra.tex, Tag 07PE, for the three derivation nodes;
the file is absent from this machine's repository. Read the official source at
https://stacks.math.columbia.edu/tag/07PE. The supplied source references remain, and the
revised proof routes are marked `proof_origin.by = agent` rather than claiming the new
argument was copied verbatim from the missing local document.

## New nodes

`lem-weil-pbc-derivation-away-transport` is the localization/transport part only: it needs
neither finite type nor regularity and concludes only the existence of a derivation on the
localization, not a derivation on the overring. Its module is
`lean/Sheaf/Paper/DerivationAwayTransport.lean`; the helper is proved.

`lem-weil-pbc-derivation-away-finite-type-core` is restriction/integrality only: its input is
an already constructed localized derivation and it assumes no localization isomorphism. Its
module is `lean/Sheaf/Paper/DerivationAwayFiniteTypeCore.lean`; the helper is proved. It shares
Tag 07PE with the item because it supplies the finite-generator restriction part of that
argument, not a renamed restatement of the item. No change record is needed for new helpers
or proof-only edits to the existing item.

## Second reading by A2

1. Compared every delivered module against the read-only repository. The two helpers are new.
   The item's original theorem signature is byte for byte identical, and its public imports
   and visibility are unchanged. Only its proof, proof-only imports, and explanatory proof
   docstring changed. No existing definition or statement was altered. Verdict: pass.
2. Compiled the complete three-module set in dependency order using `lcompile.py`: no errors
   or warnings. Searched the delivered files for holes and forbidden declarations; none.
   Compiled a scratch copy with explicit `#print axioms` for all three public theorems:
   only the three allowed standard axioms. All chosen data come from proved existence
   results, and the restricted derivative is determined uniquely by injectivity. Verdict: pass.
3. Read both new signatures and tested the mathematical edge cases: empty generator finset,
   exponent zero, unit g, zero derivation, zero rings, and g=0 (regularity then forces the
   overring to be zero). The transport helper works even when g is a zerodivisor. The
   coefficient branch of adjoin induction covers absolute rather than R-linear derivations.
   Ran fresh leanfinder, loogle and grep searches through msearch.py, and rg searches of
   lean/Sheaf and lean/WeilConjectures. LeanSearch returned an unavailable service, recorded
   honestly. Found localization APIs and uniqueness lemmas, no duplicate of either helper.
   Both helpers are true, are proper parts of the argument, and are now proved. Verdict: pass.
4. Read from the top downward. The transport helper uses the existing proved localization
   declaration. The restriction proof takes the shorter denominator-clearing route, rather
   than introducing further statements. Inspected `dag/units/sk-thm-p1.json` and its realized
   route: this item is not a unit-realizing node, and no unit node or step is bypassed. All
   unused imports and both old direct proof dependencies are accounted for above. Verdict: pass.
5. Matched each node to the actual Lean proof. The item's dependencies are the two helpers;
   transport depends on derivation-extends; restriction depends on the Mathlib finite-type
   definition. Every dependency list equals the union of step uses. The new nodes have source,
   complete steps, origins, actual search records, creation metadata, blueprint parent,
   chapter/unit, and verbatim Lean signatures. Verdict: pass.

Second reading changes: proved both split-off theorems; removed unrelated public imports and
one redundant direct proof import; supplied complete source/proof docstrings; corrected DAG
proofs, origins, dependencies, signatures and searches; rewrote the report to record one
original hole closed, zero holes added, and zero remaining split-off holes.
