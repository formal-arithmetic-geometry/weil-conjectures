## What changed
The existing target theorem now combines two proved helper theorems, in new modules
EtaleSectionCore and EtaleSectionLocalization imported only for its proof. The second reader
closed both helper proofs using Mathlib and an explicit bijective corner product map.
The target statement and all existing definitions and signatures are unchanged.

## Proved and sorry left
Algebra.Etale.exists_idempotent_splitting_of_algHom is proved, as are
Algebra.Etale.exists_idempotent_core and
Algebra.Etale.exists_localization_equiv_of_idempotent. No sorry remains in this delivery;
all three axiom prints contain only propext, Classical.choice, and Quot.sound.

## No longer needed
The target's old direct proof dependencies are replaced by the two proved helpers:
- lem-weil-pbc-etale-composition-cancellation
- def-weil-etale-morphism
- lem-weil-pbc-surjective-etale-kernel-idempotent-fg
- lem-weil-pbc-fg-idempotent-ideal-idempotent-generator
These nodes are not used by the helper proofs, which use the ring-theoretic Mathlib
cancellation, finite-presentation and idempotent-ideal criteria directly. No existing
public import is removed. The unnecessary Etale.Basic import in the new localization
module was removed, as was the redundant IdempotentFG proof import in the core
module (Etale.Basic publicly includes it). No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong
The first worker's claim that substantial unavailable algebra required two open helper
proofs was too pessimistic: both helpers admit closed proofs from Mathlib ingredients.
The first delivery lacked docstring proofs, had non-self-contained new-node statements,
left the target's DAG proof route unchanged, and copied unrelated historical reviews into
new nodes. These faults are repaired. The core helper is a strict part of the target,
and the localization helper assumes the idempotent already supplied by the core; neither
is a renamed copy of the full target. Both are now proved anyway.

## Second reading by A2
1. Compared the whole existing module by diff. Its theorem signature is byte-for-byte
unchanged; only proof imports and its proof body differ. The other modules and nodes are
new. There are no definition or statement changes requiring a change record.
2. Compiled all three modules in import order with lcompile, without warnings. Searched
for forbidden declarations and sorry. There are no axioms, unsafe/opaque declarations,
foreign implementations, hollow definitions or remaining sorry. Scratch-copy #print axioms
for each theorem shows exactly propext, Classical.choice and Quot.sound.
3. Read both new statements against their full Lean signatures: arbitrary commutative
rings, independent universes, the section's R-algebra compatibility, and the corner's
specified unit and scalar map are retained. Tested the identity section (e=1, zero corner),
a projection R×T→R (e=(1,0)), and zero rings (no nontriviality needed). The general
localization result is true without étaleness. Searched with leanfinder, loogle, msearch grep,
and rg in Mathlib, lean/Sheaf and the upstream Section.lean. Upstream's product theorem
has an abstract factor, not the specified corner, and its helper uses one universe.
LeanSearch returned Internal Server Error for both queries; these attempts are recorded.
Mathlib's cancellation, kernel finite-generation, idempotent-ideal and localization
criteria suffice; both new proofs are now closed and their docstrings explain them.
4. Followed the target downward: it combines the core with the localization equivalence.
The core uses Mathlib directly, then proves the corner map bijective, avoiding redundant
scheme-form leaves. Every removed old proof dependency is listed above. The item is not
in sk-thm-p1.json's realized statement or steps, and the realized unit route is untouched.
5. Updated the target's proof/proof_deps/proof_origin to the two actual helpers. Repaired
both new nodes' self-contained statements, search records, proof routes and origins;
removed copied reviews of other declarations. Their Lean records match the signatures.

Changes in this reading: proved both helper theorems; removed two unused new-module imports;
added source/module docstrings and complete mathematical proofs; repaired all three DAG
proof records and the report. No existing statement was changed.

## New nodes
lem-weil-pbc-etale-section-idempotent-splitting-core: the proved explicit idempotent and
corner product decomposition in Sheaf.RingTheory.EtaleSectionCore.

lem-weil-pbc-etale-section-localization: the proved equivalence extending the section in
Sheaf.RingTheory.EtaleSectionLocalization. No change records are needed.
