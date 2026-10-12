## What changed

Proved `AdicCompletion.isRegular_algebraMap_of_isDiscreteValuationRing_of_charZero`
without changing its signature. The proof obtains flatness from Mathlib's completion
instance and classifies primes using the PID theorem `IsPrime.to_maximal_ideal` and
local uniqueness of the maximal ideal. It applies two new, completely proved fibre
lemmas. All three modules compile cleanly with lcompile; the required dry run checks
the delivery separately.

The generic fibre proof uses the existing `AdicCompletion.isDiscreteValuationRing`
and the proved source-library `IsDiscreteValuationRing.isFractionRing_tensorProduct`.
It swaps tensor factors, transports characteristic zero to the zero-prime residue
field, and uses bijectivity of purely inseparable extensions to preserve the field
under the required base changes.

The closed fibre proof works for every Noetherian local ring. It constructs the
residue-field algebra equivalence using the completion evaluation quotient,
`quotIdealMapEquivQuotTensor`, and surjective scalar extension. Tensoring this
equivalence reduces every required base change to the extending field itself.

The source was checked at https://stacks.math.columbia.edu/tag/07PX and
https://stacks.math.columbia.edu/tag/0AP1; the repository's cited TeX file is not
present on this machine. The two additions are tools below the unit level, and
retain the generic and closed fibre calculations of the original route. No unit
statement or realized step is bypassed. Edge cases: DVRs are nonzero domains with
nonzero maximal ideal; mixed-characteristic DVRs are allowed; the closed-fibre
lemma has no characteristic restriction and also covers fields.

LeanFinder, Loogle, and grep searches are recorded in searches.jsonl. LeanFinder
found completion-DVR and local-residue-field infrastructure, but no exact fibre
regularity lemma. Loogle found the prime classification and quotient tensor
algebra equivalences. Grep confirmed completion flatness and evaluation quotient
APIs. LeanSearch was also attempted and returned a service error.

## Proved and sorry left

Proved the item's only original sorry:
`AdicCompletion.isRegular_algebraMap_of_isDiscreteValuationRing_of_charZero`
(node `lem-weil-pbc-dvr-completion-regular`).

Also proved both new declarations:
`AdicCompletion.isGeometricallyRegular_genericFiber_of_isDiscreteValuationRing_of_charZero`
(node `lem-weil-pbc-dvr-completion-generic-fiber`) and
`AdicCompletion.isGeometricallyRegular_closedFiber`
(node `lem-weil-pbc-completion-closed-fiber`).

No sorry remains in any module of this delivery; none was split off.
The existing imported theorem `AdicCompletion.isDiscreteValuationRing` still has
sorry and remains the next needed item, as intended for this stage.

## No longer needed

Removed the direct proof import `Sheaf.RingTheory.CompletionOfDVR` from the item's
module; it is still imported by the generic-fibre module, so is not pruned from
the target closure. No node or module is pruned.

The old direct proof dependencies replaced by the two fibre nodes are:
`lem-weil-pbc-dvr-unit-times-uniformizer-power`,
`def-weil-pbc-localization-at-prime`, `lem-weil-pbc-completion-of-dvr-is-dvr`,
`lem-weil-pbc-local-completion-local-ring`, `lem-weil-pbc-localization-base-change`,
`lem-weil-pbc-field-regular-ring`, `def-weil-pbc-finite-purely-inseparable-extension`,
and `lem-weil-pbc-tensor-over-quotient-ring`. The generic and closed fibre nodes
retain the needed proof dependencies; localization-at-prime is also a statement
dependency of both new nodes. Flatness and the regular-map definition remain direct
dependencies of the original node.

Second reading removed redundant `Mathlib.RingTheory.TensorProduct.Maps` imports
from both new modules, and `Mathlib.Algebra.Field.Equiv` from the generic-fibre
module. The APIs remain available through the necessary imports.
`Mathlib.RingTheory.AdicCompletion.LocalRing` in the closed-fibre module is now a
plain proof import: its statement's completion and local-ring notions are already
exported by `Sheaf.RingTheory.GRing`. No GRingCompletionRegular import or new
G-ring statement occurs in the delivery.

## Where the brief, the DAG or earlier work was wrong

The module originally imported only CompletionOfDVR for proof support; most other
planned steps were Mathlib leaves. The source library already contains a complete
fraction-field base-change proof specialized to DVR maps with matching maximal
ideals, eliminating the need to rewrite the elementwise uniformizer argument.
The quotient-tensor leaf was recorded as a module-linear equivalence; the fibre
calculation needs its Mathlib ring-algebra counterpart, used here directly.
No statement correction was needed.

## New nodes

`lem-weil-pbc-dvr-completion-generic-fiber`, in
`lean/Sheaf/RingTheory/DVRCompletionGenericFiber.lean`, isolates and proves the
generic fibre calculation (old steps 3–5), using the existing completion-DVR
statement. It introduces no sorry.

`lem-weil-pbc-completion-closed-fiber`, in
`lean/Sheaf/RingTheory/CompletionClosedFiber.lean`, isolates and proves the closed
fibre calculation (old step 6) in the generality of Noetherian local rings.
It introduces no sorry. No change records are needed.

## Second reading by S2

1. Compared every delivered module with the repository. Only the original module
   exists there; its sole theorem signature is byte for byte unchanged (also
   confirmed with the delivery signature parser). There is no changed definition,
   target, or existing public import, and no change record is needed. Verdict: pass.
2. Read all three proofs and compiled the complete set in import order, without
   errors or warnings. No delivered module contains `sorry`, an axiom, unsafe code,
   an opaque declaration, an external implementation, or a hollow definition.
   A scratch-copy `#print axioms` check gives only `propext`, `Classical.choice`,
   and `Quot.sound` for the closed fibre. The generic fibre and original theorem
   additionally use `sorryAx` through the existing, explicitly retained
   `AdicCompletion.isDiscreteValuationRing`. Verdict: pass as a reduction to that
   still-open upstream theorem; no claim of a fully axiom-free target closure.
3. Both new statements are proved, not sorry splits or restatements of the item.
   Checked the scalar structures and direction of each tensor/ring equivalence.
   The generic argument permits mixed characteristic and obtains characteristic
   zero of the zero-prime residue field from the given fraction field. The closed
   argument covers fields and all residue characteristics, and actually works for
   every field extension, so finite purely inseparable extensions cause no gap.
   Docstrings give complete natural-language arguments and matching source/node
   references. Fresh LeanFinder, Loogle, and grep searches with different queries,
   plus repository searches, found supporting APIs but no existing theorem that
   replaces these fibre statements. Read the proved upstream fraction-field tensor
   lemma, including its uniformizer/injectivity argument. Verdict: pass.
4. The top-level proof uses flatness, PID prime classification, and the two fibre
   calculations directly. There is no shorter exact library result found by the
   searches. Checked `dag/units/sk-thm-p1.json`: the item and new helpers are below
   its realized steps, and no realized statement, step, or cited unit is bypassed.
   The original completion-DVR module stays in the import closure. Enumerated all
   replaced old direct dependencies above, and removed redundant imports.
   Verdict: pass; no node or module pruned.
5. Read all three nodes against their Lean declarations and proofs. Their
   `proof_deps` are exactly the unions of their proof-step `uses`; source origins,
   new-node ownership, blueprint provenance, chapter, unit, and verbatim Lean
   signatures agree. Existing fields outside stage-3 ownership are unchanged.
   Mathlib leaves record the infrastructure used directly (the quotient-tensor
   ring-algebra API is the counterpart needed here). Verdict: pass.

Second reading changed only import hygiene and reporting: removed three redundant
proof imports, changed the new closed-fibre module's proof-only LocalRing import
from public to plain, and made the old dependency replacement list explicit.
The mathematical proofs and theorem signatures were retained.
