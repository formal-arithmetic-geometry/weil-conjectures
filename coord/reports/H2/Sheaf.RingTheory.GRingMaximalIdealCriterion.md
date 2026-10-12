## What changed

The signature and existing docstring of `isGRing_iff_maximalIdeal` are unchanged.
Its forward implication uses the definition of `IsGRing`. For the converse,
the proof obtains a flat local comparison map, completes it using
`flat_adicCompletion_of_flat_local`, proves that the induced completion map
is local, obtains faithful flatness and spectrum-surjectivity from Mathlib,
and applies `RingHom.isRegular_of_isRegular_comp`.

The first worker's `GRingMaximalIdealCriterionPrime` module and
`lem-weil-pbc-g-ring-maximal-ideal-criterion-prime` node were removed before
delivery. The replacement module is
`Sheaf.RingTheory.GRingMaximalIdealComparison`, with a theorem constructing
a Noetherian local comparison ring B and a flat local map R_p → B whose
composite with B → Bhat is regular. This packages only steps 2–7 of the
original plan, leaving steps 8–9 as a real reduction in the item's proof.

Added proof-only imports `Sheaf.RingTheory.GRingMaximalIdealComparison` and
`Mathlib.RingTheory.AdicCompletion.LocalRing`. All public imports are unchanged.
The existing node's proof, proof_deps and proof_origin now describe the Lean
argument; no statement, definition or change record is changed or required.

## Proved and sorry left

`isGRing_iff_maximalIdeal` has a complete Lean proof from named dependencies,
with no direct `sorry` (1 of the item's 1 original declarations closed).
The single new named open theorem is
`exists_flat_local_regular_completion_comparison`, in
`Sheaf.RingTheory.GRingMaximalIdealComparison`, recorded by
`lem-weil-pbc-g-ring-maximal-ideal-comparison`. Its body is exactly `by sorry`.
Its docstring gives the complete construction and regular-composition argument
from Stacks Tag 07PT, without assuming the criterion itself.

The item still rests transitively on that open theorem and the existing
`flat_adicCompletion_of_flat_local` and
`RingHom.isRegular_of_isRegular_comp` theorems. Thus this is a partial stage-3
delivery, not a claim that the result is free of all pending proof obligations.
Scratch `#print axioms` checks for both delivered declarations returned only
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.

## No longer needed

Removed unused proof imports from the item's module:

- `Sheaf.RingTheory.AdicCompletionNoetherian`
- `Sheaf.RingTheory.CompleteLocalGRing`
- `Sheaf.RingTheory.LocalizationRegular`
- `Sheaf.RingTheory.RegularComposition`
- `Sheaf.RingTheory.RegularThroughLocalization`

The following old direct proof dependencies are now used within the comparison
construction's plan rather than directly by the item's Lean proof:

- `lem-weil-pbc-flat-local-ring-maps`
- `lem-weil-pbc-adic-completion-noetherian`
- `lem-weil-pbc-adic-completion-mod-ideal`
- `lem-weil-pbc-local-completion-faithfully-flat`
- `lem-weil-pbc-complete-local-g-ring`
- `lem-weil-pbc-localization-regular`
- `lem-weil-pbc-regular-composition`
- `lem-weil-pbc-regular-through-localization`

These nodes remain needed for the comparison construction: none is claimed to
be globally unreachable or removable. The first worker's unpublished prime
restatement node and module are discarded entirely. An attempted direct import
of `Mathlib.RingTheory.Localization.Submodule` was unnecessary and removed;
removing `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` also compiled, so it
was removed. Removing `Mathlib.RingTheory.AdicCompletion.LocalRing` failed
because the completion local-ring instances were then unavailable.

## Where the brief, the DAG or earlier work was wrong

The first worker's new prime-local theorem moved essentially the entire
converse into one open statement. Its node's proof_deps included the original
criterion, creating a circular argument, and its docstring did not provide the
required full proof in words. Its report also failed to list the old direct
proof dependencies removed from the original node, and retained unused imports.

The replacement separates the comparison construction from completion and
regular descent. Its plan has no dependency on the original criterion, either
directly or through its dependency closure (541 nodes checked). The original
nine-step mathematical route remains sound and is retained.

## New nodes

`lem-weil-pbc-g-ring-maximal-ideal-comparison` constructs the flat local
comparison map and proves regularity of its composite with the comparison
completion, following the diagram and initial argument in Stacks Tag 07PT.
Its Lean module is `lean/Sheaf/RingTheory/GRingMaximalIdealComparison.lean`.
It has a complete docstring proof, verbatim Lean signature, source, parent
blueprint link, creation information, and proof steps whose uses union is its
proof_deps. Independent LeanFinder, Loogle and Mathlib/source/Sheaf searches
found related flat-localization APIs but no existing comparison construction;
LeanSearch returned an Internal Server Error, recorded as unavailable without
a mathematical verdict. No change record is needed.

## Second reading by H2

1. Compared the item's module to the repository with `diff`. The only changes
   are its proof body and ordinary imports; the theorem signature is byte for
   byte unchanged, and its existing docstring is unchanged. The sole new module
   states a new construction theorem. No existing definitions or statements,
   target signatures or public imports changed. Verdict: pass.
2. Compiled both modules through `lcompile.py` in import order, with no errors
   or warnings after repairs. There is exactly one `sorry`, the named comparison
   theorem listed above, and no forbidden declarations or implementation escapes.
   Scratch copies with `#print axioms` showed only the allowed three axioms and
   `sorryAx` from documented pending dependencies. Verdict: pass for a partial
   stage-3 delivery.
3. Read the comparison construction against the proof of Tag 07PT in the local
   Stacks source. In the zero ring there is no prime to supply, so the claim is
   vacuous. When p is maximal (including the field case), B = R_p and φ = id
   already witness it using the hypothesis. For arbitrary p, the faithfully
   flat completion supplies the required prime above pR_m, and the localization
   and regular-composition argument gives precisely the promised witness.
   Localization and completion preserve universe w. The theorem does not assume
   or assert regularity of R_p's own completion, and the target explicitly
   establishes that by flat completion and descent. Its complete docstring and
   node meet the split-off requirements. Searched with fresh conceptual wording
   and with `rg` on Mathlib, the adopted source and lean/Sheaf. No duplicate was
   found; closing the construction is not a short Mathlib application.
   Verdict: pass after replacing the restatement.
4. The forward direction takes the shortest definitional route; the converse
   uses the existing flat-completion and regular-permanence declarations and
   Mathlib's local and faithfully-flat tools. Pruned the five unused original
   proof imports and the two redundant trial imports. `No longer needed` lists
   every removed original direct proof dependency and explains its relocation.
   Checked `dag/units/sk-thm-p1.json` realized: neither this item nor the replaced
   lower-level dependencies is a unit realization, and no realized node or unit
   route is bypassed or changed. Verdict: pass.
5. Read both delivered node files alongside their Lean modules. The original
   node describes the actual completion/descent proof; the new node describes
   the open construction. Both proof_deps lists are exactly the union of their
   proof-step uses. The new node has the required stage-3 fields, matching Lean
   signature, parent, unit and chapter. Its proof dependency closure never
   returns to the criterion. Verdict: pass after repairing the circular node.

Second reading changed: replaced the prime-local restatement with the comparison
construction and a real completion/descent proof; supplied its full docstring
proof and node; removed unused imports; repaired proof dependencies and pruning
records; recorded fresh searches and the unavailable LeanSearch service.
