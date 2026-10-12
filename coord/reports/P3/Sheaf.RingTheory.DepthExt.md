## What changed

Proved `IsLocalRing.exists_depth_eq_ext_degree` in `Sheaf.RingTheory.DepthExt`
with its original signature and visibility, including both universes and the original
ULift Ext groups. The proof uses the existing Mathlib Rees implications, the already
proved `IsLocalRing.depth_le_supportDim`, Nakayama, and finite local Krull dimension.
It takes a maximal-length regular sequence, gets vanishing below its length, and
rules out vanishing at that length by producing an impossibly longer sequence.

Added proof-only imports `Mathlib.RingTheory.Depth.Rees` and
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`. Updated the theorem docstring and the
existing node `lem-weil-pbc-depth-ext` in `proof`, `proof_deps`, and `proof_origin`.
No definitions, statements, public imports, or other modules changed. No new nodes.

Searches: `msearch.py` LeanFinder for the depth/Ext characterization, Loogle for
`ModuleCat.exists_isRegular_tfae`, and grep for that theorem and the item name.
Also searched `lean/Sheaf`, `lean/WeilConjectures`, and pinned Mathlib directly.
The existing DAG node `lem-weil-pbc-rees-ext-regular-sequence` records the Mathlib
bridge; both constituent implications are fully proved in Mathlib.

## Proved and sorry left

Closed the sole original hole: `IsLocalRing.exists_depth_eq_ext_degree`
(node `lem-weil-pbc-depth-ext`). Holes closed: 1. Holes added: 0.
No sorry remains in the delivered module. No intermediate theorem was split off.
This is a proof, not a decomposition. The support-bound module already has a complete
proof, so this route introduces no dependency on an unproved project theorem.

Compilation with `lcompile.py` passed with no warnings. The argument covers depth
zero: its vanishing condition is vacuous, and assuming Ext zero is trivial would
force a regular sequence of length one. Universes are handled directly by the two
ULift modules in the original signature, with no Shrink transport of Ext required.

## No longer needed

Removed the proof-only import `Sheaf.RingTheory.NonzerodivisorIfMaximalNotAssociated`.
Its node `lem-weil-pbc-nonzerodivisor-if-maximal-not-associated` is no longer a direct
proof dependency of this item. The new proof also removes these planned direct DAG
proof dependencies: `lem-weil-pbc-ext-zero-hom`,
`lem-weil-pbc-ext-long-exact-second-variable`, and
`lem-weil-pbc-ext-annihilator-first-variable`. These three are Mathlib leaves rather
than separate project modules; Rees already contains its own established Ext theory.
No other existing imports were removed. The module
`Sheaf.RingTheory.DepthLeSupportDimension` remains needed.

The node is below the unit level: it is not a statement or step in
`dag/units/sk-thm-p1.json`'s `realized` lists. This shorter route leaves all of that
unit's realized statements and steps intact. No claim is made that the removed
module is globally unreachable: other items may still need it.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG's `mathlib_candidate` already points at Rees;
the new proof completes that candidate using its two general support-based
implications. This avoids the original associated-prime and quotient induction.
The source file `literature/stacks-project/algebra.tex` is absent on this machine;
the statement and source proof were read at https://stacks.math.columbia.edu/tag/00LW.
The actual shorter route was checked against the pinned Mathlib Rees source.

## Second reading by P3

1. PASS: Compared the delivered Lean file with the repository using `diff -u`,
   and separately compared the theorem signature byte for byte. The only existing
   declaration has its original signature, universes and public visibility. All
   public imports are unchanged. Changes are confined to its proof, proof docstring
   and proof-only imports; no definition or statement changed, so no change record
   or forced adaptation is required. No change record in the repository names this
   module or theorem.
2. PASS: Independently compiled the delivered file with `lcompile.py` (3.8 seconds,
   no errors or warnings). A scratch copy with
   `#print axioms IsLocalRing.exists_depth_eq_ext_degree` compiled in 3.5 seconds
   and printed exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
   Checked the whole file for forbidden declarations and attributes and for sorry:
   none occur. Read the depth definition and support-bound proof: the depth is the
   actual regular-sequence supremum, and no arbitrary object is chosen from an
   unproved existence theorem.
3. PASS: No new statements, new nodes or split-off holes. Read both Rees implication
   proofs in pinned Mathlib independently. Confirmed the vanishing implication with
   a fresh Loogle query for `ModuleCat.subsingleton_ext_of_exists_isRegular`; searched
   the project, upstream ring theory and pinned Mathlib using Ext/depth and
   regular-sequence/supremum terminology. No existing full characterization gives
   a shorter direct proof. For depth zero the empty sequence is regular because M
   is nonzero, vanishing below zero is vacuous, and vanishing at zero forces a
   sequence of length one, contradicting depth zero. The ULift linear equivalences
   preserve regularity and support, and their common universe supplies the Small
   instance required by Rees without adding a hypothesis to the signature.
4. PASS: The proof first uses established Mathlib results and the already-proved
   support bound, then obtains nonvanishing from maximality of a regular sequence.
   Both new imports are proof-only and needed (Rees and finite local Krull dimension).
   The support-bound import is used; each unchanged public import supports the
   theorem signature or depth definition. Compared old and new proof_deps: exactly
   the four dependencies listed under No longer needed were removed. Checked
   `dag/units/sk-thm-p1.json`: this item is below its realized statement and steps,
   which remain intact. No claim of global unreachability is made.
5. PASS: Parsed both node versions: only `proof`, `proof_deps` and `proof_origin`
   differ. Read all seven recorded dependencies and their Lean/Mathlib records;
   they account for Nakayama, depth, regularity, the support bound, finite local
   Krull dimension, Rees and Ext. The union of the step uses equals proof_deps.
   The four proof steps match the actual finite-supremum, ULift/support, vanishing
   and successor-length contradiction arguments. No new-node fields are needed.

Second reading changed only this report: appended the independent verification
and verdicts above. The Lean proof and DAG needed no repair. Closed holes remain
1 (`IsLocalRing.exists_depth_eq_ext_degree`); added holes remain 0.
