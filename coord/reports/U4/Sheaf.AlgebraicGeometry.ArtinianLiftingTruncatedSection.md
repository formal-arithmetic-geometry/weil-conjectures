## What changed

Proved `Algebra.artinian_lifting_truncated_section` with its exact original signature.
The proof constructs the quotient rings, proves they are Artinian local using nilpotence
of their maximal ideals, constructs the map from the localization to the larger quotient,
lifts the map from A, localizes that lift, and descends it to an R-algebra section.
The final section identity is checked on quotient representatives.

Added `Sheaf.AlgebraicGeometry.ArtinianLiftingFiniteKernel`, containing the proved theorem
`Algebra.artinian_lifting_finite_kernel` and the proved private kernel-length helper.
Its proof uses the existing ideal filtration theorem, with a descending induction written
in Lean. It explicitly transports length-one tests through ULift ring equivalences and
checks kernel length by a linear quotient equivalence and restriction of scalars.
Proof imports are private. Updated the original DAG node and added the node for this
reusable lifting theorem. No existing statement, definition, or public import changed.

Both modules compile together through lcompile.py, with no warnings. The edge cases
N=1, J=0 and zero kernel are included: properness uses N>=1, and an empty filtration is
handled by Fin.reverseInduction at its last index. No data is defined using an unproved
existence theorem; all maps obtained from the filtration are within a theorem proof.

## Proved and sorry left

Closed the one original hole, `Algebra.artinian_lifting_truncated_section`
(node `lem-weil-pbc-artinian-lifting-truncated-section`).
Also proved `Algebra.artinian_lifting_finite_kernel`
(node `lem-weil-pbc-artinian-lifting-finite-kernel`) and private `factor_kernel_length`.
No holes added; no sorry remains in either delivered module. This is a proof from an
existing stated dependency, not a decomposition into new unfinished statements.

The existing dependency `Module.exists_simple_filtration_of_length_lt_top` in
`Sheaf.RingTheory.SimpleFiltration` still contains its pre-existing sorry. It is reached
through `RingTheory.exists_ideal_filtration_length_one`, which the new theorem uses.
This delivery does not change that dependency or claim a sorry-free transitive closure.

## No longer needed

Removed `Mathlib.RingTheory.Ideal.KrullsHeightTheorem` from the main module.
The proof does not need node `lem-weil-pbc-noetherian-local-quotient-artinian-local`:
Noetherian quotient instances plus the explicit vanishing of the maximal-ideal power
and `isArtinianRing_iff_isNilpotent_maximalIdeal` give the needed structures directly.
There is no separate Sheaf module attached to that Mathlib leaf to remove.

Replaced the main module's direct import of
`Sheaf.Paper.ArtinianIdealLengthOneFiltration` with
`Sheaf.AlgebraicGeometry.ArtinianLiftingFiniteKernel`. The filtration node and module
remain needed through the new module; they are not pruned from the transitive closure.
The localization and local-unit nodes remain direct dependencies.
The old direct dependency `def-weil-pbc-module-length` is no longer used directly
by the main proof; it remains needed through the finite-kernel theorem.
Removed the redundant proof imports `Mathlib.Order.Fin.Basic` and
`Mathlib.Algebra.Ring.ULift` from the new finite-kernel module during second reading;
the needed Fin and ULift declarations are already available through its other imports. No unit statement
or realized step in `dag/units/sk-thm-p1.json` is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement change. The earlier plan's Artinian-quotient route
through minimal primes was unnecessary; the nilpotent-maximal-ideal criterion is enough.
The existing blueprint-ancestor tool returns None for this item because its created.item
chain contains Lean module names. The new node records the imported finite-etale-lifting
ancestor already used by the surrounding Artinian criterion nodes, with the precise
filtration step and its intervening nodes. The original blueprint fields were preserved.

## New nodes

`lem-weil-pbc-artinian-lifting-finite-kernel` records the fully proved finite-kernel
extension of the length-one test, in `ArtinianLiftingFiniteKernel.lean`. Source: Stacks
Tag 02HT, proof of (4) implies (1), the kernel filtration and successive lifts. The
recorded LeanFinder and Mathlib grep searches found no exact theorem; LeanSearch returned
Internal Server Error and is recorded as unavailable. Searches of WeilConjectures,
Sheaf and the imported blueprint found no duplicate statement. No change record is
needed because the existing interface and all target statements are unchanged.

## Second reading by U4

1. Compared the existing module and node with their repository versions. The original
   theorem signature is byte for byte unchanged, and every existing public import is
   preserved. No definition, target statement, visibility, or other module is changed.
   The existing node changes only its proof, proof dependencies and proof origin.
   Verdict: pass; no change record is required.
2. Compiled both modules together locally without errors or warnings. Searched both
   delivered files for sorry, axiom, unsafe, opaque, implemented_by and extern: none.
   Printed axioms in scratch copies for both public theorems and the private
   factor_kernel_length helper. The helper uses only propext, Classical.choice and
   Quot.sound; the public theorems additionally use sorryAx through the unchanged
   Module.exists_simple_filtration_of_length_lt_top dependency. There are no hollow
   definitions or arbitrary witnesses chosen into public data. Verdict: pass for
   closing the original hole from the existing stated dependency, not a claim that
   its transitive closure is proved.
3. No unfinished statement was split off. Read the new proved finite-kernel theorem,
   its docstring, node, ULift transport, quotient-kernel equivalence, and descending
   induction. Zero kernel permits a zero-step filtration; bijective quotient maps
   are handled by actual inverses. Properness follows from the kernel lying in the
   maximal ideal, so no zero-ring quotient is silently admitted. Checked N=1 and J=0
   in the original theorem: its quotient section is the identity in these cases.
   Repeated searches with a composition-series lifting query in LeanFinder, a
   kernel/length Loogle query, and composition-series/length grep, plus searches of
   both Lean roots: no duplicate finite-kernel lifting theorem was found. Existing
   composition-series results do not supply the ring-map lifting induction.
   Verdict: pass; the added theorem is proved, not a restatement left unfinished.
4. Reviewed the proof from the truncated-section target downward. Direct Mathlib
   quotient/localization tools close the quotient properties and final descent;
   the one pre-existing filtration dependency supports the finite induction.
   Checked sk-thm-p1.json realized: no realized statement or step is bypassed.
   The pruning list now explicitly accounts for every removed old direct proof
   dependency, including module length, which remains an indirect dependency.
   Tested removal of the main quotient-Noetherian import: it is required to
   synthesize Noetherian quotient instances. Tested and removed the new helper's
   redundant Fin.Basic and Ring.ULift imports. Verdict: pass.
5. Checked both node statements against the Lean signatures and each proof step
   against its implementation. The proof_deps lists are the unions of step uses;
   the new node supplies its source, proof origin, searches, creation record,
   blueprint ancestry, chapter, unit and verbatim Lean statement. The existing
   node retains its statement and blueprint fields. Verdict: pass.

Second reading changed only the two redundant proof imports and this report's
pruning accounting and review section. No mathematical proof needed repair.
