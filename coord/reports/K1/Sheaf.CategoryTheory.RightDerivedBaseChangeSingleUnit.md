## What changed

Change record: `coord/changes/rightDerivedBaseChangeSingleUnit-proof.md` records
the tool-classified command change; public signatures and imports are unchanged.

Proved `CategoryTheory.Functor.rightDerivedBaseChange_single_unit` in
`Sheaf.CategoryTheory.RightDerivedBaseChangeSingleUnit`, with its signature unchanged.
The proof evaluates `rightDerivedFunctorPlusBaseChange_fac` on the homotopy single
complex, cancels the beta localization comparison, and uses unit naturality.
Four proved private lemmas establish identity transport, exact-functor transport,
agreement of the single comparisons, and levelwise naturality. Two private
isomorphisms are explicit constructions using fully faithful preimages; neither
chooses arbitrary data from an unproved existence theorem. The public imports are
unchanged and no proof imports were added. Updated the existing node's proof to
record the actual route. The blueprint unit's route is preserved.

## Proved and sorry left

Closed one original hole:
`CategoryTheory.Functor.rightDerivedBaseChange_single_unit`
(blueprint: `lem-sbc-right-derived-base-change-single-unit`).
No `sorry` remains in this module. No holes were added, no statements were split off,
and no declarations or target signatures were changed. All four private helper
lemmas are proved. Local compilation passes without warnings.

## No longer needed

None. Both original public imports are required by the statement. No DAG dependency
or module is pruned; the original `proof_deps` was empty and remains empty. The
proof uses the existing source-library defining equation and comparison lemmas.

## Where the brief, the DAG or earlier work was wrong

The inherited sandbox attempt contained a private holed reflexive equality named
`single_base_change_coherence`, then tried to use that equality for the different
main conclusion. That does not type-check and would not constitute a reduction.
It has been removed. The original node's canonical transport step can be simplified:
its hom is an identity in these concrete single-complex definitions, so explicit
base-change naturality across that transport is unnecessary. All comparison
coherence required by the original plan is now proved locally.

## Second reading by K1

1. **Visible declarations — pass.** Compared the delivered module with the repository
   using `diff` and checked the public signature byte for byte. The categories,
   abelian and derived-category instances, enough-injectives assumptions on B and B′,
   additivity, exactness assumptions on beta and gamma, e, Y, and both composite
   morphisms are unchanged. Only private helpers, scoped elaboration options, and
   the proof were added. Both public imports provide names appearing in the statement.

2. **Proof and data — pass.** Independently compiled the complete module cleanly
   (4.3 seconds). A scratch copy with `#print axioms` checked the public theorem,
   both private isomorphism definitions, and all four private theorems: every one
   uses only propext, Classical.choice, and Quot.sound, with no sorryAx. Scanned
   for sorry and forbidden declarations; none occur. The two isomorphisms lift
   explicit existing isomorphisms through fully faithful inclusions; their data
   do not come from an arbitrary witness of an unproved existence theorem.

3. **Split statements and edge cases — pass.** No statements are split off and
   there are no new holes or new nodes. Read each proved private helper. In the
   componentwise coherence proof, degree zero reduces to e(Y) and identity maps;
   every other degree vanishes by the single-complex comparison. This also covers
   zero objects, identity functors, and the zero transformation without imposing
   left exactness on G or G′. The identity transport is justified through the
   faithful inclusion, rather than asserted as a coherence assumption.

4. **Route and pruning — pass with inherited metadata limitation.** Read the
   defining base-change unit equation and auxiliary transformation in PlusBaseChange,
   and the definition of rightDerivedPlusSingleUnit. The proof evaluates that
   equation, cancels the beta comparison, uses unit naturality, then the gamma
   comparison. Searched the current Lean roots for single-complex coherence and
   base-change unit results, and independently queried Loogle for
   HomologicalComplex.singleMapHomologicalComplex. Loogle also suggests newer
   composition/natural-transformation lemmas absent from this machine's pinned
   Mathlib source; no available shorter replacement was found. Neither public
   import can be pruned. The old proof_deps is empty, so No longer needed is
   complete. The unit sk-prop-deg0 has empty realized statement/step lists already
   in the repository, and its referenced blueprint file is absent on this machine.
   These inherited limitations prevent checking a populated realization map;
   this delivery changes no unit record and retains the existing node-level route.

5. **DAG agreement — pass.** The only node fields changed are proof and
   proof_origin; proof_deps remains empty. Its three steps describe exactly the
   evaluated unit equation, faithful-inclusion comparison calculations, and
   naturality/cancellation used in Lean. No dependency node from the old proof
   is discarded. The node statement and recorded Lean signature are unchanged.

Second-reading changes: expanded the tool-required change record to include the
verbatim old and new public signatures, and documented the inherited unit metadata
limitation here. No repair of the Lean proof was necessary. One original hole is
closed, zero holes are added, and zero statements are split off.
