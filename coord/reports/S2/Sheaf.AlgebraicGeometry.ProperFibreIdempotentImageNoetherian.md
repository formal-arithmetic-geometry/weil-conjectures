## What changed

Proved the body of `AlgebraicGeometry.proper_fibre_idempotent_image_noetherian`
from formal functions and one new intermediate theorem, with its existing signature
and docstring unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.FormalFibreIdempotentLimit`.

Two private helpers are fully proved: `formalFibreZero_iso` identifies the zeroth
formal fibre with the usual fibre, preserving the projection to X;
`completion_image_mod_one` proves the general linear descent argument from a
completion to a module killed by the ideal. The main proof verifies the quotient
scalar action, uses the Noetherian stalk instance, takes a section representative
of a germ, and transports the restriction equality through the fibre isomorphism.
Updated the original node's proof and dependencies to match this argument.

Both delivered modules compile with lcompile.py without errors or warnings.
The Stacks source was verified online at https://stacks.math.columbia.edu/tag/0G7X
because this clone contains only the literature index, not the downloaded TeX.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.proper_fibre_idempotent_image_noetherian`
(node `lem-weil-pbc-stein-fibre-idempotent-image-noetherian`).

Added one hole, the whole proof of the public named theorem
`AlgebraicGeometry.formalFibre_idempotent_limit`
(node `lem-weil-pbc-formal-fibre-idempotent-limit`), in its own new module.
It states only the infinitesimal lifting/compatibility step: an idempotent on X_0
has a lift to the inverse limit. It asserts no neighborhood section, stalk element,
formal-functions comparison, completion descent, properness or Noetherian assumption.
Its source and complete proof in words are in the docstring and node.

This is a decomposition, not a fully sorry-free proof: one hole closed, one added,
net zero for these delivered declarations. The existing
`AlgebraicGeometry.formal_functions_stalk` sorry is still an upstream dependency;
this delivery neither adds nor changes it. There is no sorry in either private
helper, the main proof, or any definition.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.NilpotentBaseChangeIdempotents` from the item's module;
it remains imported by the new infinitesimal-lifting module and remains needed
in the closure. Its node
`lem-weil-pbc-base-change-nilpotent-thickening-idempotents` is replaced as a direct
proof dependency by the new lifting node, not pruned from the mathematical route.

The standalone planned node `lem-weil-pbc-localization-noetherian` is not needed
as an explicit proof dependency: Mathlib's locally-Noetherian stalk instance in
`Mathlib.AlgebraicGeometry.Noetherian` directly supplies the Noetherian local ring.
There is no Sheaf module for that Mathlib leaf to remove. No other planned module
is pruned; formal functions and completion completeness remain essential.

## Where the brief, the DAG or earlier work was wrong

The earlier core asserted that the neighborhood section is idempotent, which is
false without a henselian hypothesis (the earlier double-cover counterexample
applies). This attempt keeps the original conclusion and only descends the fibre
image. The earlier rejected material remains in scratchpad, outside the delivery.

The plan's infinitesimal lifting is not directly expressible by one application
of `nilpotent_baseChange_idempotents`: the available declaration uses a different
pullback presentation and requires quotient-ideal/pullback identifications plus
inverse-limit compatibility. Those precise missing steps are the new theorem.
The other three steps of the original route are now Lean proofs. The unit record
`sk-thm-p1` and all of its realized steps are unchanged.

Edge cases checked mathematically: the new intermediate works for e=0 and e=1,
empty fibres, non-Noetherian bases and nonproper morphisms, since nilpotence of
m/m^(n+1) holds without these assumptions. No nonempty clopen piece is required.
The linear descent helper also works for I=0, the zero module and the unit ideal
(the annihilated target is then zero). The previous false idempotent-section
conclusion is absent from all delivered signatures.

## New nodes

`lem-weil-pbc-formal-fibre-idempotent-limit` / module
`Sheaf.AlgebraicGeometry.FormalFibreIdempotentLimit`: the compatible infinitesimal
lifting step of Tag 0G7X. It is strictly a part of the argument and has no properness
or Noetherian assumptions. It depends on the existing formal-fibre definitions
and nilpotent-base-change idempotent theorem. No interface correction, change
record or forced adaptation is needed.

## Second reading by S2

Independent second reader; the author of this review did not write the delivered proofs.

1. PASS: compared both delivered modules with the repository. The sole existing
   public declaration has exactly its original signature, visibility and docstring.
   Its only interface-adjacent change is a plain proof import replacing a plain
   proof import. No definition, target, existing public import or other module is
   changed; no change record is required.
2. PASS: independently compiled both modules in import order with lcompile.py
   (3.7 s and 7.6 s; no errors or warnings). A scratch copy with #print axioms
   checked both private helpers, the main theorem and the split theorem. The
   helpers use only propext, Classical.choice and Quot.sound. The two public
   theorems additionally use sorryAx, as expected from the listed lifting hole
   and upstream formal functions. The only textual sorry delivered is the body
   of formalFibre_idempotent_limit. There is no hollow definition, arbitrary
   witness definition, or forbidden axiom/implementation command. Removed the
   scratch probe after checking.
3. PASS: read the lifting theorem against the actual formal-fibre definitions,
   transitions, and nilpotent_baseChange_idempotents. It is true without
   properness or Noetherianity: the quotient ideal is nilpotent, idempotent lifts
   are unique, and uniqueness gives transition compatibility. Its docstring
   supplies all mathematical steps and its new node matches the statement.
   Checked n=0, e=0, e=1, empty fibres, and non-Noetherian/nonproper cases; none
   require nonempty clopen pieces. The statement is strictly the infinitesimal
   part of the original argument, not a restatement of the neighborhood-section
   conclusion. Repeated LeanFinder search using “compatible global sections on
   nilpotent infinitesimal thickenings” and searched Mathlib algebraic geometry,
   lean/Sheaf and lean/WeilConjectures for clopen/idempotent/formal-limit results.
   No exact existing theorem was found. The quotient/pullback identifications
   needed to finish this hole are substantial; no few-minute closure was found.
4. PASS: read the main reduction top downward. The zero-fibre isomorphism
   preserves projection to X; completion descent uses Mathlib's kernel/evaluation
   theorem for finitely generated ideals; the maximal ideal kills the target;
   the formal-functions germ equation and appLE composition give exactly the
   original restriction equation. Imports serve statement types or the actual
   proof/planned split proof. The old direct dependencies removed are exactly
   localization-noetherian and nilpotent-base-change-idempotents, both accounted
   for above. The latter remains in the closure. No whole module is pruned.
   Read sk-thm-p1.realized: the unit route is unchanged. Verified the source
   paragraph at https://stacks.math.columbia.edu/tag/0G7X independently.
5. PASS: compared the existing node with the repository: only proof,
   proof_deps and proof_origin differ. The listed dependencies are the union of
   the proof steps' uses and match the Lean reduction. Checked all required
   new-node fields, its source, searches, chapter, unit, blueprint ancestry,
   lean record and the complete docstring proof. No new unsupported notion or
   changed mathematical statement is hidden in the metadata.

Second-reading changes: added this independent review and verification evidence
only. The Lean proofs and node records needed no repair. This remains a
one-for-one decomposition (one original hole closed, one hole added), net zero;
it is not a completed sorry-free proof.
