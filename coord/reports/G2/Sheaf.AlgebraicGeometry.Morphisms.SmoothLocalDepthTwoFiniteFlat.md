## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.flat_of_smooth_local_depth_two_finite_extension`
by a compiling proof with the original signature unchanged. Added two proof-only imports:
`Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatTargetLocus` and
`Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat`.

The finite target flat locus is proved from the upstream Noetherian ring flat-locus
calculation, stalk-map isomorphisms, affine restrictions, and closedness of finite maps.
The main proof establishes that this locus contains U, takes its closed complement in
the Jacobson closed fibre, rules out every closed point using the local completion
calculation, and uses the stalk criterion to obtain global flatness. All three modules
compile cleanly together. The new flat-locus theorem has exactly propext, Classical.choice,
and Quot.sound as its printed axioms.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.flat_of_smooth_local_depth_two_finite_extension`
(node `lem-sbc-smooth-local-depth-two-finite-flat`). No sorry remains in the item's module.

Also proved the new supporting theorem:
`AlgebraicGeometry.Scheme.isOpen_setOf_finite_flat_stalks`
(node `lem-sbc-finite-flat-target-locus`), including its three private helpers.

Added exactly one hole:
`AlgebraicGeometry.Scheme.flat_stalk_of_smooth_local_depth_two_closed_fiber`
(node `lem-sbc-smooth-local-depth-two-closed-fiber-flat`). Its proof is exactly `by sorry`.
It concerns one specified source stalk over one specified closed boundary point of the
closed fibre. The global bad-locus and Jacobson argument is outside this statement and
is proved in the main module. This is a decomposition (one upper hole closed, one lower
hole added), not a claim to a net decrease in holes or a completed purity proof.

## No longer needed

None. No existing import, node or module was removed. The original node had no
proof-dependency nodes to prune. No finite etale extension is chosen from an unproved
existence theorem and no additional existence/construction module is imported.

## Where the brief, the DAG or earlier work was wrong

The original DAG supplied one long formal-completion paragraph with empty uses and
proof_deps, rather than declarations for its numbered ingredients. The source theorem
is true, and no statement correction or forced adaptation was needed. The existing
normalization section-flat lemmas assume normality, a Galois cover, or a section and
do not apply to this arbitrary supplied finite extension.

Read Stacks Tags 0EYB and 0EYA directly. The closed-point computation is now separated
from global flatness. Edge cases checked: empty E makes the locus universal; U = L
has no bad points; a non-quasi-compact L is covered by the affine-neighbourhood proof;
relative dimension zero at a missing closed fibre point contradicts density. Finite
flat local base changes and section-ideal completion are faithfully flat where descent
is used. The unit's depth-two/completion route is retained.

The blueprint ancestor tool returns None because existing created.item links use module
names. New nodes retain the explicit valid ancestor of the item's existing blueprint
record, sbc-thm-spreading-finite-etale-galois. Blueprint searches for closed/fibre/flat,
finite/flat, and Tag 0EYB found no duplicate statement. Mathlib searches are logged;
LeanSearch was unavailable. The upstream ring theorem is a closed generic tool from
lem-weil-pbc-noetherian-flat-locus-neighborhood; the integral closedness input is the
Mathlib leaf pqf-lem-integral-univclosed. Neither changes the unit route.

## New nodes

`lem-sbc-finite-flat-target-locus`: the generic target flat locus for a finite morphism
over a locally Noetherian scheme. New module FiniteFlatTargetLocus; completely proved.
The source-level locus is treated affine locally, then its closed complement is sent
through the finite closed map.

`lem-sbc-smooth-local-depth-two-closed-fiber-flat`: the closed-boundary-point formal
calculation from Tag 0EYB, in SmoothLocalDepthTwoClosedFiberFlat. One public named
sorry with a source and a full proof in words; no global flatness assertion.

No change records: no existing statement, definition, or public import changed.


## Earlier second reading (a previous round; superseded)

1. **Interfaces: pass.** Compared the delivered main module with the read-only
   repository using diff and compared its existing theorem signature byte for byte.
   Only its proof body and two plain, proof-only imports changed. No existing
   definition, signature, docstring, public import, or target changed. The two
   supporting modules are new. No change record is needed; no pending record in
   coord/changes names these modules or the original declaration.
2. **Kernel checks: pass as a decomposition.** Compiled all three modules together
   through lcompile.py, without errors or warnings. In scratch copies, printed
   axioms for the original theorem, both new public theorems and all three private
   helpers. The target-flat-locus theorem and helpers use only propext,
   Classical.choice and Quot.sound. The original theorem and the local
   closed-fibre theorem additionally use sorryAx, exactly as reported. The only
   remaining sorry is the public named theorem
   AlgebraicGeometry.Scheme.flat_stalk_of_smooth_local_depth_two_closed_fiber.
   There are no forbidden declarations and no definitions choosing arbitrary
   data from an unproved existence assertion.
3. **Split statement: pass.** Independently read Stacks Tags
   [0EYB](https://stacks.math.columbia.edu/tag/0EYB),
   [0EYA](https://stacks.math.columbia.edu/tag/0EYA) and
   [0EY6](https://stacks.math.columbia.edu/tag/0EY6).
   The remaining statement is precisely the closed-boundary-point formal
   calculation, with its source, full proof in words and matching node. It
   proves one local ring map flat at a specified closed-fibre point; openness,
   finite closedness, the Jacobson closed-point argument and assembly of global
   flatness are actually proved separately. This is strictly a part of the
   argument, rather than the original global conclusion under another name.
   Checked empty E, U = L, empty closed fibre, the relative-dimension-zero
   contradiction with density, and the absence of a quasi-compactness assumption
   on L. Flat local base changes preserve the required depth and permit descent;
   the completed supplied finite extension is identified by uniqueness in 0EY6.
   Independent LeanFinder query "flat local ring map at a closed point finite
   cover smooth scheme purity depth" returned smooth-chart/locus results only;
   Loogle "IsOpen, Module.Flat" returned no hits. The earlier Loogle query
   "IsFinite, Flat" could not resolve IsFinite and was not counted as evidence.
   Mathlib grep "flat.*closed|closed.*flat|isOpen.*stalk" and rg across both
   library roots found no duplicate. Existing normalization section-flat results
   have extra hypotheses and do not close this hole. Formalizing the completion
   calculation is substantial work, not a missing short library application.
4. **Route and pruning: pass.** Read the finite target-flat-locus proof from
   affine stalk-map transport through the upstream proved ring flat-locus
   theorem, affine restriction, and finite closedness. Its upstream import is
   proof-only; the new main-module imports are proof-only and both are used.
   No old dependency can be pruned: the original proof_deps is empty. Read
   sk-prop-input-spreading's written completion/depth-two step and checked that
   this delivery retains it, using generic flat-locus tools below the unit level.
   The repository unit's realized statement and step arrays are already empty;
   there is no existing node mapping to preserve or bypass there. This metadata
   limitation predates the delivery and has not been repaired by changing the
   unit, which is outside the delivery scope.
5. **DAG: pass.** The existing node changes only proof, proof_deps and
   proof_origin. Its new dependencies match the two actual proof imports.
   Each new node has the required source, statement dependencies, proof steps,
   origin, searches, status, creation, blueprint ancestry, chapter/unit and Lean
   records. All three lean.statement strings match the delivered declarations
   verbatim, and dependencies resolve in the library plus this delivery. The
   flat-locus node accurately records its upstream Noetherian flat-locus input
   and finite closedness input; the local node records the remaining sourced
   formal calculation.

Second-reading changes: appended this independent review and its search/axiom
checks to report.md. No Lean or node repair was needed. One original hole is
closed syntactically and one strictly local hole is added: net zero, a
one-for-one decomposition, with no claim of a completed purity proof.

## Second reading by G2

1. **Interfaces: pass.** Independently diffed the main module against the repository
   and checked its existing theorem signature byte for byte. Only the proof and two
   plain proof-only imports changed. Both supporting modules are new; no existing
   statement, definition or public import changed. No change record is required,
   and the repository changes directory has no record naming these declarations.
2. **Proof and axioms: pass as a decomposition.** Compiled all three delivered
   modules in import order through lcompile.py, with no errors or warnings.
   Scratch copies printed axioms of all three public theorems and the three
   private flat-locus helpers. The flat-locus theorem and helpers use only
   propext, Classical.choice and Quot.sound. The original theorem and the
   closed-fibre theorem additionally use sorryAx, corresponding to the single
   reported named hole. No forbidden declaration or hollow definition occurs.
   The main audit initially could not find the sandbox imports from its scratch
   directory; recompiling its scratch copy under the sandbox Lean root resolved
   the imports and confirmed the expected axiom list.
3. **Split statement: pass.** Read Stacks Tags 0EYB, 0EY6 and 0EYA independently.
   The new hole is the specified closed-boundary-point completion calculation;
   its docstring gives the residue-field base change, section, positive relative
   dimension, power-series extension, uniqueness and faithful-flat descent.
   It is strictly a local part of the argument: the global bad-locus argument is
   proved in Lean. Checked empty E, U = L, empty closed fibre, relative dimension
   zero, and non-quasi-compact L. No arbitrary witness from an unproved theorem
   is used to define data. Independent LeanFinder search for "depth two boundary
   stalk flat finite extension formal power series" returned stalk criteria and
   Weierstrass tools, not this statement. Loogle "Module.Flat,
   Localization.AtPrime" returned localization and smooth-fibre tools only.
   Mathlib grep "completion.*flat|flat.*completion|finite.*flat.*locus" found
   flatness of adic completion, which does not supply the missing finite-cover
   extension argument. Repository rg found no applicable duplicate; existing
   normalization section-flat lemmas require additional Galois/section data.
   Closing this hole requires substantial formalization, not a short application.
4. **Route and pruning: pass.** Read every proof in the flat-locus module and the
   global assembly. The upstream ring flat-locus theorem is used proof-only;
   affine restriction and finite closedness give exactly the target locus used
   by the main proof. Both added imports are used. The original proof_deps was
   empty, so "No longer needed: None" is complete. Read the unit's recorded
   depth-two/completion step; this delivery preserves that route and uses only
   generic tools below it. The unit's realized arrays are already empty in the
   repository; no existing mapping is removed or bypassed. The referenced
   literature blueprint directory is absent on this machine, so the complete
   unit text stored in dag/units/sk-prop-input-spreading.json was read instead.
5. **DAG: pass.** Verified that the existing node changes only proof, proof_deps
   and proof_origin. All three lean.statement strings match their declarations
   verbatim, each proof_deps equals the union of proof-step uses, and every
   statement/proof dependency resolves. New nodes have the required provenance,
   searches, creation, source, blueprint ancestry, chapter/unit and Lean fields.
   Their proof descriptions agree with the implemented reduction and open hole.

Changes in this reading: appended this independent review and fresh search/axiom
checks. No Lean or node repair was needed. One original hole closed and one local
hole added: net zero, a decomposition; the new flat-locus tool is fully proved.
