## What changed

Repair of the returned duplicate-theorem finding: replaced the private
`depth_le_of_semilinear_equiv` with `depth_eq_of_semilinear_equiv`.
The new helper proves equality rather than only an inequality. It transports regular sequences in both
directions, proving inverse semilinearity explicitly. Both the base-ring depth
transport and the module-stalk depth transport now use this stronger helper;
the separate private `depth_equiv` proof is removed. No new hole is added.
The earlier second-reading record below is preserved from the returned delivery.
The new independent second reading at the end reviews this repaired version.

Replaced the single sorry in `AlgebraicGeometry.Scheme.affine_depth_two_pushforward_hull`
by a complete Lean assembly from an affine coherent model, open-base-change comparisons,
and the existing Hartogs algebra comparison. Its statement and visibility are unchanged.
All original public imports are retained. Proof imports add finite local freeness under
pullback, the affine section functor, the module stalk functor, and the three new modules.

The proof obtains finite local freeness from
`Modules.isFiniteLocallyFree_pushforward`, transports the base-ring depth across the
open chart's stalk ring equivalence, and applies the new general affine model theorem.
It explicitly builds the restriction isomorphism required by
`depth_two_hartogs_algebra_comparison`, applies that theorem to the base-changed cover,
and transports quasi-coherence, finite affine sections, and finite depth-two stalks
along the resulting module isomorphism. Finiteness uses linear maps over precisely
the stated rings. A proved private helper transports depth using regular sequences
and the maximal-ideal submodule, rather than assuming an additive equivalence is linear.

Two new comparison theorems are proved completely. The open-direct-image comparison
uses equality of the two opens on which sections are evaluated, the cartesian square
for scalar compatibility, and presheaf functoriality for naturality. The structure-module
comparison pastes two pullback squares, uses the first projection's open-immersion
section isomorphism, and proves linearity and naturality explicitly.

Compilation: `lcompile.py --all` compiles the four modules in import order. The delivery
dry run also performs its declaration/axiom probes and the stage-3 preflight.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.affine_depth_two_pushforward_hull`
(node `lem-sbc-affine-depth-two-pushforward-hull`).

Added exactly one hole:
`AlgebraicGeometry.Scheme.exists_affine_depth_two_locally_free_model`
(node `lem-sbc-affine-depth-two-locally-free-model`). Its proof is exactly `by sorry`;
its module contains no other holes. This is a decomposition, not a net reduction
in holes: one original hole closed, one strictly smaller construction hole added.
The remaining theorem constructs a model of an arbitrary finite locally free module
on an affine open; it does not identify an actual pushforward or prove Hartogs.
The main theorem performs those comparisons and all transports with complete Lean proofs.

Also proved, with no sorry:
`AlgebraicGeometry.Scheme.Modules.nonempty_restrict_pushforward_open_iso`
(node `lem-sbc-open-restriction-pushforward-comparison`), and
`AlgebraicGeometry.Scheme.Modules.nonempty_open_base_change_structure_module_iso`
(node `lem-sbc-open-base-change-structure-module`). All private helpers are proved.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.ModuleFinitePresentationExtension` from the item's module.
Its node `lem-weil-pbc-module-finite-presentation-extension` is now a proof dependency
of the pending affine model's construction, so it is not claimed globally unnecessary.
No original public imports were removed or privatized. The other original proof imports,
`WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward` and
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsAlgebraComparison`, are used.
No mathematical dependency module can be pruned globally by this delivery.
The duplicated one-sided private helper and the separate same-ring `depth_equiv`
helper are no longer needed; their uses are served by the generalized equality.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated a one-sided depth statement already present
in `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoCoherentModuleExtension`.
That theorem is private, and its module imports this item, so importing it is
neither a visibility-correct nor an acyclic repair. The repair therefore uses
the requested generalization-in-place alternative: a single equality theorem,
supplies both depth transports.
The downstream module and all existing library interfaces remain unchanged.

The original plan's double-dual construction and kernel calculation had no Lean
statements matching them. They are collected into the general affine model theorem,
with the complete nonintegral kernel calculation in its docstring and node.
Tags 0EBI and 0EBJ assume integrality, while this item does not. The new model does
not apply those integral statements as black boxes: it retains the explicit kernel
argument from the parent's plan. Edge cases checked: empty W, W equal to top, empty
spectrum, zero module, disconnected affine schemes, and nonintegral Noetherian rings.
The comparisons impose no finite, etale, Noetherian or depth assumption and include
empty inverse-images. No statement or definition is changed.

The source tree's `DepthTwoHartogsRestriction` was absent from the published compiled
library. This delivery uses the already available original Hartogs algebra comparison
instead and supplies its exact restriction-isomorphism input using proved comparisons;
it neither copies nor restates the unavailable dependency.

The unit record `sk-prop-input-spreading` has no realized bindings for this node.
Its depth-two-extension/Hartogs route is preserved. Finite flat pushforward is used
as the existing generic tool from the picard unit. The finite-presentation extension
remains a tool for the new affine model; no unit statement or route is bypassed.

Mathlib searches (recorded by `msearch.py`): LeanFinder for a coherent double-dual
model returned finite-type/presentation definitions, not a model theorem. Loogle
`Module.Dual` returned dual definitions and algebraic lemmas. Grep found restriction
adjunctions but no depth-two dual theorem. LeanSearch returned an Internal Server Error,
recorded as unavailable. A second LeanFinder search for open base change found the
restriction/pullback and restriction/direct-image counit isomorphisms used in the proof,
not either comparison theorem. Blueprint searches for double dual, finite locally free
coherent extension, and base change structure sheaf found no duplicate of these statements.

## New nodes

`lem-sbc-affine-depth-two-locally-free-model` is the pending double-dual construction
on a Noetherian affine scheme. It isolates steps 1--3 of the parent's plan from the
subsequent Hartogs identification. The finite-presentation extension theorem is its
first proof dependency. The remaining localization and kernel argument is spelled out.
Module: `Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoLocallyFreeModel`.

`lem-sbc-open-restriction-pushforward-comparison` records the fully proved comparison
for a general module and two open immersions. Module:
`Sheaf.AlgebraicGeometry.Morphisms.OpenRestrictionPushforwardComparison`.

`lem-sbc-open-base-change-structure-module` records the fully proved structure-module
comparison for the base-changed cover; it has no geometric finiteness or depth hypotheses.
Module: `Sheaf.AlgebraicGeometry.Morphisms.OpenBaseChangeStructureModule`.

No change records or forced adaptations are required: every existing signature,
definition, visibility, and public import is unchanged.

## Earlier second reading (a previous round; superseded)

1. Interfaces: PASS. Diffed the item against the repository and independently
   compared the existing theorem signature byte for byte. Only its proof, private
   helpers, scoped elaboration options and plain proof imports change. The other
   three delivered modules are new; all three node signatures match their Lean
   declarations verbatim after trimming terminal whitespace. No existing data
   definition or public import changes, and no change record is needed.
2. Proofs: PASS. Independently compiled all four modules in import order without
   errors or warnings. There is exactly one sorry, the named theorem
   `exists_affine_depth_two_locally_free_model`, as reported. No prohibited axiom,
   unsafe/opaque/extern declaration, or hollow data definition occurs. The delivery
   tool's declaration-by-declaration axiom probes pass: only standard axioms and
   sorryAx from still-open statements are allowed. The private algebra-module
   isomorphism is reflexivity, not arbitrary choice from an existence theorem.
   The model witness H is eliminated inside a proposition proof only.
3. Split statements: PASS. The model is a strictly smaller construction than the
   original actual-pushforward theorem: the latter now proves base-change,
   restriction, Hartogs identification and scalar-sensitive transports itself.
   Checked the double-dual kernel argument over a general Noetherian ring, without
   integrality: cancellation takes place in free modules using a base regular
   pair, not cancellation of arbitrary nonzero scalars. Nakayama ensures each
   successive quotient is nonzero when the finite stalk is nonzero. Empty W,
   W=top, empty spectrum, zero P and disconnected/nonintegral bases are covered.
   Checked the sources [0G41](https://stacks.math.columbia.edu/tag/0G41),
   [0EY6](https://stacks.math.columbia.edu/tag/0EY6),
   [0EBI](https://stacks.math.columbia.edu/tag/0EBI) and
   [0E9I](https://stacks.math.columbia.edu/tag/0E9I); the integral hypothesis of
   0EBI is not silently imported. Repeated LeanFinder, Loogle and Mathlib grep
   with vector-bundle/reflexivity queries, plus repository searches. They yield
   no existing affine model theorem. Related restriction/base-change helpers in
   PushforwardRankOnOpen and Cohomology/DirectImage/Sections are private, and do
   not supply a public replacement for either new comparison. The remaining
   model proof needs substantial localization and affine-module infrastructure;
   it is not a hole closable in a few minutes.
4. Route and pruning: PASS after import repair. The delivered assembly follows
   the coherent depth-two model followed by Hartogs route. Checked the unit's
   realized fields (all empty); its depth-two extension step remains intact.
   The only old proof dependency removed directly is the finite-presentation
   extension, explicitly listed above; it moves to the model's proof plan.
   Its module must remain reachable there. All newly added imports used only
   for proofs are plain imports. Original public imports stay unchanged.
5. DAG: PASS. Existing-node differences are confined to proof, proof_deps and
   proof_origin. The dependency union matches the new assembly. New nodes have
   source, complete proof narrative, searches, provenance, blueprint ancestry,
   chapter/unit and exact Lean records. One model hole is added and one original
   hole closed: a decomposition with net zero, not a complete target proof.

Second-reading changes: added the missing plain import of
`Sheaf.AlgebraicGeometry.ModuleFinitePresentationExtension` in the model module,
so its pending construction keeps the stated dependency in the import closure.
Replaced that new module's public Tilde import by the smaller public Modules.Sheaf
import; Tilde is now a plain proof import for the construction plan. Added the
independent reflexivity searches to its node and this review record. No theorem
statement or proof body was changed.


## Second reading by M1

1. Interfaces: PASS. Compared each delivered module with the repository: only
   AffineDepthTwoPushforwardHull exists there; the other three modules are new.
   Independently extracted and compared the existing theorem signature byte for
   byte, including every hypothesis and all three conclusions. Existing public
   imports and visibility are unchanged. No definition used by a target changes;
   no change record or forced adaptation is needed.
2. Proofs: PASS. Compiled all four modules locally in import order with
   lcompile.py --all, without errors or warnings. Scanned all four for forbidden
   declarations and found exactly the single reported named model theorem sorry.
   In a scratch copy, printed axioms for the repaired depth equality, the private
   direct-image isomorphism, the main theorem, the model, and both comparison
   theorems. Helpers and comparisons use only propext, Classical.choice and
   Quot.sound. Main theorem and pending model additionally use sorryAx.
   The inverse semilinearity proof is explicit and correct. Both zero-module
   branches and nonzero finite-module Nakayama branches are covered. The private
   data definition is Iso.refl; no arbitrary witness is chosen into data.
3. Split statements: PASS. Read the model statement and its complete double-dual
   construction proof independently. It separates the coherent construction
   from the actual-pushforward identification, so it is strictly a part of the
   argument, rather than a restatement. Checked empty W, W=top, zero P, empty
   spectrum, and disconnected and nonintegral bases. In the kernel calculation,
   a base regular pair acts regularly on the free source; cancellation in the
   free target proves that division by x stays in the kernel. Nakayama gives
   nonzero successive quotients for a nonzero finite kernel. No domain assumption
   is needed. Verified the sources 0G41(2), 0EY6 and 0EBI online; 0EBI's integral
   hypothesis is not used as a black box. The construction requires substantial
   affine/localization infrastructure and cannot be closed in a few minutes.
   Repeated msearch LeanFinder with a coherent-extension/vector-bundle query,
   Loogle for AddEquiv.isRegular_congr, and grep for kernel/free, dual/localization
   and regularity transport. Found component lemmas, no existing model theorem.
   Repository searches also found only private one-sided or same-ring depth
   transports. The existing private pushforward_restrict_square in DirectImage/
   Sections gives a related general comparison but is not public. The repaired
   semilinear equality generalizes the downstream private one-sided statement;
   that downstream module imports this item, so importing it would create a cycle.
4. Route and pruning: PASS. The main proof assembles finite locally free
   pushforward, the affine model, open-base-change comparisons and the existing
   Hartogs theorem, then transports all three conclusions over their exact scalar
   rings. Checked the unit's realized fields: none bind this node. The prescribed
   depth-two model/Hartogs route is kept. Every added proof import is plain;
   FiniteDescent supplies pullback finite local freeness, the upstream Tilde module
   supplies affine section transport, and ModuleStalkFunctor supplies stalk
   transport. The old finite-presentation-extension dependency is explicitly
   listed as removed directly and remains imported through the new model. No
   globally pruned module is claimed. One hole closed and one added is a net-zero
   decomposition, not a completely proved target.
5. DAG: PASS. Compared the existing node with its repository version; only proof,
   proof_deps and proof_origin differ. Checked each dependency list equals the
   union of the proof steps' uses and all four Lean-node signatures agree.
   Each new node has its source, proof narrative, searches, provenance, blueprint
   ancestry, chapter/unit and complete Lean record. The parent names the actual
   finite-locally-free, model, comparison and Hartogs declarations it uses.

Second-reading changes in this round: updated the stale opening review status and
added this independent review of the returned depth-equality repair. No Lean proof,
statement, definition, import or DAG field needed repair. The scratch axiom probe
was removed after checking it. The earlier round's import repairs remain in place.
