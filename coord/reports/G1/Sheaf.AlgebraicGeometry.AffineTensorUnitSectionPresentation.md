## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.Modules.affine_tensor_unit_section_presentation`
by a complete Lean reduction. Its signature and visibility are unchanged. The proof first
obtains the affine pushout ring and first tensor sections from the new module
`Sheaf.AlgebraicGeometry.AffinePushoutFirstTensorSections`, then applies the existing
`quasiCoherent_algebra_changeOfRings` to the final extension along epsilon.
Quasi-coherence is established using existing pushforward, scalar-restriction,
affine-pushout-algebra and ordinary pullback declarations. The ordinary and tensor
pullbacks are compared by uniqueness of left adjoints.

The fully proved private helper `scalar_tensor_presentation` contains the algebra calculation.
It transports tensor multiplication through the first comparison, proves it balanced over the
pushout algebra by additive generation, and extends it to an additive map from the outer
tensor product. This proves the required kernel inclusion. Delta-balancing kills the displayed
relations, and single-tensor induction proves the reverse inclusion. Balancing by the first
inclusion moves every outer scalar inside, proving surjectivity. The kappa hom-inv equation
then proves the canonical gamma-unit formula.

Updated the original node's `proof`, `proof_deps` and `proof_origin`, and added a node for the
first affine comparison. All writes are in this item's sandbox; no other held module is adapted.
Proof imports were added for the new comparison, the existing affine tensor algebra's
quasi-coherence, separatedness and the ordinary module-pullback quasi-coherence instance.
The scoped heartbeat allowance is documented; local compiles have remained below 60 seconds.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.affine_tensor_unit_section_presentation`
(node `lem-weil-pbc-affine-tensor-unit-section-presentation`).

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.affine_pushout_first_tensor_sections`
(node `lem-weil-pbc-affine-pushout-first-tensor-sections`), in its own new module. Its
proof is exactly `:= by sorry`; its source and complete proof in words are in the docstring.
It concerns only B and P, with no final extension H, gamma, surjectivity of q, or kernel
assertion. It is therefore the first geometric part of the argument, rather than a renamed
version of the result. The equivalence p is determined uniquely by its unit normalization
and first-factor action on pure tensors, so no arbitrary witness supplies definition data.
Delta is used solely in the balancing proof, not as data of a public definition.

This is a decomposition: one upper hole closed and one lower hole added, net zero new
hole closures. The scalar-tensor kernel, surjectivity and canonical-unit calculations are
fully proved and introduce no holes. The existing imported declarations may themselves
rest on sorry, as intended in stage 3; none is modified by this delivery.

Both modules compiled cleanly through the delivery tool, about 14 and 39 seconds respectively.
`deliver3.py G1 Sheaf.AlgebraicGeometry.AffineTensorUnitSectionPresentation --no-push`
printed OK: the commit compiles and passes preflight except for the second reading, which
is reserved for the next worker. The delivery tool also ran its declaration axiom probes.
Nothing was pushed.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`
from the original module, replacing it by the more precise first-tensor comparison module.
It remains needed by that new module's geometric proof plan, so neither its node nor its
module is claimed globally pruned. The old direct dependency `lem-weil-pbc-module-pullback-affine-sections` is now
used through `lem-weil-pbc-affine-pushout-first-tensor-sections`; it is not globally
pruned. The old dependency `pqf-def-affine-morphism` remains directly needed for
`hV.preimage f` and remains in the updated proof plan. No DAG dependency or module
is globally pruned.
The other original proof dependencies remain needed, directly or through the first affine
comparison. The unit quasi-coherence declaration is available through the added ordinary
pullback's Tilde module; no separate redundant import for it is retained.

## Where the brief, the DAG or earlier work was wrong

No statement correction or forced adaptation was needed. The original plan's sentence
identifying the section-ring pushout and both tensor actions is substantial glue absent
from the existing affine pullback section signature. It is isolated as the single new
geometric theorem, while the alleged elementary algebra observation is now written out
as a complete Lean proof. The existing affine-pushout-algebra quasi-coherence theorem
already states the needed quasi-coherence; it is used instead of duplicated in the new node.

The local checkout has no `literature/stacks-project/morphisms.tex`. The source was read
from the official [Stacks Tag 01SB](https://stacks.math.columbia.edu/tag/01SB), including
its affine reduction and final algebra observation. Expanded omitted details are marked
`proof_origin.by = agent`. Searches were actually run through `msearch.py`: Lean Finder
returned affine scheme-pullback results, grep returned the ordinary ring tensor pushout,
and LeanSearch returned HTTP Internal Server Error, recorded as unavailable. The Loogle
query using unqualified IsPushout was invalid and is not treated as evidence of absence.
Blueprint searches for `affine.*tensor` and `pushout`, and a broader `tensor` search, found
no existing blueprint statement of this specific ring-and-module comparison. The ancestor
tool could not resolve the module-valued created.item chain; the new node instead preserves
the original node's explicit ancestor `thm-weil-pbc-finite-etale-lifting` and extends its via
chain. The realized unit statements and proof steps are not bypassed.

Edge cases checked in the new statement: f the identity has delta=id and p the ordinary
tensor-unit equivalence; every ring section is the single product r times 1. For N=0 the
first module and all maps are zero, while the independent ring comparison still applies.
For an empty preimage W all section rings and modules are zero, and the empty sum gives
the generator formula. The general formulas use neither flatness nor nonzero hypotheses.
The fully proved algebra helper uses only additive generation, the two actions and epsilon
splitting, so these edge cases are also covered by its Lean proof.

## New nodes

`lem-weil-pbc-affine-pushout-first-tensor-sections` is in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-pushout-first-tensor-sections.json`.
It states the affine comparison p and the second ring inclusion delta with their actions,
additive ring generation and unit normalization. Its module is
`lean/Sheaf/AlgebraicGeometry/AffinePushoutFirstTensorSections.lean`. The first two steps
of the original affine presentation plan motivate it; final extension, kernel and
surjectivity are deliberately left to the original module's proved argument. The node
has the same chapter and unit as the original, a full Lean record, genuine logged searches,
and complete sourced proof steps. There are no change records because no interface changed.

## Second reading by G1

1. **Interface: pass.** Read the full diff against the repository module and compared
   the entire existing theorem signature up to `:= by` byte for byte: identical.
   All original local notations and public imports are unchanged. The existing
   declaration's visibility is unchanged; the added imports are proof-only.
   No definitions or statements of other modules are adapted, and no change record
   is required.
2. **Proof and trust: pass.** Independently compiled both modules in import order
   through `lcompile.py` (12.6 s and 43.1 s, clean). Read the private algebra proof:
   the epsilon-balanced additive map gives the forward kernel inclusion; tensor
   normalization and delta-balancing give equality; alpha-balancing gives
   surjectivity. Read the quasi-coherence transfer, section equivalence transport,
   gamma formula and kappa inverse cancellation in the main proof. There is no
   forbidden declaration or option, no new definition, and no sorry in the main
   module or helper. The only new sorry is the reported named geometric theorem.
   Independent scratch `#print axioms` checks returned only propext,
   Classical.choice and Quot.sound for scalar_tensor_presentation; the main
   theorem and split geometric theorem additionally use sorryAx, as expected
   from the reported open dependencies. Scratch copies were removed.
3. **Split statement: pass, still open.** Read its signature, sourced docstring and
   node together. On an affine chart it asserts E=C tensor_D C and M=C tensor_D N
   with the two canonical actions, before the final extension; it does not restate
   the surjection or kernel conclusion. The hP unit equation fixes the comparison
   on 1 tensor n and b-linearity fixes it on all pure tensors. Delta is the second
   canonical ring inclusion. Neither witness is used to supply a public definition.
   Checked f=id, N=0, W empty and also the nonflat map Z -> Z/2: both tensor actions
   and epsilon splitting still have the stated formulas, with no flatness needed.
   Independently searched via msearch Lean Finder for global sections of coproducts
   of quasi-coherent algebra sheaves and via grep for sheaf coproduct/pushout and
   preservation of pushouts/tensors; neither supplied this combined comparison.
   Repository searches and inspection of ModulePullbackAffineSections,
   AffineModuleTensorAlgebraQuasiCoherent and QuasiCoherentAlgebraAffineInclusion
   found partial ingredients, not a duplicate. The ring pushout-to-affine-sections
   comparison and compatibility with the module action remain substantial; they
   cannot be closed in a few minutes without a new formal construction. The
   unqualified Loogle IsPushout query was invalid and is not evidence of absence.
4. **Route and pruning: pass after repair.** The fully written algebra argument uses
   existing TensorProduct lifts, balancing and induction; no shorter existing
   theorem located replaces its geometric reduction. Proof-only imports provide
   the section comparison and quasi-coherence/adjunction instances. The new
   module's proof-dependency imports are retained for its open geometric plan.
   Checked dag/units/sk-thm-p1.json realized statement and all step lists: this
   work occurs below those nodes and bypasses none. The old direct affine-section
   dependency is redirected through the new node, not globally pruned. Restored
   the omitted affine-morphism dependency because hV.preimage f uses it directly.
5. **DAG: pass after repair.** Compared the updated main node's steps, uses,
   proof_deps and proof_origin against the actual proof. Compared the new node's
   verbatim Lean signature, statement, source, searches, creation record, blueprint
   ancestry, chapter and unit against its module. Its proof_deps are the union of
   its proof-step uses. The main node now also records pqf-def-affine-morphism in
   step 2 and proof_deps. Existing fields outside proof/proof_deps/proof_origin
   are unchanged.

Second reading changed only the main node's affine-morphism dependency bookkeeping
and this report's pruning/review documentation; the Lean proofs were kept. This
remains one original hole closed and one strictly lower hole added, a decomposition
with net zero hole closures, not an axiom-free proof of the import closure.
The source was independently checked at
[Stacks Tag 01SB](https://stacks.math.columbia.edu/tag/01SB).
