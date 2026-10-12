## What changed

Replaced the proof of `AlgebraicGeometry.gabber_h0_zariski_gluing` without changing
its signature or existing docstring. Added the proof-only import of
`Sheaf.AlgebraicGeometry.GabberH0ZariskiLocalData` and Mathlib's unique-gluing module.
The new module states the geometric restriction identifications and local section
transport, with a source and complete proof in words. The target uses
`gabber_zariski_etale_restriction_injective` to construct an injective comparison,
then the private, fully proved `lift_of_local_lifts` to establish compatibility,
glue the sections, and identify their image by local equality. Finally it composes
with the top-section identification and proves both original equations.

The existing node's proof, proof dependencies and origin were updated to match
this route. Both modules compile cleanly with the prescribed compiler.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.gabber_h0_zariski_gluing`
(node `lem-weil-pbc-gabber-h0-zariski-gluing`). Its proof now has no sorry.
The private helper `lift_of_local_lifts` is fully proved, including empty covers.

Added exactly one hole: `AlgebraicGeometry.gabber_h0_zariski_local_data`
(node `lem-weil-pbc-gabber-h0-zariski-local-data`), in its own new module.
It constructs restriction data and identifies local representatives; it asserts
neither injectivity nor existence of a global lift. Those steps are proved in
the target using the existing comparison theorem and Mathlib's sheaf axiom.
This is a decomposition: one upper hole closed and one lower hole added, net zero
newly closed holes before accounting for upstream dependencies. It is not a claim
that the theorem's full axiom closure is sorry-free. No definitions are added and
no data are extracted from an unproved theorem into a definition.

## No longer needed

Removed the item's direct proof-only imports:
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits` and
`Sheaf.Paper.ZariskiEtaleInclusionMorphismOfSites`.
The composition declarations remain visible through the unchanged public descent
import, and the inclusion construction remains in the remaining lemma's proof plan.
No geometric node is claimed pruned: the original geometric dependencies were
relocated into the local-data node, while closed-immersion base change and the
injective comparison remain used directly in the parent proof.
No unit statement or unit proof step was bypassed.

For completeness, the old parent `proof_deps` no longer used directly are
`def-weil-pbc-etale-sheaf-of-sets`, `def-pc-fibre-product`,
`lem-weil-pbc-sets-etale-inverse-image-composition-units`, and
`lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites`. All four remain in
the new local-data node's proof dependencies; none is pruned from the import
closure by this delivery. The other three old dependencies remain in the parent.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped because the reusable geometric construction interface
was missing. This is a split point, not an obstacle: the local-data lemma expresses
that construction in Lean, leaving actual injectivity and gluing outside it.

The local Stacks tex file referenced by the node is absent on this machine.
The proof was checked against the official source at
https://stacks.math.columbia.edu/tag/09ZF (fourth proof paragraph).
LeanSearch returned Internal Server Error; the unavailable search is recorded,
and LeanFinder, Loogle and grep searches were completed. No tool was bypassed.

Edge cases checked: an empty refinement family forces Xprime, and hence its
fibre product, to be empty; the empty-cover sheaf axiom supplies the gluing.
A nonempty refinement with empty fibre product is handled by the same gluing proof.
No finite, surjective, compactness or global-section-bijectivity hypothesis was added.
The universal compatibility clause applies only to comparisons satisfying the
canonical unit equation, which the existing comparison theorem supplies.

## New nodes

`lem-weil-pbc-gabber-h0-zariski-local-data`, in
`lean/Sheaf/AlgebraicGeometry/GabberH0ZariskiLocalData.lean`, packages the restriction
sheaves, their presheaf identifications, fibre-product identifications, top-section
transport, and local representative equations for any unit-compatible comparison.
It is the geometric part of steps 1, 2 and 4, stopping before the injectivity and
global gluing of step 3. Its source is Stacks Tag 09ZF, fourth proof paragraph.
There are no change records because no existing signature or definition changed.

## Second reading by C2

1. **Interface: pass.** Read the complete diff against the repository module.
   The existing theorem signature is byte-for-byte unchanged, including all
   universes, representative equation `hs`, cover equation `hW`, factorization
   equation `hphi`, pointwise Kan-extension instance, and both final equations.
   Its existing docstring and all public imports are unchanged. Only private
   proof code and proof-only imports changed; no existing definition changed.
   Both delivered node `lean.statement` strings equal their Lean signatures.

2. **Proof and axioms: pass as a decomposition.** Compiled both modules in
   dependency order through `lcompile.py`; neither has errors or warnings.
   Scanned both modules: their sole `sorry` is the reported named local-data
   theorem; there is no definition or forbidden declaration. Compiled scratch
   copies with `#print axioms`: `lift_of_local_lifts` uses only `propext`,
   `Classical.choice`, and `Quot.sound`; both public theorems additionally use
   `sorryAx`. The parent obtains the canonical comparison's unit equation via
   `(hbeta beta).mpr rfl`, proves local compatibility by its componentwise
   injectivity and naturality, uses unique gluing, and uses separatedness to
   identify the glued image. It then proves the first equation using `he` and
   the second using `hunit`. No arbitrary existence witness is installed in a
   definition. The imported descent comparison chooses a composition isomorphism
   characterized uniquely by its unit equation, not an arbitrary section.

3. **Split statement: pass.** Read every clause of the local-data lemma and
   checked its construction against Stacks Tag 09ZF's refinement paragraph:
   https://stacks.math.columbia.edu/tag/09ZF. Restriction sheaves and their
   presheaf isomorphisms fix the geometric meaning of G and H; the open
   base-change isomorphism has the required projection equation. The local
   clause supplies only local preimages for unit-compatible comparisons, not
   injectivity, overlap compatibility, or a global preimage. Those latter
   steps remain genuinely proved in the parent. The docstring explains the
   construction and both transport equations. Checked empty index type,
   empty fibre product, singleton cover, and identity base change: preimages
   of opens cover in each case, and empty covers use the sheaf axiom.
   Repeated LeanFinder, Loogle, and grep searches with restriction/open-subscheme
   terminology, and searched the project and upstream source. Found generic
   restriction and inverse-image tools and the existing injectivity proof's
   explicit restriction construction, but no theorem giving the required
   local representative and composite-unit transport package. These ingredients
   do not close its remaining geometric transport proof in a few minutes.

4. **Route and pruning: pass after report repair.** The parent uses the existing
   restriction injectivity theorem and Mathlib's unique-gluing/local-equality
   lemmas instead of adding holes for these steps. Both added imports are
   proof-only; the new module's imports support its signature. Checked the old
   dependency list against the new union and explicitly listed the four
   relocated dependencies above. No module is claimed pruned. Read
   `dag/units/sk-thm-iff.json`: its statement and realized proof-step node remain
   `lemma-weil-pbc-property-iff-acyclicity`; this subsidiary construction changes
   neither the unit's route nor any realized field.

5. **Nodes: pass.** The parent proof steps track the actual obtains, closed
   immersion base-change instance, comparison, private gluing proof, and final
   transport. Its `proof_deps` is the union of those steps' uses. The new node
   has the source, natural-language proof, searches, creation/blueprint data,
   matching chapter and unit, and verbatim Lean record required by the brief;
   its dependency union agrees with its construction plan. Only the permitted
   proof fields of the existing node are changed.

**Second-reading changes:** completed the explicit list of relocated old proof
dependencies under `## No longer needed` and added this review. No Lean code,
statement, definition, or node was changed. One original hole is closed and one
strictly lower geometric hole is added: decomposition, net zero holes closed.
