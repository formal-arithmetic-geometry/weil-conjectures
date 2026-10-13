## What changed

Proved `AlgebraicGeometry.Scheme.Modules.restrictedResolution_open_cohomology`
without changing its signature, visibility, or public imports. Added the proof-only
import `Sheaf.AlgebraicGeometry.ModuleCohomologyAugmentedLift`. Constructed the
restriction lift and its augmentation square, calculated its section components,
and combined the existing augmented-lift formula with the proved chain-map
identity using homology functoriality and inverse cancellation. Updated the
existing node's proof, proof dependencies, and proof origin to this route.

The argument treats empty and equal opens, zero coefficients, and degree zero
uniformly. No restriction map is inverted and no new data is selected from an
existence theorem. The blueprint unit's statement and steps are unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.restrictedResolution_open_cohomology`
(node `new-restricted-resolution-open-cohomology`), the item's only original hole.
Added: none. Remaining in the delivered module: none. No intermediate statements
were split off. The proof uses the already proved
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_of_augmentedLift`.
Its existing upstream proof dependencies retain their own status; this delivery
does not claim the entire transitive axiom closure is sorry-free.

## No longer needed

No existing import was removed: the original public import
`Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices` supplies the statement's
objects and must remain. Only the augmented-lift module is newly imported for
the proof.

The direct proof no longer requires the planned nodes
`lem-sp-right-adjoint-preserves-injectives` and
`lem-weil-pbc-module-restriction-open-immersion-limits`, or direct imports of
`WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves` and
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`.
It also delegates the independence calculation of
`lem-weil-pbc-module-cohomology-fmap-functorial` to the existing augmented-lift
formula; no direct import of
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial` is needed.
These are removals from this node's direct plan, not assertions that those
modules are unused elsewhere or absent from transitive imports.

## Where the brief, the DAG or earlier work was wrong

The plan was mathematically valid. Its explicit injective-pushforward and
identity-comparison construction is unnecessary because the existing
augmented-lift theorem computes the map for the lift constructed here.
The known top-to-open theorem supplied a useful model but does not itself
cover two arbitrary opens. The actual section calculation is proved directly
using restriction component formulas and naturality.

No interface changes, new nodes, forced adaptations, disputed statements,
or process failures.

## Second reading by U4

1. Interface: compared the sole delivered Lean module against the repository
   version. The existing theorem signature is byte for byte identical after
   removing one extra space before `:= by`. Its visibility, universes, hypotheses,
   conclusion, and public import are unchanged. There are no definitions, new
   declarations, adapted modules, or change records. Verdict: pass.
2. Proof: read the whole proof and compiled the module with `lcompile.py`, cleanly
   in 53.2 seconds. A scratch copy of the final file compiled in 47.3 seconds;
   `#print axioms AlgebraicGeometry.Scheme.Modules.restrictedResolution_open_cohomology`
   reported exactly `propext`, `Classical.choice`, and `Quot.sound`, with no
   `sorryAx`. Scanned the delivery for `sorry` and forbidden declarations or
   attributes: none. The explicit complex maps t and beta use the supplied
   resolutions and their comparisons; the canonical sections isomorphism is
   constructed componentwise. No data is chosen from an unproved existence
   theorem. Verdict: pass.
3. Split statements: none were added or left in this module. Read the statement
   and proof of `moduleCohomologyFMap_of_augmentedLift`: its augmentation equation
   is precisely hbeta here, and its prescribed inverse section components are ha.
   The lift and component calculation require no nonempty-open, positive-degree,
   affine, or nonzero-coefficient hypothesis. They apply to L = U, L empty, zero
   coefficients, and p = 0. Verdict: pass; no decomposition or relabelled hole.
4. Route and pruning: read Stacks Tags
   [01FB](https://stacks.math.columbia.edu/tag/01FB) and
   [01E2](https://stacks.math.columbia.edu/tag/01E2), the imported restricted-choice
   structure, and the top-to-open `restrictedResolution_cohomology` proof.
   The augmented-lift theorem supplies the shortest available cohomology-map
   computation; the remaining arbitrary-open section square is genuinely proved
   here by naturality, comparison cancellation, component formulas, and presheaf
   composition. Fresh msearch queries `globalSections.*restrict|restriction.*homology|augmentedLift`
   (grep) and `"homologyFunctor", "map_comp"` (Loogle), and source searches in
   lean/ and the upstream checkout found no replacement for the complete pinned
   equation. The public FlatBaseChangeOpenChoices import is needed by the
   statement; the plain augmented-lift import is used only by the proof. Read
   dag/units/sk-thm-p1.json: neither this node nor any of the three bypassed direct
   dependencies realizes a unit statement or step. The unit's realized route
   stays unchanged. `No longer needed` lists all three removed direct proof
   dependencies; no existing module import is removed. Verdict: pass.
5. DAG: compared the delivered node with its repository version. Only `proof`,
   `proof_deps`, and `proof_origin` differ. The dependency list is exactly the
   union of the steps' uses. Steps match t/ht/hbeta, a/ha and the augmented-lift
   application, the degreewise equality hc, and homology functoriality with target
   inverse cancellation. The statement and Lean record are unchanged and there
   are no new nodes to validate. Verdict: pass.

Second-reading changes: removed the extra pre-proof space to restore literal
signature equality and added this review. No mathematical proof repair was
necessary. Closed one original hole; added zero holes; no split-off statements.
