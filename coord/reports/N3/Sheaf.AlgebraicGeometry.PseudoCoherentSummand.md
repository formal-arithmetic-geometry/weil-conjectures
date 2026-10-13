## What changed

Proved `AlgebraicGeometry.Scheme.pseudoCoherent_of_isIso_biproduct` without changing its
signature or public imports. Its proof refines local witnesses to affine opens, explicitly
lifts the finite-free terms and differential matrices to a bounded-above module complex,
applies the existing ring summand theorem, and sheafifies both resulting models.

Added the fully proved module `Sheaf.AlgebraicGeometry.AffineDerivedSummandModels`, with
`AlgebraicGeometry.Scheme.affine_derived_summand_models`. It lifts an arbitrary decomposition
of an associated complex to modules, with no pseudo-coherence or boundedness assumption.
It uses the affine derived equivalence and localized-site transport, the exact derived
tilde/Gamma adjunction, and invertibility of the counit on retracts. This is the affine
transport step of the original plan, not a restatement of pseudo-coherent summand closure.

Updated the existing node's proof and dependencies to this route and added the new helper's
node. Removed the direct affine criterion import; the affine derived equivalence import
is now in the helper. Added the proof import of the helper and the existing module-sheaf
transport API. No definitions, existing signatures, other held modules, targets, chapter
records, or unit records were changed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.pseudoCoherent_of_isIso_biproduct`
(node `lem-pc-pseudo-coherent-summand`).

Also proved the new theorem `AlgebraicGeometry.Scheme.affine_derived_summand_models`
(node `lem-pc-affine-derived-summand-models`). Both delivered Lean modules contain no
`sorry`. Holes added: zero. Holes split off: zero. This is one hole closed, not a
decomposition. Existing imported dependencies, notably
`DerivedCategory.pseudoCoherent_summand`, remain separate proof obligations.

The delivered files compiled together without errors or warnings using `lcompile.py`.
`deliver3.py --no-push` printed OK; the second reading is intentionally left to the reader.
The new helper compiled in approximately 33 seconds and the main module in approximately
24 seconds, within the single-file limit. Checked that all local free-module constructions
use actual bases and lifted differentials. There is no definition taking data from an
unproved mere-existence statement. The argument covers arbitrary rings, empty affine opens,
empty schemes, and zero summands; it does not impose Noetherianity or bounded-below hypotheses.

## No longer needed

Removed direct import `Sheaf.AlgebraicGeometry.AffinePseudoCoherentCriterion` and dependency
`lem-pc-affine-pseudo-coherent-criterion`. Its global affine-localization/gluing argument is
unnecessary: the original local finite-free witness is lifted directly on an affine
refinement. The direct import of `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence` was
moved to the new helper, so that module and its node remain needed transitively.

The following project modules and their nodes leave this item's import closure compared
with the repository baseline. Other consumers may still need them; this is not a claim
that all have left the full targets' closure.

- `Sheaf.AlgebraicGeometry.AffineFiniteFreeSheafComplexLift`: `lem-pc-affine-finite-free-sheaf-complex-lift`
- `Sheaf.AlgebraicGeometry.AffinePrincipalSheafComplexTransport`: `lem-pc-affine-principal-sheaf-complex-transport`
- `Sheaf.AlgebraicGeometry.AffinePseudoCoherentCriterion`: `lem-pc-affine-pseudo-coherent-criterion`
- `Sheaf.AlgebraicGeometry.AffinePseudoCoherentLocalizationCover`: `lem-pc-affine-pseudo-coherent-localization-cover`
- `Sheaf.AlgebraicGeometry.AffinePseudoCoherentPrincipalModel`: `lem-pc-affine-pseudo-coherent-principal-model`
- `Sheaf.AlgebraicGeometry.AffinePseudoCoherentPrincipalSheafModel`: `lem-pc-affine-pseudo-coherent-principal-sheaf-model`
- `Sheaf.RingTheory.FiniteConeCycleAttachment`: `lem-pc-ring-finite-cone-cycle-attachment`
- `Sheaf.RingTheory.FiniteConeFreeExtension`: `lem-pc-ring-finite-cone-free-extension`
- `Sheaf.RingTheory.FiniteConeFreeModel`: `lem-pc-ring-finite-cone-free-model`
- `Sheaf.RingTheory.FiniteHomologyOfMPseudoCoherent`: `lem-sc-finite-cohomology`
- `Sheaf.RingTheory.HomologyVanishingLocalizationSpan`: `lem-pc-homology-vanishing-localization-span`
- `Sheaf.RingTheory.MPseudoCoherentLocalizationConeConstruction`: `lem-pc-m-pseudo-coherent-localization-cone-construction`
- `Sheaf.RingTheory.MPseudoCoherentLocalizationConeLocal`: `lem-pc-m-pseudo-coherent-localization-cone-local`
- `Sheaf.RingTheory.MPseudoCoherentLocalizationConeStep`: `lem-pc-m-pseudo-coherent-localization-cone-step`
- `Sheaf.RingTheory.MPseudoCoherentVanishingBase`: `lem-pc-ring-m-pseudo-coherent-vanishing-base`
- `Sheaf.RingTheory.PseudoCoherentIffAllM`: `lem-pc-ring-pseudo-coherent-iff-all-m`
- `Sheaf.RingTheory.RingPseudoCoherentLocalizationGlue`: `lem-pc-ring-pseudo-coherent-localization-glue`
- `Sheaf.RingTheory.StabilizingConeTower`: `lem-pc-ring-stabilizing-cone-tower`

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable tool was found. The original plan's affine criterion detour
was longer than necessary: its input already includes an explicit finite-free local model.
The transport step was not directly exposed by the affine equivalence's signature; the
new helper proves it via the derived counit and retracts. This also avoids treating
quasi-coherence of summand cohomology as undeveloped elementary glue.

The blueprint unit `sk-thm-picard-duality` has no realized entry requiring the discarded
affine criterion route. The proof retains the scheme-to-ring reduction and the ring
summand theorem. The missing local Stacks source files were read through the public
Stacks pages https://stacks.math.columbia.edu/tag/08CE and
https://stacks.math.columbia.edu/tag/06Z0. LeanSearch returned an HTTP 500 and is recorded
as unavailable, not as a negative search result. LeanFinder, Loogle, and source searches
were also run; no existing exact affine splitting theorem was found.

## New nodes

`lem-pc-affine-derived-summand-models`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-derived-summand-models.json`, states the
proved affine decomposition-lifting theorem. Its source is Stacks Tag 06Z0's derived
adjunction and affine equivalence, as used in the original Tag 08CE affine reduction.
The node records the actual comparison, derived-adjunction, and counit-retract proof,
the three required kinds of search, and the unchanged blueprint ancestor
`lem-sc-finite-duality`. There are no new holes or change records.

## Second reading by N3

1. **Interfaces: pass.** Diffed the existing module and node against the repository.
   The complete existing theorem signature, including universe parameters and both
   derived-category instance hypotheses, is byte for byte identical. Its public import
   is unchanged. The only new public declaration is the reported affine helper, in its
   own module; no existing definition, target, or other held module changes. The existing
   node changes only `proof`, `proof_deps`, and `proof_origin`.
2. **Proofs: pass.** Independently compiled both delivered modules together with
   `lcompile.py`: helper 34.7 seconds, item 25.5 seconds, no errors or warnings. Scanned
   both source files: no `sorry`, forbidden axiom, unsafe/opaque declaration, extern,
   implementation override, or kernel-check bypass. Compiled scratch copies with
   `#print axioms` for both public theorems: exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The latter is from existing imported obligations,
   including the ring summand theorem and affine derived equivalence, not new holes.
   Read the exact-left-derived adjunction implementation and the affine transport API.
   The local module complex uses actual finite free modules and lifted differentials;
   its shape, square-zero equations, and upper bound are proved. All model witnesses
   are eliminated within proofs of propositions. No new definition chooses arbitrary
   data from an unproved existence theorem.
3. **New statements: pass.** There are no split-off holes. The proved helper is strictly
   the affine transport part, with no pseudo-coherence assumption or conclusion; it
   does not restate the item. Checked its argument: the fully faithful left adjoint
   has invertible counit on its image; naturality and retract closure of isomorphisms
   give invertible counits on the two summands; full faithfulness lifts their combined
   decomposition. Empty affine opens, the zero ring, zero complexes and zero summands
   obey the same equations. Unbounded complexes impose no hidden finite-support
   assumption. Independently searched LeanFinder with essential-image/retract wording,
   Loogle for the adjunction counit, and the repository affine modules for retracts and
   essential images. Found generic categorical ingredients already used, no existing
   affine decomposition theorem to replace this helper. Recorded these searches in
   the new node. Checked the cited derived adjunction and affine equivalence against
   https://stacks.math.columbia.edu/tag/06Z0 and the summand result against
   https://stacks.math.columbia.edu/tag/08CE.
4. **Route and pruning: pass.** Read the item from its target downward: affine refinement,
   explicit finite-free lift, derived summand lift, ring summand theorem, and termwise
   sheafification. The existing affine criterion would add an unnecessary detour;
   no shorter matching upstream or Mathlib theorem was found. Each retained import
   supplies statements or proof APIs used by this argument; proof-only imports are
   plain imports. Computed both import closures from source: the 18 removed project
   modules are exactly the list under `## No longer needed`. Both old proof dependencies
   omitted from the new direct list are accounted for: the affine criterion is pruned,
   while the affine equivalence remains through the helper. The unit
   `sk-thm-picard-duality` has empty realized statement and step lists, and no protected
   realized route is bypassed or changed.
5. **DAG: pass.** Checked both nodes against their Lean declarations and proof steps.
   Their dependency lists equal the union of step uses; the new node's verbatim
   signature matches the new theorem. Its source, creation, search, blueprint ancestry,
   chapter, unit, and Lean records satisfy the new-node requirements. The existing
   node's revised proof describes the explicit construction actually compiled.

Second reading changed only this report and the new node's search evidence. No Lean
proof or signature needed repair. Original holes closed: one; new holes: zero;
split-off holes: zero. The helper is proved relative to its imported dependencies.
