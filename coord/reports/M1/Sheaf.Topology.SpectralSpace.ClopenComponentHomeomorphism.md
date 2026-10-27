## What changed

Proved `isHomeomorph_connectedComponentsMap_of_bijective_clopen_preimage` in
`Sheaf.Topology.SpectralSpace.ClopenComponentHomeomorphism`, with its statement unchanged.
The proof follows the existing four-step DAG plan. It imports
`Sheaf.Topology.Connected.ComponentQuotientClopenNaturality` and
`Sheaf.Topology.ProfiniteClopenPullback` privately. Natural clopen descent transfers
bijectivity to the continuous map of component quotients. The existing theorem
`spectralSpace_connectedComponents_profinite` supplies the compact Hausdorff totally
disconnected instances for both quotients. The profinite pullback criterion supplies
injectivity, surjectivity and openness. Mathlib's `IsHomeomorph` constructor assembles
these facts with continuity. Surjectivity of `ConnectedComponents.mk` identifies the
normalized map with `hf.connectedComponentsMap` and retains the normalization equality.

The initial LeanFinder, Loogle and grep searches found no shorter theorem covering the
whole statement. The existing declared dependencies fit without any signature repair.
The unrelated universe parameter of `clopen_descent_naturality` is explicitly specialized
to `u`; both space universes in the item remain independent. No point or nonemptiness
assumption is introduced, so the same proof covers empty spaces.

## Proved and sorry left

Closed 1 of 1 holes:
`isHomeomorph_connectedComponentsMap_of_bijective_clopen_preimage`
(node `lem-sfb-spectral-clopen-component-homeomorphism`).
No sorry remains in the item, no holes are added, and no statements are split off.
The proof uses the existing statements
`ConnectedComponents.clopen_descent_naturality`
(node `lem-sfb-component-quotient-clopen-naturality`) and
`bijective_and_isOpenMap_of_bijective_clopen_preimage`
(node `lem-sfb-profinite-clopen-pullback-bijective-open`), whose existing proofs are
still sorry in the shared source. They are retained dependencies, unchanged by this
packet; this delivery does not claim their transitive closure is proved.

## No longer needed

Removed the direct private import `Mathlib.Topology.Separation.Profinite`:
the item uses the already-stated profinite clopen criterion, and does not itself
need to develop its clopen-basis argument. All three existing DAG proof dependencies
remain needed and are used. No DAG node or project module is withdrawn or pruned.
Public imports remain unchanged. There are no new nodes and no change records.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The current DAG already provides the
short assembly requested by the brief; its dependency set and proof route agree
with the delivered Lean proof. No node edit is necessary. Source passages checked:
Stacks `topology.tex`, `lemma-spectral-pi0`, `lemma-pi0-profinite` (clopen saturation),
and `lemma-profinite-refine-open-covering` (clopen neighbourhoods). The unit route is
preserved.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
