## What changed

Proved `AlgebraicGeometry.Scheme.lowestResidueModel_withinOpen` without changing its signature.
Choose an affine neighbourhood V directly in U inside the inverse image of O, factor
V -> S through O, transport the supplied complex P by the open-site equivalence, and
restrict termwise. The constructed K preserves the supplied free indexing types and
upper bound. Its negative terms vanish because the corresponding residue Betti numbers
are zero. A private proved comparison identifies exact open restriction in the derived
category with the chosen derived pullback, using a K-flat resolution and its counit.
The shared-category wrapper and private local instances bridge Scheme.Modules to the existing
SheafOfModules category without introducing a second derived category.

Added `Sheaf.AlgebraicGeometry.ResidueBettiZeroOfTensorVanishing`, with a completely
proved public theorem `AlgebraicGeometry.Scheme.derivedFiberBetti_eq_zero_of_tensor_vanishes`.
It tests the universal tensor hypothesis on the concrete upstream residue skyscraper,
proves its stalk evaluation bijective, takes exact stalks, transports the natural tensor
comparison to complexes, and uses the existing K-flat residue comparison. No arbitrary
object is chosen from an unproved mere-existence theorem to define data.

All new proof imports are non-public. Original public imports and declaration visibility
are preserved. The item's node records the actual proof; a new node records the proved
residue lemma. Both modules compile together through lcompile.py without errors or warnings.
The argument includes rank zero, arbitrary integer degrees, reversed a,b, and empty opens
(no x exists). The chosen model is the restriction of P, not a newly chosen representative.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.lowestResidueModel_withinOpen`
(node `lem-sc-lowest-residue-model-within-open`).

Also proved the new theorem
`AlgebraicGeometry.Scheme.derivedFiberBetti_eq_zero_of_tensor_vanishes`
(node `lem-sc-residue-betti-zero-of-tensor-vanishing`). All private helpers are proved.
No sorry remains in either delivered module; no hole is added or split off.
This closes 1 original hole and adds 0 holes, using existing library declarations.

## No longer needed

The item's planned dependencies `lem-pc-affine-tor-amplitude-criterion`
(`Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion`) and
`lem-pc-tor-amplitude-open-local` (`Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal`)
are not needed. They were not imported in the supplied module, and no such imports
are added. The new fixed-degree skyscraper test directly proves the needed Betti vanishing.
No existing import is removed. The actual proof dependencies replace the two planned
Tor lemmas with the proved residue test and `lem-pc-kflat-resolution`.
The old direct proof dependency `def-pc-derived-tensor-cohomology-vanishes`
now occurs through the residue-test node; its public import and statement
dependency remain, so its module is not pruned.

## Where the brief, the DAG or earlier work was wrong

The first DAG step named TorAmplitudeOpenLocal as though it supplied the global-to-stalk
Tor criterion. Its Lean declaration instead deduces a global bound from open-neighbourhood
bounds. AffineTorAmplitudeCriterion handles a tilde model on Spec A and assumes a <= b;
it does not directly handle the supplied over-site residue model or arbitrary a,b.
Neither is necessary: the residue skyscraper test works in each degree separately.

The delivery tool requires a change record for the new file-local elaboration commands;
`coord/changes/lowestResidueModel_withinOpen-proof-elaboration.md` records those commands
and the unchanged effect on every consumer. No statement or definition is disputed or
changed. No forced consumer adaptation is
needed. The unit record sk-prop-av-cube has no realized statement or step attached to
this helper; the supplied-model restriction and the cube route are retained.

## New nodes

`lem-sc-residue-betti-zero-of-tensor-vanishing` is the fixed-degree consequence of the
stalkwise Tor test of [Stacks Tag 09U9](https://stacks.math.columbia.edu/tag/09U9).
Its module is `Sheaf.AlgebraicGeometry.ResidueBettiZeroOfTensorVanishing` and its theorem
is fully proved. The source, complete proof steps, existing dependencies, exact Lean
statement, and three actual Mathlib search kinds are recorded. LeanSearch was unavailable;
LeanFinder and source grep returned no exact match. The blueprint search found no node
stating this general fixed-degree result. The proof-elaboration change record is
`coord/changes/lowestResidueModel_withinOpen-proof-elaboration.md`.

## Second reading by P3

1. Compared both delivered modules with the repository versions. The public target signature and all existing declaration signatures are unchanged; the only target difference is its proof body and proof-only imports. Verdict: pass.

2. Compiled both modules together with `lcompile.py --all`; compilation completed without errors or warnings. The delivered files contain no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. Scratch copies with `#print axioms` show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from still-open existing dependencies for both public theorems. These are local hole closures, not claims that the transitive proofs are already axiom-free. Verdict: pass.

3. Read the new residue-Betti theorem and its proof. Its statement is a strict fixed-degree consequence of the universal tensor hypothesis, with no added assumptions; the theorem is fully proved and has the recorded node. It is not a restatement of the target. Independently searched LeanFinder for vanishing after tensoring all module sheaves versus residue-field stalk cohomology, and source grep for skyscraper/stalk and residue/vanishing. No exact reusable public theorem was found; Mathlib skyscraper results concern a different presheaf construction. Checked empty schemes (no x), zero and infinite-dimensional fibres, and every integer degree. The implication only uses zero cohomology to infer zero finrank, never its invalid converse. Verdict: pass.

4. Checked the proof route and imports. The supplied complex is explicitly restricted termwise; the open derived comparison is proved with a K-flat resolution. The unit route remains unchanged (`sk-prop-av-cube.realized` attaches no step to this helper), and the proof-only `QuasicoherentKernel` import is necessary for the finite-limit instance, as a removal experiment confirmed. The two old planned Tor dependencies are both listed under No longer needed. Existing public open-pullback comparisons apply to canonical open inclusions rather than this arbitrary composite immersion; private comparisons cannot be reused directly. Verdict: pass.

5. Checked DAG proof steps and dependencies against the Lean proof, including the new node and its source/search records. Both Lean signatures occur verbatim in the modules; both proof dependency lists equal the union of the step uses. Verdict: pass.

Restored the existing target docstring byte for byte, preserving its API documentation. Expanded this report with the independent checks and axiom limitation. Restored the necessary proof-only import after the pruning experiment. No proof repair was needed; no statement, definition, or public import was changed.
