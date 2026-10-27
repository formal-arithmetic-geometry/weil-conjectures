# Stage-1 report: lem-trf-finite-type-component-open-qc

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-type-component-open-qc.json`: statement; split into five proof steps using existing nodes. No new Mathlib leaf and no new unsplit node.
- `citations.json`: twelve step/node entries, each quoting the cited statement verbatim.
- `report.md`: this report. `searches.jsonl` is the search command's actual log.

## Attachments

No attachment for the item. Searches under `lean/WeilConjectures/` for its blueprint tag, connected-component openness and finite-type components found no declaration giving every clause. The already attached tool node `lem-sfb-noetherian-connected-components-open` correctly carries `TopologicalSpace.NoetherianSpace.finite_connectedComponents` and `TopologicalSpace.NoetherianSpace.isOpen_connectedComponent` in `WeilConjectures/Mathlib/Topology/NoetherianSpace.lean:50–63`. I read these complete proofs; neither states quasi-compactness or finite type of a component of a scheme, so they do not attach the item.

## WANTED

None. All sources used are available locally. No SGA source is used.

## Findings and changes

The imported statement is correct and is preserved verbatim. The proof was empty. Stacks 057K (`more-morphisms.tex`, `lemma-local-local-structure-finite-type`, paragraph beginning “Let T be the connected component”) uses Noetherianity to obtain an open component of a smooth fibre. Its Noetherian/open argument does not use smoothness; the item correctly isolates that argument for any finite-type scheme over a field. The extra quasi-compactness and finite-type conclusions are supplied by existing general results, rather than silently adding smoothness, separatedness or an algebraic-closure assumption.

The distinction between quasi-compactness of the space T and of the inclusion j:T→C is made explicit. Step 4 checks j's inverse image of every affine open, rather than inferring quasi-compactness of j solely from quasi-compactness of its source.

The latest blueprint was read at `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`, together with the unit record `dag/units/sk-i-curve-zero.json` and chapter record `dag/chapters/sec-trace-formula.json`. This is an auxiliary node far down the recorded created-item chain, not the unit's key statement. Its existing ancestor and precise inherited 057K place are preserved. The present ancestor proof concerns contracting correspondences and does not separately state this component lemma. No unit or chapter is modified, and no alternative route replaces a unit step.

## Unfinished work

None for this one-level split. All cited nodes already exist. There are zero new nodes and zero new Mathlib leaves.

## Not duplicates

No new nodes. Whole-DAG title/concept searches found and reused `lem-sfb-noetherian-connected-components-open`, `lem-sfb-noetherian-space-compact-subsets`, `lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`, `lem-weil-pbc-qc-open-immersion-finite-type`, and `lem-sfb-finite-type-composition-base-change`. Blueprint searches for connected components, Noetherianity, 01T6 and quasi-compact open immersions found no blueprint statement duplicating the whole item. The affine finite-type Noetherian node is insufficient alone because C need not be affine; the normal-component node has an extra normality hypothesis, which this proof avoids.

## Mathlib searches

The item's old searches are retained. New searches were made only through the required msearch.py command, and their exact tool/query/results are copied from searches.jsonl into the item. I read the LeanSearch compact-open/affine-cover results, the LeanFinder results for Noetherian compactness and schemes, and the grep hits. A second phrasing asks about Noetherian topological spaces. These find separate Noetherianity and compactness results, not the entire item as a one-line specialization. Loogle for `AlgebraicGeometry.IsNoetherian, connectedComponent` returned no hits. The Noetherian component openness theorem is a project declaration, already represented by the existing closed tool node; it is not a Mathlib leaf for this item. No absent service is reported as a negative search.

## Review by NE

I checked the item against Stacks 057K at `lemma-local-local-structure-finite-type`, reading the actual proof beginning with the choice of the connected component of Y_s. The local source asserts that Noetherianity makes this component open. I also read Morphisms 01T6 (`lemma-finite-type-noetherian`), Properties 01OV (`definition-noetherian`) and 01OZ (`lemma-Noetherian-topology`), Topology 04MF (`lemma-locally-Noetherian-locally-connected`), 04ME (`lemma-locally-connected`) and 04ZA (`lemma-Noetherian-quasi-compact`), and Morphisms 01T5 (`lemma-immersion-locally-finite-type`) and 01T3 (`lemma-composition-finite-type`). The tag-to-label correspondences were checked in the local tag table. This expanded assembly is marked agent-written rather than pretending the source printed all its steps.

For step 1 I opened the statements of `def-weil-affine-spectrum`, `pqf-def-locnoeth`, `lem-weil-pbc-finite-type-over-noetherian` and `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`. The first gives the one-point spectrum of a field and its global coordinate ring. The locally Noetherian definition applies to its single chart: the two possible ideals of a field prove its coordinate ring Noetherian directly. A one-point space is quasi-compact. Thus the finite-type-over-Noetherian statement really applies to C→Spec k. The minimal-closed-subset statement then gives the topological condition needed below: complements reverse inclusion, so the minimal condition implies stabilization of increasing open chains. I do not take topological Noetherianity just from the definition of a Noetherian scheme.

For step 2 I opened `lem-sfb-noetherian-connected-components-open` and `lem-sfb-noetherian-space-compact-subsets`. The former asserts openness under exactly the ascending-chain hypothesis obtained in step 1, and has no separation or smoothness hypothesis. The latter asserts compactness of every subset of the underlying space of a topologically Noetherian scheme, not merely of the entire scheme. Hence it applies to T. Its topology agrees with the one in the item.

For step 3 I opened `def-weil-open-immersion` and `def-weil-connected-scheme`. The former explicitly identifies the open subscheme with (T,O_C restricted to T), giving the same underlying subspace topology. Nonemptiness is witnessed by c, and connectedness is part of the item's definition of its connected component, so this step is elementary. The empty-space convention in the connectedness node is respected.

For step 4 the same all-subsets compactness statement applies to each T∩V, not just to T. I checked `def-weil-finite-type-morphism`: its quasi-compactness clause tests preimages of affine opens. The inverse image here is literally T∩V. Subspace opens are intersections with ambient opens; thus the compactness result supplies exactly the finite subcover needed in the preimage topology. This step is an elementary use of the cited theorem and that definition; it conceals no assertion that compact sources always give quasi-compact morphisms.

For step 5 I opened `lem-weil-pbc-qc-open-immersion-finite-type` and `lem-sfb-finite-type-composition-base-change`. The first assumes precisely an open immersion and quasi-compactness of that morphism, both verified in steps 3–4. The second's first clause gives finite type of the composite once j and C→Spec k have finite type. No use of the second, base-change clause is made. Both are existing Mathlib leaves. The component-openness tool is already Lean-closed; no off-route unsplit theorem is introduced.

I tested the argument on Spec k, on Spec(k[epsilon]/(epsilon^2)), on a disjoint union of two affine lines, and on a connected nonseparated finite-type scheme (the affine line with doubled origin). In the last case the argument still uses no separatedness. If C is empty there is no c, so the universal statement has no instance and does not wrongly assert a nonempty component. No new statement needs separate edge-case testing. Every step is under 2000 characters. I checked B–E: complete statement and citations, no duplicate or clause-restating node, no proof moved into a new node, no unprovided hypothesis or circular citation. No statement correction was necessary. The only substantive repair to the initially missing argument was the explicit affine-preimage check for quasi-compactness of j.
