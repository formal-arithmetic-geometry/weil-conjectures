# Q96 stage-1 report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-scalar-cochain-retraction.json: statement split into six steps; no new nodes; no new Mathlib leaves. Statement and statement dependencies retained exactly.
- citations.json: the sole step/node citation, copied verbatim from the naturality statement.
- searches.jsonl: actual msearch.py results; previous searches retained in the item's JSON.
- report.md: this report.

## Attachments

None. Searches for the exact blueprint tag and for scalar/cochain/retraction concepts in lean/WeilConjectures found no declaration stating this item. The existing homogeneous/inhomogeneous coordinate theorem in RepresentationTheory/HomogeneousInhomogeneousContinuousCohomology.lean assumes compact Hausdorff totally disconnected groups and discrete coefficients, and ContinuousCohomologyCoefficientEquiv.lean treats coefficient equivalences and iterated coinduction. Neither states this scalar retraction theorem with its full hypotheses and conclusions.

## WANTED

None. The proof is explicitly agent-written. Its cochain convention is read in Stacks Tag 0DVG (etale-cohomology.tex, section-continuous-group-cohomology, lines 9007–9032), rather than attributed to a theorem there asserting scalar projections.

## Findings

The item is true as written. There was no previous sandbox split, proof, report or search log to resume. The inherited statement already supplies precisely the field continuity and E-linearity needed. No statement dispute or route change was necessary. The latest blueprint paragraph (3) is the parent direct-image route; it does not contain the arithmetic expansion, so the proof origin is agent, not document. The inherited unit record names sec-six-functors whereas this item is in sec-six-functors-basics; the latest blueprint places the unit in the latter. These maintainer-owned fields were not changed. The blueprint ancestor tool returns None, as the item's existing blueprint.from.node records; its specific from.place and via chain are retained. Searches for retraction and cochain across the blueprint found no equivalent full statement.

Read the results of all six current msearch calls (LeanFinder twice, Loogle, LeanSearch, grep twice). No service was unavailable. The semantic services return the older ContinuousCohomology.homogeneousCochains/iterated induction API, and the local grep identifies the current TopRep homogeneous complex and ContinuousCohomology.cochainsMap. Read ContCohomology/Basic.lean and Functoriality.lean: their iterated C(G,C(G,...)) representation and abstract coefficient functoriality do not prove the full statement here in one line; they do not supply its finite-coordinate scalar retraction or arbitrary-group joint-coordinate comparison. The second semantic phrasing gives normed complete-field basis continuity facts, which have hypotheses absent here. The mapping-cone projection hits are unrelated. Existing naturality is stronger and more directly applicable than adding a new specialized cochain lemma.

## Not duplicates

No nodes created. Reused lem-sfb-joint-continuous-coordinate-naturality; retained lem-sfb-topological-homogeneous-cochain-coordinates as the statement dependency defining the convention. Checked the transitive statement/proof dependencies of both: neither reaches this item.

## Review by Q96

I read delivery-errors B–E, the stage-1 brief and stage contract, the three-level route policy, GOAL.md, the chapter and unit records, the latest chapter/unit text and the latest direct-images proof paragraph (3). For the cochain definitions I read Stacks Tag 0DVG, section-continuous-group-cohomology, including the degree-zero formula and the warning that topological-coefficient cochains need not be exact. No exactness assertion is used here. I read the complete statements of both the homogeneous-coordinate convention node and the simultaneous naturality node, and the latter's coefficient-map/restriction hypotheses and four displayed identities. No new node requires an additional source.

Step 1 is an elementary coordinate continuity argument: evaluating the assumed jointly continuous action at each fixed standard basis vector proves continuity of each matrix entry in E. Its image is continuous in F and L because the field inclusions are assumed continuous. Finite sums and products give joint continuity, without assuming the inclusions are topological embeddings or using a compact-open exponential law. Matrix identities survive the field maps, so these are genuine actions. This also checks the topological E-vector-space assumptions needed later.

Step 2 uses only the given p: coordinate evaluation proves continuity; E-linearity pushes p through the finite matrix sum because every matrix entry lies in E. I checked that F-linearity and multiplicativity are never used. The inclusion is equivariant by the same formula, and subtraction gives Q. The identities Pi=1 and Qi=0 follow coordinatewise, including the empty coordinate set.

Step 3 is the only non-elementary invocation. It cites lem-sfb-joint-continuous-coordinate-naturality, whose statement explicitly provides postcomposition maps, preservation of continuity and equivariance, both differential identities and the two coordinate-map squares. Apply it three times with the identity homomorphism and the coefficient maps P,i,Q. Steps 1 and 2 establish every hypothesis, with the correct domains and codomains. citations.json quotes the actual hypothesis and conclusion block verbatim. This takes no information from that node's proof.

Step 4 checks each remaining projection identity pointwise, so there is no hidden assertion that an arbitrary functor preserves subtraction. Step 5 writes restriction as precomposition in each argument; it verifies subgroup continuity by the induced topology and then the commutation square by evaluating both sides. Cocycles remain cocycles by linearity and step 3's differential identity, and the claimed vanishing is Qi=0 at each value. Step 6 verifies empty finite powers and degree zero. For k=0 the inhomogeneous differential is gv-v, so it still commutes with each equivariant linear coefficient map. I checked the trivial group, F=L (then p=id and Q=0), E=F with a nonmultiplicative linear p, and d=0; none needs a missing hypothesis. For example p: C→R given by real part with E=F=R has p(i²)=-1 but p(i)²=0, while the proof still works for real-valued action matrices.

Against B and D, no new standalone nodes repackage a clause or elementary calculation; the only substantial cochain tool already exists. Against C, each cited result says exactly what step 3 uses, and its citation is backed by the actual statement text. Against E, all topologies are those stated, arbitrary subgroups have their induced topology, and no discreteness, Hausdorffness, local compactness or completeness is inserted. Each proof step is below 2000 characters; none hides a separate standard comparison. The proof dependencies are exactly the union of uses. No Lean was written, no compiler or build was run, and no file outside this sandbox was written.

## Unfinished work

None in the mathematical split. Server validation and direct delivery follow this report.
