# Q57 stage-1 report: lem-sfb-finite-profile-rank-open

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-profile-rank-open.json: statement node, now split in five steps; Mathlib searches found no exact match. The statement and its statement dependencies are unchanged.
- citations.json: verbatim statements for every node cited by every proof step.
- searches.jsonl: five fresh searches made with the required msearch.py command, retaining the item's earlier search records as source history.

New nodes: 0. New Mathlib leaves: 0. The DAG already supplies the non-elementary inputs, so no elementary finite-set observation or clause of the item was extracted into a node.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for finite-profile and rank-open terminology. PushforwardRankOnOpen and the Picard rank-neighbourhood modules concern finite locally free morphisms or reference bundles, not this statement about arbitrary coherent modules and universal closed rank loci.

## Wanted literature

WANTED: Grothendieck, Bourbaki Expose 221, Techniques de construction IV: les schemas de Hilbert, Lemmas 3.5 and 3.6, printed pp.263--264, archival local PDF for lem-sfb-finite-profile-rank-open. The node's named local PDF is absent. I read the primary Numdam scan at https://www.numdam.org/article/SB_1960-1961__6__249_0.pdf, PDF pages 15--16 (zero-based), including the surrounding Lemma 3.4 argument. The report preserves the wanted designation; no literature file was written. The proof is explicitly agent-origin.

## What was wrong and what changed

The item had a complete statement but no proof or proof dependencies. It now has the finite-profile argument and references the existing coherent-universal-rank-locus statement, rather than duplicating its Fitting-ideal construction. Every W_d is open; the finite bad-profile witnesses identify their infinite intersection with a finite intersection. The proof then verifies Noetherianity and coherence on V, applies the rank-locus theorem there, and explicitly constructs the final factorization through the open V.

There is no statement dispute, no changed hypothesis, and no change of route. The newest blueprint is literature/blueprint/latest (main-20261023-1620). I read its six-functors-basics chapter, sk-thm-sf-ctf-stability unit and direct-image proof. This item remains a subsidiary Hilbert-construction prerequisite along its recorded alteration ancestry. Its inherited blueprint.from.node is null; tools/blueprint_refs.py ancestor reports None for the current created.item chain. I retained that field and its detailed place and via list; no invented ancestor was supplied. Whole-blueprint searches for finite profile and 05P8 found no imported equivalent; the fibre/rank search found broader unrelated nodes. No blueprint source is replaced with an older snapshot.

## Mathlib searches

The fresh searches and exact queries are in searches.jsonl and appended to the item. Both LeanFinder phrasings returned freeLocus, rankAtStalk and nearby algebra results. LeanSearch returned finite fibres, local frame finiteness, quasi-coherent presentation data, finite intersections of opens and ideal-sheaf lattice results. Loogle with Module.rankAtStalk, IsOpen had no hits. The mandated grep for Fitting/fitting/finite profiles/rank loci in AlgebraicGeometry had no hits. I read Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean around isOpen_freeLocus and isLocallyConstant_rankAtStalk_freeLocus: these concern the free locus of the original module, and the global locally constant rank theorem assumes flatness. They do not represent pullbacks becoming locally free, and they do not supply this finite-profile theorem. The second phrasing was run before concluding no match. These are real searches, not reconstructed search claims.

## Not duplicates

No new node is created. The existing lem-sfb-coherent-universal-rank-locus is deliberately reused; it supplies individual ranks and arbitrary test schemes but not the simultaneous finite-profile argument. The existing lem-sfb-noetherian-open-closed-finite-presentation is deliberately reused for the geometry of V. I also read lem-weil-pbc-coherent-module-local-on-open-cover and lem-weil-pbc-open-immersion-module-pullback-restriction; no duplicate of either is created. Coherence restriction is the two-line definition argument written in step 3, rather than a new node.

## Review by Q57

I read delivery-errors B through E in both copies, then checked the actual node statements and source texts. For the item I read Bourbaki 221 Lemmas 3.5--3.6 in the primary scan and Stacks divisors.tex, Tag 05P8, lemma-locally-free-rank-r-pullback, its three clauses and proof. The latter handles every morphism T to S without a Noetherian condition on T. I also read properties.tex Tags 01OW (lemma-locally-Noetherian) and 01OZ (lemma-Noetherian-topology), and modules.tex Tags 01BV (definition-coherent) and 01B5 (definition-finite-type). No new nodes need further source readings. No forbidden SGA source is used.

Step 1 uses the first assertion of lem-sfb-coherent-universal-rank-locus. Its statement says precisely that the residue-fibre dimension upper-bound subset is open. The Noetherian base, coherent module and nonnegative integer hypotheses are the item's hypotheses for every d at least m. No free-locus theorem is being substituted for this assertion.

Step 2 uses only finite-set membership and inequalities. For a point s violating any bound, h_s is in H and in the bad subset B. The preselected witness for this very profile is one of the finite tests, giving the contradiction. This proves both inclusions, including profiles in H never realized by a point. No compactness assertion is used for an infinite intersection of opens.

Step 3 uses exactly the locally Noetherian and quasi-compact-open-immersion clauses of lem-sfb-noetherian-open-closed-finite-presentation. Its closed immersion is chosen to be the identity of V, so no existence of a nontrivial closed subscheme is presumed. Quasi-compactness of V follows by taking the inverse images of a finite affine cover of S under that quasi-compact map. I checked pqf-def-coherent: finite type is local finite generation, and the kernel requirement is quantified over every open. The latter quantifier includes every open of V, so restriction inherits the condition. This short argument is written out, not treated as an unstated general pullback-coherence theorem.

Step 4 uses the final closed-in-S clause and full universal property of lem-sfb-coherent-universal-rank-locus, now with base V. Step 3 verifies its Noetherianity and coherence hypotheses. Step 2 verifies all fibre dimensions are at most r_d, since open restriction has the same local rings and stalks at its points. The cited statement explicitly gives a quasi-coherent defining ideal, a closed immersion and the equivalence for every test scheme. It says locally free of rank r_d, not merely constant fibre dimension; no flatness has been inserted.

Step 5 reapplies that universal property on the original S separately for each d. This gives actual factorizations through W_d, so it does not rely on an unproved residue-field dimension base-change theorem. To combine them it only needs the set-theoretic image in the finite intersection. I wrote out the scheme map to V: the same point map, structure maps restricted to opens of V, identical local stalk maps, and uniqueness. def-weil-open-immersion says explicitly that V has the restricted structure sheaf and embeds as its open subset. Thus no unsupported claim that arbitrary immersions factor from their pointwise image is made.

C4: every cited node was opened and read; citations.json copies its actual statement verbatim. C1: every non-elementary input is one of those cited statements. B1--B9: no new unsplit objects, no proof hidden inside a new statement, and all searches and blueprint fields are retained honestly. D1--D5: the finite-profile proof is in the item, not moved to a renamed clause. E1--E7: the hypotheses were checked at each use, and no coherence preservation under arbitrary pullback is assumed. Every proof step is below 2000 characters, so there is no long-step hidden lemma.

Small cases checked: empty S and empty V; empty H (then S must be empty); H with no bad profile; unused bad profiles in H; repeated witness degrees; m=0; all r_d=0; and arbitrary nonreduced or non-Noetherian test schemes. For F=A/(x) on Spec A with A=k[x], the rank-one condition is closed after the bounded-generator open, whereas rank zero is the open complement of x=0. For A=k[epsilon]/(epsilon^2) and F=A/(epsilon), constant fibre dimension one does not imply freeness; the representing closed rank-one locus is Spec k. This checks that the proof really keeps the scheme structure and does not replace the universal condition with fibre dimensions. With F=0 and r>0, the rank locus is empty and only the empty test scheme can satisfy the condition, as required.

## Unfinished work

None for this one-level split. The existing cited nodes retain their own independent queue and review states. No Lean file was written, no compiler or Lake command was run, and no repository or launcher file was changed.
