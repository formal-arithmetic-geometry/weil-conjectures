## Worker report

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-perturbed-image-artin-rees-bound.json, the existing statement node, now split with six elementary steps. There are no new nodes and no new Mathlib leaves. citations.json is an empty list because no proof step cites another node; the Noetherian definition remains a statement dependency.

Attachments: none. Searched lean/WeilConjectures for the exact blueprint id and for perturbation, approximate-complex and Artin-Rees terminology. The AdicTowerLimit and AdicTowerLattice declarations concern towers, not two perturbed differentials. None states this item.

WANTED: none.

The statement agrees with literature/stacks-project/more-algebra.tex, Tag 07VE, lemma-approximate-complex, first conclusion. The proof uses only its first paragraph, not its second conclusion concerning exactness of the perturbed complex. The item already assumes both image division bounds, exactness of the original complex and the perturbed composite being zero; these hypotheses account for all the substantive inputs. No statement correction was needed.

The inherited blueprint creation chain has no imported ancestor: tools/blueprint_refs.py ancestor lem-sfb-perturbed-image-artin-rees-bound prints None. I retained its existing from.node=null, detailed place and via chain. Read the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.md and its proof, especially (3), and the unit and chapter records. This is a supporting ring calculation far below that route; neither the unit nor the chapter was changed.

Searches: tools/blueprint_refs.py search perturb and search Artin-Rees both returned zero blueprint nodes. Searched the whole DAG for Artin-Rees and Tag 07VE. The latter occurs in this item, its parent lem-sfb-adic-relation-matrix-initial-ideals and lem-sfb-artin-object-graded-approximation. The parent is an equality of initial ideals, and the higher node concerns graded approximation; neither is the present division bound. The general lem-weil-pbc-artin-rees supplies existence of a bound for one fixed map, not preservation of a specified bound under simultaneous perturbation. No new lemma is warranted: the finite induction can be written entirely from the item's own hypotheses.

Ran msearch.py searches recorded in searches.jsonl: LeanSearch for the fixed Artin-Rees perturbation bound, Loogle for range and pow, two LeanFinder phrasings for simultaneous perturbation/uniform division bounds, and grep in RingTheory for approximateComplex, approximate_complex, perturb and exists_pow_inf_eq_pow_smul. All services responded. Read Mathlib/RingTheory/Filtration.lean:389 (Ideal.exists_pow_inf_eq_pow_smul), AdicCompletion/Exactness.lean:185 (AdicCompletion.map_exact), and the adic-map material in AdicCompletion/Functoriality.lean. The first supplies some bound for a fixed submodule, while completion exactness and successive lifting do not preserve a prescribed bound for a second pair of differentials. No match was claimed. Earlier searches inherited from Q54 remain intact, alongside the actual searches of this attempt.

Nothing remains mathematically unfinished in this split. Dry run and delivery are performed after writing this report.

## New nodes

None: each local inference is a direct application of a hypothesis, linearity, ideal multiplication, or finite induction. Creating a one-step improvement lemma would obscure a short explicit argument already carried by the proof steps.

## Not duplicates

No new nodes are proposed. Existing Tag 07VE citers were read as described above; no existing node is modified except this item.

## Review by Q23

I read the source's first paragraph at Tag 07VE with the node open. The source's assumptions are precisely the item's two Artin-Rees inclusions, original exactness, congruences modulo I^(c+1), and the perturbed zero composite. Its finite adjustment establishes only the first conclusion required here. The Noetherian and Jacobson hypotheses may remain unused because the two bounds are hypotheses and the Jacobson condition enters only the source's additional exactness conclusion. I left those hypotheses and the statement text unchanged.

Step 1 chooses a preimage and sets up a bounded induction, rather than assuming a convergent infinite sequence. Step 2 proves the only filtration calculation used later by expanding finite sums and multiplying ideal coefficients; it uses the explicit definition of I^sT in the statement. Step 3 applies the right-map bound at exponent r+c+1, which is at least c; r<n-c ensures r+c+1<=n, giving the necessary descending-power inclusion. Step 4 invokes im f=ker g and applies the left-map bound only when r>=c. When r<c it makes no unavailable bound assertion. Step 5 handles these two cases separately and checks g'(a-f'(b))=g'(a) from g'f'=0. Step 6 terminates after exactly n-c improvements. Each inference is written out from the hypotheses; there are no hidden non-elementary citations, so citations.json is correctly empty. The Noetherian definition node was opened and says that every ideal of a commutative ring is finitely generated; it remains only a statement dependency.

For edge cases I checked n=c (zero improvements), c=0 (the left-map bound is always available), r=c (the exponent r-c is zero), I=0 (all positive powers vanish), and zero L, M or N (all choices and inclusions still make sense). No positivity, injectivity, completeness, separatedness or local-ring hypothesis is introduced. In particular the proof does not use the later Krull intersection argument, which would prove a different conclusion.

Against delivery-errors B--E: there are no new statement-only nodes, no new notions needing definition nodes, and no new-source or duplicate obligations; TeX uses single escaping after JSON decoding. Each step is below 400 characters and spells out its argument. The proof has no dependency edges, hence introduces no cycle or off-unit tool use, and it does not move the conclusion into another node. The original statement, inherited metadata, proof-route origin and literature source are preserved. The repair made here was to expand the imported empty proof into the explicit induction, including the often missed r<c case. This is my author self-review; the maintainer's independent review remains the delivery review required by the brief.
