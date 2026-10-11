Files written:

- `dag/nodes/sec-picard-framework/lem-pc-ring-pseudo-coherent-localization-glue.json`: repaired statement node and induction proof.
- `dag/nodes/sec-picard-framework/lem-pc-ring-m-pseudo-coherent-vanishing-base.json`: Tag 064W statement-only node.
- `dag/nodes/sec-picard-framework/lem-pc-ring-pseudo-coherent-iff-all-m.json`: Tag 064U statement-only node.
- `citations.json`: verbatim citations for every node used by every proof step.

Attachments: none.

WANTED: none.

What was wrong and what was repaired: the former definition node incorrectly identified Tag 064N with a bounded-above projective model, making the all-m equivalence false. It was removed, and both support statements now use the exact inline finite-free definition from the existing triangle node. Step 1 now fixes an arbitrary m, gets local m-pseudo-coherence from the (1)=> (2) direction of the all-m node, notes the n>=m shift, and states the induction on n-m. Step 3 concludes directly from the (2)=> (1) direction, with no finite reversal of infinitely many cones. The item source now reads through Lemma 15.66.5, Tag 064U; stale references to absent top-finite and cone files were removed.

## Not duplicates

`lem-pc-ring-m-pseudo-coherent-vanishing-base` vs `lem-pc-pseudo-coherent-bounded-finite-free-model`: the new node is the Tag 064W m-pseudo-coherence base implication; the existing node constructs a finite-free model under pseudo-coherence and an upper cohomology bound.
`lem-pc-ring-m-pseudo-coherent-top-finite` vs `lem-weil-pbc-module-finite-of-localization-span`: the new node derives finiteness of top cohomology from m-pseudo-coherence; the existing Mathlib leaf glues already-finite localizations.
`lem-pc-ring-m-pseudo-coherent-cone` vs `lem-sc-cone-pseudo-coherent`: the new node states the symmetric bounded-above two-out-of-three theorem for the explicit m-pseudo-coherent complex definition; the existing node is the one-directional distinguished-triangle implication with a different derived-category definition.
`lem-pc-ring-m-pseudo-coherent-cone` vs `lem-pc-ring-pseudo-coherent-distinguished-triangle`: the new node is the Tag 064R module-complex m-pseudo-coherence cone statement used for this induction; the existing node has the scheme-level plain pseudo-coherence conclusion and does not state the m-bounded invariant.
`lem-pc-ring-m-pseudo-coherent-top-finite` vs `lem-sc-finite-cohomology`: the new node uses the Tag 064S top-degree formulation for an m-pseudo-coherent module complex; the existing node packages a different derived-category definition and additionally assumes vanishing above m.
`lem-pc-ring-m-pseudo-coherent-cone` vs `lem-pc-pseudo-coherent-distinguished-triangle`: the new node is the m-pseudo-coherent cone theorem for complexes of modules; the existing node concerns plain pseudo-coherence of derived objects on schemes.
`lem-pc-ring-pseudo-coherent-iff-all-m` vs `lem-pc-pseudo-coherent-bounded-finite-free-model`: the new node is the Tag 064U equivalence for every integer m; the existing node is only a bounded finite-free model construction.

## Review by E1

I read the returned item, the ancestor blueprint sentence in `lem-sc-finite-duality`, the existing triangle and finite-cohomology nodes, and the source places for Tags 064R, 064S, 064U, 064W, and 066D. For Step 1 I verified the arbitrary fixed m, the local all-m implication over each A_fi, the n>=m shift, the vanishing base, top cohomology finiteness, and the unit-ideal finite-module gluing. For Step 2 I verified that the cited triangle statement has the exact finite-free definition and the two clauses used, and checked the elementary shift E[-n] and degree drop. For Step 3 I checked that the all-m node itself defines pseudo-coherence as a bounded-above finite-free model. I removed the false 064N definition and stale report entries, corrected the source to 064U, and rewrote citations to quote the retained node statements verbatim. Small cases checked include a one-element cover with f_1=1 and the zero complex.

What could not be finished: no Lean implementation exists in the source checkout; this remains a stage-1 statement split.

## Second reading by E1

I read Tag 066D (label `lemma-glue-pseudo-coherent`) in `more-algebra.tex` and checked the item hypothesis by hypothesis against its finite-free localization statement. I checked Step 1 against exact localization, the unit-ideal vanishing criterion, Tag 064S, and the finite-module localization node; the global upper bound and the top-degree choice are now explicit. I checked Step 2 against the cone long exact sequence and the existing full Tag 064R node; its shifted hypotheses are stated rather than replaced by an informal two-out-of-three claim. I checked Step 3 against Tag 064U and the finite-free replacement conclusion.

The false Tag 064N definition node was removed rather than cited. The vanishing-base node was repaired to use the same finite-free inline definition as the triangle node. The item no longer carries an unnecessary definition dependency; its induction and conclusion now use only the retained all-m node and existing triangle/finite-cohomology/localization nodes. Small cases checked: the zero complex, a one-element cover with the element equal to 1, and bounds above all local cohomology.

## Second reading by E1

I re-read Tag 066D (label `lemma-glue-pseudo-coherent`) in `more-algebra.tex`: its statement has both the fixed-$m$ and pseudo-coherent clauses. The item now states both clauses, with the ring-level $m$-pseudo-coherence definition inline and the finite-free pseudo-coherent definition from Tag 064U. The new all-$m$, vanishing-base, and triangle nodes were checked against Tags 064U, 064W, and 064R; their hypotheses and finite-free wording agree. Step 1 is the fixed-$m$ induction, Step 2 is the cone induction, Step 3 derives the pseudo-coherent clause by applying Step 1 for every $m$ and Tag 064U. The localization, top-degree, cone-vanishing, and finite-module hypotheses were checked at each use. Small cases checked: the zero complex, a one-element cover with $f_1=1$, and $n<m$.

Changed the item title, statement, source place, statement dependency, proof, and citations to restore the omitted fixed-$m$ clause and to renumber citations after adding its induction step. No new nodes were added or removed in this second reading.
