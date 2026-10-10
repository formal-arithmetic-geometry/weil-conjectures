Files written:

- dag/nodes/sec-curve-estimates/lem-weil-pbc-complex-spectral-sequence-comparison.json: split statement; no Mathlib match.

Attachments: none.

WANTED: none.

What was wrong or incomplete: the imported item had no proof and no proof dependencies. The earlier delivery specified only the bidegree of $d_1$, although the definition permits arbitrary shapes on later pages. It also cited a theorem about filtered complexes for an abstract spectral sequence and used that theorem's bidegree in the wrong indexing. The statement now requires $d_{r,i},d_r:E_r^{p,q}\to E_r^{p-r+1,q+r}$ for every $r\geq1$. Without that condition, a later differential can kill a class in each finite-stage spectral sequence at increasingly late pages while the colimit spectral sequence retains it. The parent application uses hypercohomology spectral sequences of the stupid filtration, which have the required bidegree.

What could not be finished: nothing.

## Review by F1

I read Etale Cohomology Lemma Tag 0EZM (lemma-colimit-variant-complexes) and checked its bounded-below hypercohomology spectral sequences against the item's abstract statement. I read the existing statements of lem-weil-pbc-filtered-colimit-abelian-groups-exact, def-sp-spectral-sequence, and lem-weil-pbc-five-lemma; no new node was needed. The Lean source was searched by the item id and blueprint tag; no exact declaration exists.

Step 1 cites filtered-colimit exactness for commuting colimits with kernels and images, and the spectral-sequence definition for the page-to-page homology identification. Those statements say exactly the facts used. Starting from the assumed E_1 isomorphism, induction gives the pagewise isomorphisms.

Step 2 cites no external node: its bidegree, vanishing region, stabilization, convergence isomorphisms, and compatibility with the maps are all hypotheses of the corrected item. At $(p,q)$ the outgoing target is $(p-r+1,q+r)$, zero for $r>p+1$, and the incoming source is $(p+r-1,q-r)$, zero for $r>q-a$. Thus $R(p,q)=\max(p+1,q-a)+1$ works for every index $i$ and the limit sequence. Step 1 at this same finite page and the assumed compatibility give the graded abutment isomorphism. The previous citation to thm-sp-spectral-object-yields was removed because its statement concerns a filtered complex, while this item quantifies over abstract spectral sequences; its indexing also put the shifts in the opposite coordinates.

Step 3 cites exactness of filtered colimits for the short exact sequences of successive filtration quotients and the five lemma for the induction. I checked both endpoint hypotheses: the filtration is zero above n and equal to the whole abutment at q<=a, so only the finite range a<=q<=n is involved. Small checks were made on a constant one-object system (the map is the identity), zero spectral sequences, and a complex concentrated in the lower-bound degree (the conclusion reduces to the E_1 comparison).

The blueprint reference was retained from the imported item: the ancestor is prop-weil-pbc-strict-henselization-stalk-formula, and the split realizes its sentence about the derived statement via the finite spectral-sequence comparison. I tested zero sequences, a single-stage constant system, and the returned counterexample with an increasingly late nonzero differential. The new bidegree excludes that counterexample; the finite-page bound then handles every bidegree. I also checked the filtration endpoint hypotheses in Step 3, the cited statements against their uses in Steps 1 and 3, and the absence of literal backslash-n text in Steps 2 and 3.
