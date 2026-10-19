# Worker report: lem-trf-nodal-etale-chart

Files written:

- `lem-trf-nodal-etale-chart.json` — item, statement node, split; no new nodes.
- `citations.json` — verbatim statement quotes for the three cited DAG nodes.

Attachments: none. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` carries the blueprint tag or states this item.

WANTED: none. The cited Stacks and ILO sources are present in `literature/`.

The imported item had an empty proof and was therefore not already split. I kept its statement and hypotheses unchanged. I did not create child nodes: the smooth, marked, and nodal normal forms are the item's own clauses, and the remaining fine-saturated chart clause is likewise part of the item. Existing DAG lemmas are cited where they supply reusable facts. The required Mathlib searches were run and recorded in `searches.jsonl`; they found only generic smooth/étale declarations and no nodal-family or logarithmic chart theorem.

## Review by Q25

I read the full item statement and its source references, Stacks Project `curves.tex`, Tag 0CBY (`lemma-etale-local-structure-nodal-family`, including both proofs), and Illusie–Laszlo–Orgogozo, Exposé VI, §§1.4 and 1.8 and Proposition 1.9, printed pages 69–71. I also opened the statements of `lem-pur-smooth-pair-local-coordinates`, `lem-trf-nodal-family-fitting-singular`, and `def-trf-log-regular-pair` before writing the proof and checked each quote in `citations.json` verbatim.

Step 1 handles a smooth point outside the Cartier marking: the smooth locus is open and the divisor is closed, so the neighbourhood can be made smooth over the base and disjoint from D. I checked that this uses only the item's flat locally-finitely-presented nodal-family hypotheses and the stated smoothness-away-from T condition.

Step 2 handles a point of D. The marking is etale over Y and is contained in the relative smooth locus, so both the ambient neighbourhood and the marking are smooth over the chosen base. The cited smooth-pair coordinate lemma says exactly that an etale map to affine space cuts out the closed pair by coordinate functions. Relative dimensions one and zero force its parameters to be a=0 and b=1, giving the stated coordinate z and D=(z=0).

Step 3 handles a nonsmooth point. I checked the Tag 0CBY hypotheses against the item's flatness, local finite presentation, and completed nodal fibre condition. The tag gives the etale model `uv=h` and the point u=v=0. Since D lies in the smooth locus it can be removed from this neighbourhood. The cited fitting-singular lemma identifies the nonsmooth locus with the singular subscheme; shrinking inside the open image and using smoothness over Y minus T makes h a unit on V minus T_V. This also verifies that no projectivity hypothesis has been introduced.

Step 4 uses the definition of a fine saturated divisorial log-regular pair to refine the base by a fine saturated chart P→M_Y. The equation h is invertible off T, hence belongs to the divisorial log structure; its chart pushout description writes it as εα(a), with ε a unit and a in P. The same refinement can be pulled back to all three neighbourhoods. I checked the edge cases T empty, D empty, a smooth fibre, and a nodal model `uv=h` with h a unit off T; each normal form specializes as stated. A whole-DAG search for Tag 0CBY and the phrases “nodal local equation”, “etale chart”, and “uv=h” found no duplicate child lemma that says any of the item's clauses.
