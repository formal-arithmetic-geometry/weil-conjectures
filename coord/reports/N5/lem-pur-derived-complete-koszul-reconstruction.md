Files written:
- `dag/nodes/sec-smooth-purity/lem-pur-derived-complete-koszul-reconstruction.json` — statement split into four proof steps; no Mathlib leaf.
- `dag/nodes/sec-smooth-purity/lem-pur-regular-element-koszul-quotient.json` — new statement-only regular-element two-term quotient lemma; no Mathlib leaf.
- `citations.json` — verbatim statement quotes for every cited node in every step.

Attachments: none.

WANTED: none.

The item has no exact sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; the keyword and blueprint-tag searches found no declaration for this item. The nearest existing blueprint result is the proper-base-change lemma `lemma-weil-pbc-koszul-quotient-limit`, but it is formulated for constant Noetherian coefficient sheaves and a different adic datum. It does not state the arbitrary ringed-site principal-element comparison here, so I did not duplicate it or use it as a citation. The generic levelwise-Roos-isomorphism node is used only as a tool in the final triangle argument, as recorded in `split_report.tool_uses`.

## Not duplicates

- `lem-pur-regular-element-koszul-quotient` vs `lemma-weil-pbc-koszul-quotient-limit`: the new node is the principal regular-element calculation for an arbitrary sheaf of rings and explicitly gives the two-term quotient augmentation and its strict transitions; the existing node concerns a Noetherian constant coefficient datum, arbitrary finitely generated ideal, and derived-limit comparison.
- `lem-pur-regular-element-koszul-quotient` vs `lem-pur-derived-complete-koszul-reconstruction`: the new node states only the levelwise two-term augmentation quasi-isomorphism and transition compatibility; the item additionally tensors with an arbitrary K-flat representative, compares derived limits, and reconstructs a complete object from a Roos triangle.
- `lem-pur-regular-element-koszul-quotient` vs `lem-weil-pbc-constant-completion-equivalence`: the existing node treats constant Noetherian coefficient sheaves, all generators, and a completion equivalence; the new node treats an arbitrary ringed site and one regular global element and states the explicit two-term quasi-isomorphism.
- `lem-pur-regular-element-koszul-quotient` vs `lem-weil-pbc-ringed-koszul-completion-reflector`: the existing node gives the reflector/universal property of a multi-generator Koszul completion; the new node gives the principal-element Koszul-to-quotient augmentation and its strict tower maps, with no reflector conclusion.

## Review by N5

I read the imported item node, its source note, the `sk-thm-sf-compatibility` unit route, and the relevant Stacks passages: algebraization.tex Tag 0A0E for the Koszul construction and sites-cohomology.tex Tag 0941 for strict tower derived limits and Roos triangles. I also read every statement cited by the four proof steps: the new regular-element lemma, the K-flat and total-tensor definitions, the abstract derived-category definition, levelwise exactness of tower evaluation, the ringed strict-tower homotopy-limit theorem, the derived-limit definition, and the generic levelwise-Roos-isomorphism lemma.

Step 1 checks the only algebraic hypothesis that matters: injectivity of multiplication by $t$ implies injectivity of every $t^m$, so the two-term complex has vanishing degree $-1$ cohomology and quotient $B_m$ in degree $0$. The transition maps have the stated multiplication-by-$t$/identity form and commute with both differentials and quotient maps. Step 2 chooses the already required K-flat representative $P$ and explicitly identifies the cone after tensoring; K-flatness makes it acyclic, so each $a_m$ is a quasi-isomorphism. The strict transition compatibility is checked before localization. Step 3 uses exact evaluation of the tower category to detect the quasi-isomorphism and then applies the cited exact derived-limit functor. Step 4 uses the given Roos triangle for $K$, the canonical Roos triangle for the Koszul tower, and the product of the level maps to obtain a morphism of triangles by the triangulated completion axiom. Its projection equations give the required quotient maps, and the cited levelwise-Roos lemma proves the first component is invertible and identifies the triangles.

I checked the short steps for hidden lemmas and kept the only non-elementary auxiliary fact—the regular-element two-term quotient calculation—as its own node. The longest proof step is under 2,000 characters and contains one routine triangle-completion argument. Edge cases checked in the statement are $t$ a unit (all $B_m=0$ and the towers are contractible), $K=0$, $m=1$, and a complex $P$ concentrated in degree zero. No statement or hypothesis was changed, no SGA source was used, and no Lean or build tool was run.

What I could not finish: no Lean proof was attempted, as this is the authorized stage-1 natural-language DAG work only.
