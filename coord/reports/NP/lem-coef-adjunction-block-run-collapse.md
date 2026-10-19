Files written:

- dag/nodes/sec-six-functors/lem-coef-adjunction-block-run-collapse.json: item, statement split into four elementary proof steps; no new nodes and hence no Mathlib leaves.
- citations.json: empty because every proof step is a direct finite-word argument from the item's own definitions.

Attachments: none.

WANTED: an archival copy of Riehl--Verity, Homotopy coherent adjunctions and the formal theory of monads, Proposition 3.2.2 and proof, pp. 824--825, for the parity and two interval-restriction calculation. The online PDF was read and is cited as the proof source.

The Lean source search in /home/ubuntu/weil-src-slopmaster2/WeilConjectures found no declaration tagged (blueprint: lem-coef-adjunction-block-run-collapse) and no declaration stating this finite-word lemma. The item is therefore split rather than attached. The DAG and blueprint searches found no duplicate node and no separate blueprint statement of this run calculation. The existing four Mathlib searches were rerun with msearch.py; they returned only unrelated Coxeter/free-group reductions or no hits, so mathlib_match remains null.

No statement, definition, hypothesis, or coefficient category was changed. No source error was found.

## Not duplicates

No new node was created, so there is no new-node duplicate pair to report. The item itself is the existing unsplit DAG node; the nearby lem-coef-adjunction-two-block-splicing node is its strict parent and has a different bijection statement.

## Review by NP

I read the item node, its unit sk-prop-sf-biduality-general, the fixed chapter sec-six-functors, the parent lem-coef-adjunction-two-block-splicing, and the definition node def-cbc-enhanced-diagrams-cones. I also checked the slopmaster2 source for an exact finished declaration and found none. The statement's endpoint conventions, alternating inequalities, threshold labels, maps C_h and D_h, and deterministic leftmost reduction were kept verbatim.

Step 1 proves odd run lengths by tracking the parity of each alternating inequality: a 0-to-1 boundary is necessarily upward and a 1-to-0 boundary downward, so the transition parity alternates with the labels; the initial endpoint fixes the first transition parity. The no-transition case is checked from return to the extremal endpoint, which requires an even number of alternating steps. Step 2 applies the odd constant-word reduction to C_h: 1-runs become constant h+1, 0-runs retain strict inequalities, and unequal boundary values prevent cross-run cancellation. Step 3 gives the dual calculation for D_h: 0-runs become constant zero, 1-runs are shifted entrywise with strict inequalities preserved, and positive-versus-zero boundaries prevent cross-run cancellation. Step 4 checks first, last, and singleton runs and explains why the leftmost deterministic reduction is the independent run reduction. Every step uses only the definitions in the item, so the uses arrays and citations.json are empty; there are no uncited external facts. I checked edge cases r=0, h=0, h=r, singleton words, and words with one unbroken run.
