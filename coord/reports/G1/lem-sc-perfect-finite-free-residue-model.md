Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-perfect-finite-free-residue-model.json` — statement, split; Mathlib searches found no match.
- `dag/nodes/sec-abelian-varieties/lem-sc-perfect-pullback-perfect-residue.json` — statement-only child; Mathlib searches found no match.
- `dag/nodes/sec-abelian-varieties/lem-sc-perfect-local-pseudocoherent-free-model.json` — statement-only child; Mathlib searches found no match.
- `citations.json` — verbatim statement quotes for every cited node and step.

Attachments: none.

WANTED: none.

No statement error was found. The imported item had no proof; its source proof uses Tag 0BCC locally and Tag 0BC7 for descent. The field splitting input is the existing generic `lem-pod-perfect-point-complex-field`, declared as a tool use rather than duplicated. Step 3 now combines the existing affine filtered-colimit descent node with the existing finite-projective standard-cover node to obtain a principal open on which every term is finite free.

## Review by G1

I read Tag 0BCD in `/home/ubuntu/c1-stacks-review/more-algebra.tex` and the preceding Tag 0BCC proof. I also read the existing `lem-pc-affine-perfect-colimit-descent` statement and the generic field-splitting node before citing them. Step 1 checks that the affine residue fibre is perfect by the new pullback node, then takes finite-dimensional cohomology ranks and finite support from the field-splitting statement. Step 2 checks that the local-ring hypotheses of the new pseudo-coherent model node hold for a perfect complex and that the ranks are precisely the $d_i$ from the item; finite support from Step 1 turns its bounded-above model into a bounded one. Step 3 checks that the index category of principal localizations is directed, that the local model is a bounded finite-projective complex, and that the existing colimit node supplies a bounded model over some $A_f$; $f\notin\mathfrak p$ makes $D(f)$ contain $x$. I corrected the imported empty proof, added the missing proof dependencies, declared the two off-unit generic tools, and recorded exact quotes in `citations.json`. Small cases checked include $E=0$ (all $d_i=0$), $E=\mathcal O_X$ (rank one in degree zero), and a bounded complex already free near $x$.

## Second reading by G1

- Item statement: checked against More on Algebra Tag 0BCD (`lemma-lift-perfect-from-residue-field`), including the prime-local fibre dimensions, finite nonzero range, and affine localization conclusion; verdict: agrees hypothesis by hypothesis.
- Step 1: checked against Tag 0BCD and the statements of `lem-sc-perfect-pullback-perfect-residue` (Tag 066W) and `lem-pod-perfect-point-complex-field`; verdict: the derived residue fibre is perfect and therefore has finite-dimensional cohomology with finite support, exactly what the step uses.
- Step 2: checked against Tag 0BCC (`lemma-lift-pseudo-coherent-from-residue-field`) and the definitions cited in the new node; verdict: localization of a perfect complex is pseudo-coherent, the rank data are the stated fibre dimensions, and finite support makes the bounded-above representative bounded.
- Step 3: checked against Tag 0BC7 (`lemma-colimit-perfect-complexes`) and `lem-weil-pbc-finite-projective-standard-free-cover`; verdict: principal localizations form the required directed colimit, the bounded finite-projective complex descends, and a principal neighborhood of the prime makes its finitely many terms free without changing their ranks.
- New node `lem-sc-perfect-pullback-perfect-residue`: checked against Tag 066W; statement is self-contained with its perfect-complex definition citation, TeX is valid, and no existing or Mathlib duplicate was found.
- New node `lem-sc-perfect-local-pseudocoherent-free-model`: checked against Tag 0BCC; statement is self-contained with all local-ring, derived-category, and pseudo-coherence notions cited, and no existing or Mathlib duplicate was found.
- Existing dependencies: read the full statements of `lem-pc-affine-perfect-colimit-descent`, `lem-weil-pbc-finite-projective-standard-free-cover`, and `lem-pod-perfect-point-complex-field`; each says the fact used, with no proof-only reliance or cycle.
- Small cases: checked the zero complex, a field with a one-dimensional degree-zero complex, the zero ring/empty affine open, and a model already free near the prime; all conclusions reduce correctly.
- Changes: corrected the sandbox copy's stale `created.item` metadata to this item and added this second-reading section; no mathematical statement or proof step required repair.

