Files written:

- `lem-pod-projective-hom-evaluation-model.json`: item split into five proof steps; no new nodes.
- `citations.json`: verbatim citations for every node used by every step.

Attachments: none.

WANTED: none. The proof source is available in `literature/stacks-project/more-algebra.tex`.

The imported item was unsplit and had no Lean declaration. I kept its statement, hypotheses, coefficient category, totalization convention, naturality clauses, and the explicit Koszul sign. No duplicate node was created: the existing DAG has generic K-flat tensor and projective-derived-morphism statements, but no node that states this full module-complex Hom model together with its evaluation map. Mathlib has K-projective localization infrastructure, but no exact theorem for the complete statement.

## Review by Q104

I read the item, the `sk-thm-derived-duality` unit and its parent node `lem-pod-cohomology-of-dual-over-field`, together with Stacks Tags 0A66 (RHom out of a bounded-above projective complex), 0A5W (derived internal Hom), 0A5Y (Hom-complex composition), 0GWQ (internal-Hom evaluation), 0FNG (Koszul signs), and 0A8H (Hom-complex construction). I also opened the statements of every cited DAG node. Step 1 uses exactly the projective-is-flat statement and the bounded-above-flat-implies-K-flat statement; the hypotheses match termwise projectivity and the stated upper bound. Step 2 uses the product-total Hom definition, its homotopy-class cohomology equivalence after shifting the target, and the bounded-above-projective derived localization bijection. These give the comparison in every degree and its contravariant/covariant functoriality. Step 3 applies the existing K-flat tensor-model statement with P as first factor; its statement explicitly permits an arbitrary unbounded second complex. Step 4 checks the displayed signed evaluation against the Hom differential and total tensor differential, then identifies it with the counit through the source Hom–tensor adjunction construction. Step 5 checks naturality by the same precomposition, postcomposition and tensor formulas. I tested the edge cases P=0, P=R[n], N=0, an unbounded N, and a non-finitely generated free projective term; each formula remains defined and no step uses finite generation or boundedness of N. The Mathlib searches were rerun with Q104 and recorded in `searches.jsonl`; they found only general K-projective/evaluation infrastructure, so the item remains a non-Mathlib split.
