Files written:

- `lem-sc-deg-pullback-finite.json`: repaired split item, 0 Mathlib leaves.
- `lem-sc-generic-rank-leading-degree.json`: repaired statement-only child, no Mathlib match.
- `citations.json`: refreshed verbatim quotes for all cited nodes.

Attachments: none. `AlgebraicGeometry.Scheme.Hom.degree_pullback` remains non-attachable because its proof rests transitively on sorry-backed declarations.

WANTED: none.

The return identified five faults. I added affine cohomology (Tag 089W) and the existing affine pullback-ampleness statement (Tag 0892) to Step 1 and declared them as tool uses, and replaced the derived pushforward comparison by the ordinary finite pushforward comparison before applying the projection formula. Step 2 now explicitly states coherence of `f_* O_X`, generic freeness of rank `[k(X):k(Y)]`, and dimension equality via `lem-sc-finite-surjective-dimension`; the Hilbert-polynomial devissage parenthetical and its dependency were removed. The generic-rank child now states only the m^g coefficient (for g = dim Y, equivalently g! times that coefficient) and cites the actual Section 33.44 intersection-number/pullback argument rather than misdescribing the 0BEX proof.

## Review by H1

I reread Stacks Varieties Lemma 33.45.11 (Tag 0BEX), Morphisms Lemma 0892, and Cohomology Lemma 089W, plus the existing DAG statements for affine pullback ampleness, affine cohomology, projection formula, and finite-surjective dimension. Step 1 uses each cited statement for exactly the displayed well-definedness, cohomology, and tensor/direct-image comparison. Step 2 uses the generic-rank child only for its m^g coefficient assertion, the dimension node for dim X = dim Y, and the degree definition for the g! extraction. I checked that f finite implies affine, that Y is noetherian, and that the finite pushforward is generically free on a nonempty open. The child source now records the Section 33.44 intersection-number/pullback argument and explicitly fixes g. I tested the zero-dimensional case, where the coefficient convention gives the expected constant degree.

## Not duplicates

- `lem-sc-generic-rank-leading-degree` vs `lem-sc-deg-pullback-finite`: the child concerns an arbitrary coherent sheaf's generic-rank coefficient on one proper integral scheme; the item concerns degree under a finite morphism and additionally uses affine cohomology, projection formula, and function-field rank.

## Second reading by H1

- Item statement checked against Varieties Lemma 33.45.11 (Tag 0BEX), label `varieties-lemma-degree-finite-morphism-in-terms-degrees`: finite dominant morphism of proper integral varieties, ample invertible module, function-field degree, and Hilbert/intersection degree all agree hypothesis by hypothesis.
- Step 1 checked against Morphisms Lemma 0892 and Cohomology Lemma 089W: finiteness gives affineness, pullback ampleness is available, affine cohomology identifies Euler characteristics, and the cited projection formula gives the ordinary pushforward comparison after specializing to an invertible tensor factor.
- Step 2 checked against Tags 0517 and 0GWM plus the cited dimension and degree nodes: on an affine generic neighborhood, finite pushforward is a finite module, hence finitely presented; its generic localization is the field extension of rank `[k(X):k(Y)]`, and 0GWM spreads that freeness to a nonempty principal open before the generic-rank coefficient node is applied. Dimension equality supplies the same `g`, and the degree definition supplies the `g!` extraction.
- Child `lem-sc-generic-rank-leading-degree` checked against the Section 33.44 intersection-number/pullback argument used by Tag 0BEX: it is statement-only, self-contained, and asserts exactly the generic-rank leading-coefficient comparison. Its zero-dimensional case gives the expected constant coefficient; a field and a free sheaf give rank-one and rank-`r` checks.
- No duplicate child was found: the child is a generic-rank coefficient lemma, while the item is the finite-morphism degree formula.
- Small cases checked: `g=0` (degrees are constant Euler characteristics), a finite field extension of `Spec k`, and the identity morphism; all give the stated equality.
- Changed Step 2 to supply the missing non-elementary generic-freeness argument; added citations and proof dependencies for `lem-sc-noetherian-finite-module-finite-presentation` and `lem-sc-finitely-presented-free-at-prime-principal`, and recorded both as existing tool uses. Refreshed their verbatim quotes in `citations.json`.
