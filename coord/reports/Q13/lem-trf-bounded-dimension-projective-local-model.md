## Files written

- `dag/nodes/sec-trace-formula/lem-trf-bounded-dimension-projective-local-model.json` — statement split into five proof steps; no Mathlib leaf.
- `dag/nodes/sec-trace-formula/lem-trf-local-quasi-finite-projection.json` — new unsplit statement node; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-finite-projective-envelope.json` — new unsplit statement node; no Mathlib match.
- `citations.json` — verbatim statement quotes for every cited node in every step.

## Attachments

None. I searched the read-only slopmaster2 source for the item id, its title, and the relevant geometric phrases; no sorry-free declaration states this item.

## WANTED

- WANTED: Orgogozo, “Modifications et cycles proches sur une base générale”, Proposition 2.3, author-version p. 4, for the quasi-finite projection and projective finite-envelope construction; the PDF was read online and is not in `literature/`.

## What was checked and corrected

The imported item had an empty proof and an inherited blueprint ancestry from the trace-formula locality node. I kept its statement and fixed the blueprint place to the first reduction paragraph of the Gabber proof. I searched the whole DAG and blueprint before adding nodes: the existing Zariski-main factorization `thm-pqf-zmt-factorization` is used directly, while no existing node states the bounded local projection or the dimension-preserving projective finite extension. I ran the required LeanFinder, Loogle, grep and LeanSearch searches for the item and for each new node; the searches found only generic affine-space, finite, Proj, and quasi-finite declarations, so both new nodes remain unsplit.

## Review by Q13

I read the item source reference (Orgogozo Proposition 2.3, p. 4) and the source statements of every cited DAG node. Step 1 applies the fibre-dimension-after-base-change statement exactly to the map to the strict-local base, preserving the hypothesis that all fibre dimensions are at most (N); the strict-henselization-limit definition supplies the resulting local scheme. Step 2 uses the new local projection node, whose conclusion supplies an affine neighbourhood, (d\le N), and a separated finite-type quasi-finite map to affine (d)-space. Step 3 checks the hypotheses of `thm-pqf-zmt-factorization`: the target affine space is quasi-compact and quasi-separated, and the map is separated, finite type, and everywhere quasi-finite. Step 4 uses the new finite-projective-envelope node, which explicitly gives an open immersion into a projective proper (P\to B) and the fibre bound (\le d\). Step 5 uses the strict-localization colimit and its functoriality; because the chosen affine neighbourhoods are open neighbourhoods of the pointed objects, intersecting pointed etale neighbourhoods with them is cofinal, so the canonical maps identify (X_{(x)}) with (P_{(y)}). The point (y) is the image of the original geometric point, and the projective/proper and (d\le N) clauses give the exact conclusion.

I tested the new statements on the edge cases (d=0), (N=0), (T=\varnothing), and (T=\mathbf A^d_B): the envelope may be (P^0_B=B) in the zero-dimensional case, the empty finite scheme is allowed, and the standard affine chart of (\mathbf P^d_B\) handles the full affine-space example. No hypothesis of Noetherianity, finite presentation, or quasi-compactness of the original (f) was added; only the affine local chart and the strict-local base are used.

The two new nodes are strictly smaller than the item: the first constructs only the quasi-finite affine chart, and the second extends a finite affine-space model to projective space without asserting any strict-local isomorphism. No cycle is introduced. The off-unit Zariski-main theorem is recorded as a tool use in the split report because it is a general factorization theorem outside the trace unit's route.

## Source error

None found in the imported statement. The source PDF is unavailable locally, so the report records it as WANTED while preserving the cited online place.

## What could not be finished

No Lean code or compiler was run, as required for this stage-1 delivery. The two new statement nodes remain for later splitting or proof attachment.
