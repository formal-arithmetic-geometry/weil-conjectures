# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-prime-transcendental-coordinate.json` — statement, split proof; no new nodes.
- `citations.json` — three verbatim citations for the second proof step.

## Attachments

None.

## WANTED

None.

## What was wrong or incomplete

The imported item was unsplit: its statement and Stacks source were present, but it had no proof steps, proof dependencies, or split report. No statement correction was needed. The existing Mathlib searches found no theorem stating the simultaneous finite-prime transcendence assertion. No duplicate DAG node states Tag 0GTE's lemma. The affine calculation $\kappa(\mathfrak p)=\operatorname{Frac}(B/\mathfrak p)$ is written explicitly in the proof as the standard computation from the residue-field definition; the product-prime and algebraic-quotient facts are elementary consequences of the hypotheses and definitions, so no auxiliary node was created.

## What could not be finished

Nothing.

## Review by NI

I read the target node, its source at More on Morphisms, Tag 0GTE, lines 8566–8592, the ancestor blueprint proof for `lem-trf-local-term-locality`, and the statements of `def-weil-residue-field`, `def-pc-field-extension`, and `def-weil-algebraic-element`. I checked the edge case $r=0$ separately (the ideal contains $0$ and the conclusion has no indexed conditions), and the $r=1$ empty-product case. For each $i$, Step 1 constructs an element of $J_i=J\prod_{j\ne i}\mathfrak p_j$ outside $\mathfrak p_i$ using incomparability and primality; this is exactly the product-ideal fact cited by the source. Step 2 uses the affine residue-field fraction description, clears a denominator by an element of $J_i\setminus\mathfrak p_i$, and checks that if both numerator and denominator images were algebraic then their quotient would be algebraic, contradicting the chosen transcendental element. Step 3 checks that the other summands vanish modulo $\mathfrak p_i$, so the sum has the selected transcendental image at every prime. I verified every `uses` entry against the cited node statement and recorded its verbatim sentence in `citations.json`. I also ran the required LeanFinder, Loogle, grep, and LeanSearch queries on 2026-10-18; none states this lemma. No hypotheses were added or dropped, and no auxiliary node or tool use is needed.
