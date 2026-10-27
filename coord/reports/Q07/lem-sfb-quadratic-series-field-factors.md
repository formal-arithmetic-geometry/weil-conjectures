# Report: lem-sfb-quadratic-series-field-factors

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-quadratic-series-field-factors.json`: existing item, split with eight proof steps; no new nodes.

Attachments: none.

WANTED: none.

The item is not already proved by a finished declaration in `lean/WeilConjectures/`; the only related source file is `RingTheory/PowerSeriesQuadraticIdeal.lean`, and it does not state this item. I retained the imported statement and its existing definition dependencies. The whole-blueprint search found no blueprint node stating this coefficient-series factor theorem. Existing DAG searches found the monic quotient basis node `lem-weil-pbc-monic-quotient-free` and the power-series normal-domain node `lem-weil-pbc-power-series-normal-domain`, so I cite those rather than creating duplicates. The latter is a generic theorem from the `sk-thm-p1` route and is declared as a tool use because this item needs it only to establish normality of the field-factor series rings.

## Review by Q07

I read the item source and the latest blueprint material around the six-functor stability/direct-image route, then checked the imported statement against the Stacks source `literature/stacks-project/curves.tex`, Tag 0C4A, Cases I and II. I also read the statements of every cited DAG node. Step 1 uses `lem-weil-pbc-monic-quotient-free`, whose statement gives the basis `1,T` for a monic degree-two quotient; this is exactly what the coordinate expansion needs. Steps 2 and 3 prove the split and nonsplit cases directly. In the split case I checked the second root `s=-β-r`, distinctness from the nonzero discriminant, and both explicit interpolation inverse formulas. In the nonsplit case I checked the norm calculation and the inverse formula in characteristic two as well as odd characteristic, with the no-root hypothesis supplying nonvanishing of the norm.

Step 4 defines the coefficientwise extension of the algebra isomorphism and its inverse, and checks multiplication coefficientwise using finite Cauchy sums. Step 5 uses `def-weil-pbc-noetherian-ring`, `def-weil-pbc-normal-ring`, and `lem-weil-pbc-power-series-normal-domain`; I verified that a field is Noetherian and a normal domain directly, so the cited normal-power-series statement applies to each factor. The product-of-domains nilpotent argument is written out. Step 6 establishes the unique `u+zv` expression and that scalar power series lie in `A=F+tB`. Step 7 uses the exact statements of `def-weil-pbc-integral-closure` and `def-weil-finitely-generated-module`: the displayed monic norm equation proves integrality, while the same expression gives the two module generators. Step 8 proves injectivity of multiplication by `t` by coefficient shifting and records why all computations remain valid in characteristic two and in the split product case.

I checked every non-elementary citation against the verbatim statements recorded in `citations.json`; all quotes are complete statement text. I also ran fresh LeanSearch, LeanFinder, Loogle, and Mathlib-source searches through `msearch.py`; they returned only general quadratic-algebra, norm, and field-power-series ingredients, with no theorem stating this combined result. No new node was needed, so there are no duplicate pairs to record.

What was corrected: the imported item had no proof. I supplied the missing split/nonsplit algebra argument, coefficientwise series isomorphism, basis expansion, explicit norm equation, integrality, finiteness, reducedness, and regularity of `t`, while retaining the original statement and dependencies.

What remains unfinished: nothing within this stage-1 item. No Lean code is written by stage-1 policy. The self-review above is complete.

Edge cases checked explicitly: over F₂, β=1 and γ=0 gives the split algebra with roots 0,1; β=γ=1 gives the degree-two field, where the norm is a²+ab+b². Over F₃, β=0 and γ=2 gives the two roots 1,2, and γ=1 gives the no-root case. The zero series has u=v=0 and satisfies the displayed equation; constant z gives its original polynomial relation. A zero discriminant is excluded, so the repeated-root algebra F[Z]/(Z²) is not a permitted counterexample. The zero ring is excluded by the field hypothesis. Every proof step is under 2000 characters. The statement is unchanged, no new node conceals a clause or a proof, and the only non-elementary facts used are the two cited existing theorem nodes.
