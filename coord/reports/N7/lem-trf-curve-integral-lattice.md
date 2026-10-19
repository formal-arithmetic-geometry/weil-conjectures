Item: lem-trf-curve-integral-lattice. Group N7. Stage 1 repair.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-curve-integral-lattice.json`: repaired statement/proof split; no new DAG nodes; Mathlib searches report no matching theorem.
- `citations.json`: verbatim excerpts for every cited node at every proof step.
- `searches.jsonl`: four searches executed by `msearch.py` for this item.

## Attachments

None. I found no sorry-free declaration tagged `(blueprint: lem-trf-curve-integral-lattice)` in the read-only source checkout.

## WANTED

None.

## What was wrong and what changed

The returned review identified four defects. Step 3 previously asserted the finite-Tor condition from the integral definition, which only defines the condition; it now establishes that `M` is in the derived-complete integral category, observes that `M_1` is concentrated in degree zero, and applies the existing `lem-coef-integral-residue-tor` with interval `[0,0]` to obtain the uniform finite-Tor bound for all `M_n`. Step 4 previously invoked the adic realization proposition without identifying its inverse-limit object with the integral compact-support definition; it now makes that identification via `def-weil-integral-rational-qbar-compact-support`. It also records a compatible auxiliary family of zero Frobenius coefficient morphisms for the proposition's coefficient-morphism interface, while explicitly retaining the statement's assertion that no Weil structure is introduced. Finally, the category-ambiguous parenthetical `K_O=K_E, alpha=id` was replaced by a formulation using a chosen integral representative and its localization isomorphism.

## Review by N7

I reread the current item against Step 5 of `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md`, the unit `sk-thm-trace-transport`, and the statements of every cited DAG node. I checked the global hypotheses (`ell != char(k_0)`, separated finite type, curve dimension bound, and the completed coefficient sheaf) and retained the item's exact conclusion and no-Weil qualification.

Step 1 uses `prop-constructible-truncations` for the rational standard truncation triangles and `sk-lem-int-integral-heart` for finite stratification and finitely generated local integral models; these statements support the common uniform torsion exponent and the torsion-free quotient. Step 2 uses `def-weil-rationalization-karoubi` for scalar localization, the truncation node for bounded cones, and `def-weil-integral-rational-qbar-compact-support` for flat rationalization of compact support, giving the displayed identification of cohomology.

Step 3 now checks the point that caused the return. The integral-heart local models give derived completeness and bounded constructible reductions, so the definition `def-weil-derived-complete-integral-detailed` applies to `M`; the first reduction is a degree-zero constructible sheaf. The statement of `lem-coef-integral-residue-tor` says that an integral object whose first reduction lies in `[a,b]` has every reduction in the same uniform Tor interval, so `[0,0]` gives `M_n in D^b_ctf` for all `n`. The finite-ring origin equivalence `lem-weil-pbc-finite-ring-constructible-derived-origin` supplies the etale objects, and `def-weil-pbc-etale-origin-witness` records the explicit pairs. The quotient maps and the definition `def-trf-adic-system` give the normalized transitions. I checked these assertions on `M=0`, a free rank-one local model, and a torsion lattice before quotienting.

Step 4 now identifies the two meanings of the integral compact-support object: the definition `def-weil-integral-rational-qbar-compact-support` makes it the derived inverse limit of the level compact supports, exactly the `P_O` used by `prop-trf-adic-coefficient-morphism-systems`. That proposition's statement assumes only a normalized finite-Tor tower for its realization clause and explicitly has no Weil-structure hypothesis. For completeness I recorded the compatible zero maps `psi_n : L Phi^* M_n -> M_n`; `def-trf-frobenius-coefficient-morphism` says any such maps are coefficient morphisms and the zero family satisfies the compatibility equation. This family is auxiliary and does not add a Weil structure. The proposition then supplies the bounded finite-free representative and every reduction comparison.

Step 5 checks the hypotheses of `thm-nagata-compactification`, `lem-trf-compactification-cohomology` (including its explicit etale-origin witness), `thm-sc-finite-type-torsion-cd`, `lem-sf-separably-closed-torsion-cd`, and `def-sc-etale-torsion-cd`. The closure compactification has dimension at most one, so the torsion cohomological dimension is at most two; the standard t-structure gives the negative-degree vanishing. Empty `X_0`, `M=0`, and dimension-zero `X_0` all give the stated range. No new node was created, so there are no duplicate pairs or new-node searches to review. All citations and Mathlib search records were regenerated after the repair.

## What could not be finished

Nothing remains before the required server dry run.
