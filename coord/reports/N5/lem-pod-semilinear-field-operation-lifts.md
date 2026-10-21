# N5 stage-1 delivery: lem-pod-semilinear-field-operation-lifts

## Files written

- `dag/nodes/sec-poincare-duality/lem-pod-semilinear-field-operation-lifts.json`: statement item, split into nine steps; Mathlib verdict no match. Statement and statement dependencies unchanged. No new nodes or Mathlib leaves.
- `citations.json`: one verbatim statement excerpt for every node cited by every proof step (18 entries).
- `searches.jsonl`: actual logged search results, retained without rewriting. `prepare.py` is sandbox-only preparation, not a project change.

## Attachments

None. The exact blueprint tag has no hit in `lean/WeilConjectures`. Concept searches in `WeilConjectures/WeilSheaf` found `AlgebraicGeometry.WeilComplex.upperStarCompForgetIso` and `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerStar_comp_forget_iso` in `Operations.lean` (73, 95). I read their statements and bodies: they cover forgetful comparisons for a different derived-Weil category, do not give the explicit tensor/Hom fixed-pair formulas and all field-stage transport assertions, and therefore are not an attachment for the whole item. OtherSections' compact-support projection declaration is also only a partial operation statement. No finished proof of the whole item was found.

## WANTED

None. The proof is an agent expansion of the local blueprint; it is marked `proof_origin.by = agent`, not attributed to a human source.

## What was wrong / changed

The imported item was statement-only, as intended by Q108's re-split of `prop-weil-operations`. Its source says to use `lem-fix-weil-operations`; its proof supplies the transport and lift ideas but not the explicit arrow calculations. I supplied those calculations and cited narrower, existing site-theoretic, completed-coefficient and comparison lemmas rather than moving the five clauses into new tasks. I did not change the item statement, its hypotheses, its coefficient categories, its blueprint lineage or the chapter/unit route. The old searches in the node are retained; the new searches are appended from their actual log.

The review avoided two tempting but incorrect citations. `lem-coef-frobenius-exchange-equivalence` assumes both schemes separated and only treats the raw rational stage, so I used `lem-pod-weil-frobenius-compact-support-exchange`, which explicitly removes those restrictions and covers both field stages. `lem-pod-geometric-frobenius-internal-hom-comparison` has separatedness, finite-Tor and site-perfect hypotheses stronger than the generic preserved domain here; I used `lem-pod-derived-automorphism-hom-evaluation`, whose statement treats arbitrary scheme isomorphisms and every pair on its constructible internal-Hom domain. I did not infer an invertible exchange merely from the fact that its unmated comparison is invertible: the ordinary exchange uses the explicit equivalence hypotheses of the mate criterion.

## What could not be finished

Nothing mathematical remains in this one-level split. Existing cited nodes may remain open; this delivery does not assert their proofs are finished. No Lean file was written and no compiler, Lake or build tool was invoked.

## Searches and blueprint scope

I read `GOAL.md`, the human's three-level contract in `SETUP.md`, the stage-1 brief and stage document, worker role, chapter `sec-poincare-duality`, and unit `sk-lem-finite`. The item is a created node below `prop-weil-operations`, not the unit's key finiteness statement, so the unit realization fields are untouched. The local current blueprint `prop-weil-operations.md` and `.proof.md`, together with `lem-fix-weil-operations.proof.md`, give the equivariant-operation route. I read Stacks `sites-modules.tex`, Tag 0GMX, `remark-pullback-internal-hom`: it gives the evaluation-related underived comparison, not the completed/derived theorem. The latter is correctly taken from the existing derived-automorphism node, not claimed to be Stacks 0GMX itself. No SGA source is used.

Whole-DAG searches included semilinear and Frobenius transport/comparison, inverse-image equivalence and completed pullback. Whole-blueprint searches through `tools/blueprint_refs.py` included `Frobenius`, `automorphism`, `Weil operations`, and `fixed pair`; ancestor lookup gives `prop-weil-operations`. The similar blueprint node `lem-fix-weil-operations` states existence and coherence of lifts, but not this item's entire integral/rational equivalence and explicit functoriality statement. `same_as` remains empty. No new node was created, so there are no pairs requiring a new-node duplicate justification.

The six new searches were run only with the prescribed `msearch.py N5 lem-pod-semilinear-field-operation-lifts` command: two LeanFinder phrasings, Loogle `"IsoAlgebra"`, LeanSearch, and two Mathlib grep patterns. All succeeded. The first semantic search returned module-sheaf adjunction/composition declarations rather than rational constructible Weil pairs. The second found `CategoryTheory.Endofunctor.Algebra.functorOfNatTrans`; I read `Mathlib/CategoryTheory/Endofunctor/Algebra.lean` 152–161. It only changes the algebra endofunctor by a natural transformation in one fixed category; it does not provide the geometric equivalence, derived coefficient operations or all five lifts here. Loogle found `AlgCat` ring-algebra equivalences, and LeanSearch found homological-complex naturality. The logged grep in `CategoryTheory/Endofunctor` locates `Algebra.functorOfNatTrans` at line 156. These are useful formal analogues, not exact matches or one-line specializations for this item.

## Review by N5

I checked the split against delivery-errors B–E with the actual node statements open. There are no new statement-only nodes, no hidden restatement tasks and no source not present locally. Every proof citation has a verbatim excerpt in `citations.json`. All nine steps are shorter than 2000 characters, but I also checked them for substantive hidden comparisons rather than using the length as a substitute for review.

Step 1 uses `lem-weil-frobenius-square-cartesian`, whose statement gives the inverse scheme maps, commutation and Cartesian assertion for arbitrary k0-schemes. Its hypotheses are weaker than the item. The short structure-map check is written explicitly; in particular the Frobenius map is not assumed k-linear.

Step 2 uses `lem-weil-proetale-isomorphism-inverse-image` for the site/module equivalence, exactness and inverse-limit preservation, and `lem-weil-isomorphism-derived-pullback` for identification of completed pullback with termwise transport and preservation of integral constructibility. The latter includes the actual completed coefficient-sheaf structure isomorphism, not a constant-integral-sheaf substitution. Both apply to g and its inverse because ell is invertible in characteristic p. The inverse-composition identity comes from composing inverse site equivalences on complexes, not from testing only reductions of a derived map.

Step 3 uses the displayed Hom-tensor definition and triangle description of `def-weil-rationalization-karoubi`, the representative/equality/triangle description of `def-weil-algebraically-closed-coefficients`, and the actual natural, unital, tower-compatible pullback comparisons in `lem-pur-integral-operations-scalar-extension`. Those statements say exactly what the construction needs: linear extension of the integral identities and cancellation of common-stage comparison maps. It does not claim that every rational Weil isomorphism has an integral lattice preserved by Frobenius. The inverse equivalence is established before a Weil structure is imposed.

Step 4 uses the natural integral composition isomorphism and associativity in `lem-pod-integral-pullback-composition`, together with the ambient ringed-site composition normalization of `lem-weil-pbc-proetale-derived-pullback-composition`. Their hypotheses allow arbitrary scheme morphisms with compatible coefficient sheaves. For the latter comparison at integral coefficients the isomorphism legs are identified with their exact inverse images by Step 2; no arbitrary non-isomorphism is declared exact for completed coefficients. Rational and common-stage formulas use precisely the functors already defined in the item and Step 3.

Step 5 uses only clause (1) of `fix-prop-adjunctions` for the ordinary constructible adjunction, the specified mate formula in `def-exchange-projection`, and `lem-weil-mate-iso-along-equivalences` for invertibility. I checked the types: L=L'=Lf*, G=P_Y and G'=P_X, so the required left comparison is the inverse of Step 4, and its mate has type P_Y Rf* -> Rf* P_X. Both G and G' are equivalences by Step 3. The compact-support input is the separate `lem-pod-weil-frobenius-compact-support-exchange`, which explicitly states naturality, invertibility, the two coefficient stages, the domain restrictions and absence of separatedness hypotheses on X0 and Y0. No ambient exceptional adjoint is used.

Step 6 uses the arrow equation and inherited identity/composition of `def-weil-weil-sheaf-complex`. The actual three-equality calculation uses only that equation, naturality and functoriality. Its elementary flag refers to this calculation, after the comparisons have already been established in Steps 4–5. Its isomorphism assertion follows because the two factors are isomorphisms.

Step 7 uses the all-stage natural tensor comparison in `lem-pur-derived-pullback-tensor-iso` and the tensor bifunctor of `def-weil-derived-pullback-tensor-hom`. I checked both input Weil-arrow equations and wrote the resulting four-term identity. The underlying tensor domain stays the previously proved one. Step 8 similarly uses `lem-pod-derived-automorphism-hom-evaluation` and the internal-Hom bifunctor definition. The automorphism node explicitly supplies localized/common-stage naturality, including arbitrary localized morphisms, and imposes constructibility on the output rather than site-perfectness on all inputs. I checked the direction of u:M' -> M and the equality theta_M^{-1}u=(Pu)theta_M'^{-1}; these give the displayed Hom-arrow equation. The first structure map must be inverted to type the comparison.

Step 9 uses the forgetful functor defined in `def-weil-weil-sheaf-complex` and merely observes that the previously constructed arrows and objects have exactly the specified underlying values. Its elementary flag does not claim a new exactness or constructibility theorem. There is no triangulated structure on pairs; the statement's exactness language concerns only the given derived functors, as the item itself requires.

I checked edge cases: f=id makes the covariant comparisons identities under the composition normalization; empty geometric fibers give the unique maps; on a point, structures theta_M=a, theta_N=b yield tensor scalar ab and Hom scalar b/a, testing the contravariant inverse. Choosing a=ell, b=1 tests a rational Weil structure with no invertible integral datum. The same formulas work over a common larger coefficient field by the cocycle and cancellation just used. Non-separated finite-type X0,Y0 are allowed because the selected generic site-isomorphism, tensor and Hom inputs do not add separatedness, and the compact-support exchange explicitly covers that case. No preservation domain was enlarged. No statement dispute was found.

Generic tools from other units are declared individually in `split_report.tool_uses`; they provide the site, coefficient or categorical inputs below this unit's Frobenius-equivariance step, and do not replace its proof route. I also inspected dependency paths for the selected existing input nodes to ensure none uses this item; the required server dry run supplies the final full-graph check.

## Not duplicates

No new nodes.
