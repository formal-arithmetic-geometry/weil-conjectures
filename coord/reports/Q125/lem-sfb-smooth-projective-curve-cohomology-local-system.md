# Stage-1 report: Q125

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-projective-curve-cohomology-local-system.json`: statement, split; no Mathlib match. The existing statement is unchanged. Five assembly steps reuse existing nodes.
- `citations.json`: one verbatim statement quotation for each step/node pair.
- `report.md` and the automatically recorded `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched `lean/WeilConjectures/` for the item's blueprint tag, curve cohomology, genus, and local constancy. `AlgebraicGeometry.IsConnectedCurve.sheafH_constantZMod_of_isProper` (`AlgebraicGeometry/Curve/Estimate.lean:139`) covers a single proper curve, not a family. The smooth-proper local-constancy theorem in `SixFunctors/Etale/BaseChangeTheorems/SmoothProperLocallyConstant.lean:226` assumes a finite-type base over a field. Neither supplies the item over arbitrary schemes. Both were read as source material only; no compiler was run.

## WANTED

None. All sources needed for this assembly are present in `literature/stacks-project/`.

## Corrections and route

The item previously had no proof. I retained its statement, citations, inherited searches and blueprint provenance, and corrected the inherited generic Mathlib-search verdicts that discussed frame schemes rather than this item. Fresh searches used the prescribed msearch command: LeanSearch, Loogle, grep, and two semantic phrasings via LeanFinder. The actual hits are in the search log and were read: they concern cotangent cohomology, etale/smooth morphisms, condensed locally constant objects and profinite limits. None gives the item's etale higher direct image, rank or exchange map. The old LeanSearch outage remains recorded as unavailable; today's successful query is recorded separately.

I read the chapter and unit records, the three blueprint levels in SETUP, and the latest blueprint section, unit, and direct-images proof. The inherited source route is the smooth curve local-system prerequisite to the level cover inside the alteration proof. The current blueprint direct-images proof is shorter but still has the proper-image step; this assembly changes neither that step nor the chapter route. `blueprint_refs.py ancestor` reports null for this non-imported chain, matching its existing provenance. Whole-blueprint searches for cohomology local systems, proper cohomology and loc-cst-torsion found no equivalent family theorem. DAG searches by 0GLI, 095T, 03RQ and projective/proper identified the existing tools used below. No duplicate or clause-restatement node was created.

## Not duplicates

No new nodes; no new/existing pair requires adjudication.

## Review by Q125

I read Stacks `more-etale.tex`, proposition-loc-cst-torsion (0GLI), including its arbitrary-base reduction; `etale-cohomology.tex`, theorem-proper-base-change (095T), lemma-cohomology-smooth-projective-curve (03RQ), remark-stalk-pullback (04JN), and lemma-equivalence-abelian-sheaves-point (04JQ); and `morphisms.tex`, lemma-characterize-locally-projective (01WB) and lemma-locally-projective-proper (01WC). I also read the current blueprint proper-curve cohomology statement and proof. No new node needs a separate source review.

Step 1 uses the exact statement of `lem-trf-projective-bundle-proper`, which explicitly uses the same finite-type quasi-coherent projective-bundle convention, then `lem-sfb-smooth-proper-finite-cohomology-local-system`, which explicitly permits arbitrary base schemes and all nonnegative degrees. The input is the constant one-dimensional finite-field module, so its finite locally constant hypothesis holds with no cover to construct. Smoothness is assumed and properness was obtained with the correct convention.

Step 2 uses `det-properbasechange-modules`, which asserts the canonical module exchange and its invertibility when the forgotten complex has torsion cohomology. Here the complex is the constant A-sheaf in degree zero, killed by ell. `lem-pe-constant-left-module-inverse-image` explicitly supplies exact module inverse image and its derived functor; `lem-kun-pullback-constant` supplies the canonical constant-coefficient identification. Thus taking H^1 gives precisely the map in the statement. No assertion of compatibility is inferred merely from the existence of some isomorphism.

Step 3 uses both clauses of `lem-weil-pbc-geometric-point-pullback-stalk`: exact sections on an algebraically closed point, also for modules, and sections of inverse image equal to the geometric stalk. I opened `def-weil-pbc-direct-image`: it explicitly gives the sectionwise formula and injective-resolution computation, including module coefficients. I opened `def-weil-pbc-etale-cohomology`: it explicitly defines cohomology by the same resolution. The displayed three equalities are then a direct computation with one complex and an exact functor, not an uncited Leray theorem. This step is elementary relative to those stated inputs. Since its first map is Step 2's BC at the geometric point, the required provenance of the stalk isomorphism is preserved.

Step 4 uses `lem-pc-proper-base-change` only for its stated properness-preservation clause. The hypothesis already gives smoothness, connectedness, projectivity, dimension one and genus g for the geometric fibre. The invertible integer stays a unit under the local-ring map to Omega, so the characteristic condition for `lem-sc-primitive-root` and `thm-sc-proper-cohomology` holds. Their statements respectively supply the primitive root on this algebraically closed field and the degree-one group A^(2g). The genus convention is literally dim H^1(O) in `def-sc-genus`. Additive isomorphisms of groups killed by the prime ell are A-linear because integer multiplication gives every scalar. Only a fibrewise root is used; no root or Tate-twist trivialization is chosen on T.

Step 5 uses the statements of `lem-weil-pbc-inverse-image-stalk-germ` for restriction to a cover member and `lem-weil-pbc-constant-sheaf-geometric-stalk` for the value of a constant sheaf. Their additive stalk identifications commute with scalars by naturality in scalar endomorphisms (and again A is the prime field). A nonempty cover member has a geometric point, chosen by taking an algebraic closure of a point's residue field. Its constant vector space is therefore A^(2g); applying a linear isomorphism to constant sheaves finishes the local-model identification. This is a short elementary argument, so I did not create a separate fixed-rank lemma.

I checked delivery-errors B through E against these files: every cited result was opened, every non-elementary input has an existing node, no source proof is used for an unstated stronger clause, and the citation quotes are copied verbatim. Off-unit statements are declared in split_report.tool_uses as generic tools. No new node is an elementary fact, duplicate, clause of the item or missed Mathlib leaf. Every proof step has fewer than 2000 characters. There is no hidden long lemma.

For g=0 the same rank calculation gives the zero vector space and zero local sheaf; for ell=2 the primitive root is -1 in characteristic unequal to 2, which is allowed. Disconnected bases are treated separately on each cover member, without choosing a common global trivialization. Empty T has the empty etale covering and all base changes to it are empty. No Noetherian hypothesis enters: it is expressly absent from 0GLI and from the general module PBC statement. I found no statement dispute or false edge case.

## Unfinished work

None for this one-level split. Existing dependencies retain their own stage states. Delivery awaits the prescribed server preflight and push.
