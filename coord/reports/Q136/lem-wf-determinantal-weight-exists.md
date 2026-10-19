# Q136 — lem-wf-determinantal-weight-exists

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-wf-determinantal-weight-exists.json: statement, split into four proof steps, not a Mathlib leaf. Original mathematical statement retained. Added missing statement dependencies and searched blueprint.same_as.
- citations.json: verbatim statements backing every use in every proof step.
- searches.jsonl: actual msearch.py results, reused in the item's mathlib_searches; no new nodes.

## Attachments

None. Searched the slopmaster2 project by the blueprint id, determinant-weight terminology and HasDetWeight. The nearby declaration AlgebraicGeometry.WeilGroup.IsLisse.hasDetWeight in WeilConjectures/EtaleCohomology/Purity/RealSheaves/Purity.lean:225 asserts a normalized HasDetWeight under smoothness, characteristic inequality and IsEtaleQuotient assumptions; it does not assert exactly the item's existence and uniqueness of the determinant line's punctual weight. HasDetWeight.eq at line 257 also requires a supplied closed point. These are relevant reference implementations, not a complete exact attachment. No upstream master sorry declaration was treated as finished evidence.

## WANTED

None.

## Corrections and source comparison

The main-20261015 statement and proof agree with the imported item. The current unit text was read in literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-d-real-detweights/_section.md, as well as the DAG unit and chapter. The route remains determinant character, rank-one finite geometric image, rank-one purity, and a closed-point uniqueness calculation. This item is a supporting lemma, not the unit's whole definition, so no unit realization fields were changed.

The imported proof implicitly assumed the Weil representation was defined over a finite coefficient field and that the curve had a closed point. Step 1 now explains the finite coefficient choice: the lisse model descends to E and the single degree-one operator and its inverse require only finitely many additional algebraic matrix entries. Step 3 uses existing closed-point and residue-field nodes, rather than quoting these facts without dependencies. The original fundamental-representation definition by itself does not prove continuity: the proof now also cites lem-wf-weil-fundamental-representation. No statement dispute or change is needed; the normal geometrically connected curve and prime-to-characteristic coefficient conventions give exactly the hypotheses used.

Mathlib searches were run through msearch.py only, with two semantic phrasings, Loogle and two source regexes. LeanFinder returned isocrystals, finite-group character theory, Lie weights, spectral norms and norm/Hilbert-90 facts. LeanSearch returned linear determinants and unrelated weights. None concerns rank-one Weil purity. Loogle found no matching pair of Weil/pure names. Source grep found no relevant declarations; the only hit for the broader pattern was NumberTheory/SelbergSieve.lean:97, whose line merely quotes a tactic expression using pure and weights. No service failure was recorded as absence.

Blueprint searches used blueprint_refs.py with determinant, purity of the determinant, unique real, closed point, coefficient field and purity weight, alongside DAG regex searches and the ancestor command. The determinant search found this item, its definitions, downstream weight comparisons and different determinant identities, but no duplicate of the complete existence-and-uniqueness statement. The supporting closed-point theorem and closed-point residue-field theorem already exist, so no new node was created.

## Not duplicates

No new nodes. Existing nodes were reused for all required results.

## Review by Q136

I read the current blueprint item and its separate proof file, the determinant-line definition, the continuous-fundamental-representation statement, the rank-one finite geometric image theorem and punctual-purity corollary, and the closed-point residue-field statement in the current main-20261015 snapshot. I also read the statements of every node in citations.json directly from dag/nodes. The coefficient convention was checked against def-pod-lisse-l-adic-sheaves and the text of Deligne, Weil II, (1.1.1), printed pp. 146–147. The topological closed-point fact was checked in literature/stacks-project/topology.tex at lemma-quasi-compact-closed-point, Tag 005E. These are the sources used; no prohibited SGA route is used.

Step 1 uses the fundamental-representation definition for the geometric action, degree-one operator and conjugation identity, the corresponding named lemma for continuity, and the lisse coefficient definition for its finite-stage object and common-stage morphisms. Enlarging E by the finitely many entries of the operator and inverse is explicit algebraic field extension; the conjugation equality descends because scalar extension is injective. No unproved finite-field-of-definition theorem is hidden here. This detail was absent from the imported paragraph.

Step 2 takes the rank-one representation and determinant character from def-mg-determinant-line itself. Continuity is justified by the determinant polynomial in the already continuous matrices, not by the definition of the character alone. I checked that the finite-image theorem requires normality, geometric connectedness, separation, finite type, pure dimension one, a finite E and ell not dividing q; these are exactly the curve convention and coefficient hypotheses plus step 1. The corollary applies in this situation and explicitly supplies the real weight 2 log_q |iota(c)| of the rank-one sheaf. The scalar c is a unit, so its norm has a logarithm. This is the unit's stipulated rank-one route, with no replacement theorem.

Step 3 uses the finite-type definition for quasi-compactness and the geometric hypothesis definition for nonemptiness. The Kolmogorov property is written out in affine charts using the prime-spectrum definition. The existing quasi-compact Kolmogorov closed-point statement then provides y; no Jacobson-density assertion is assumed. The existing closed-point-field statement applies to X_0 finite type over the field k_0 and supplies a finite residue extension. Since k_0 is a finite field and its residue extension is a field, its cardinality is finite and greater than one. These two generic statements are declared as tool uses; they do not change the rank-one purity route.

Step 4 uses the determinant definition for rank one and the explicit local-Frobenius construction for invertibility. In a one-dimensional stalk an invertible linear map is multiplication by a nonzero scalar; this does not invoke general spectral theory. The two conditions from def-weil-punctual-weights give the same positive real power of q_y. Taking logs and cancelling the positive log q_y proves equality. This is elementary after the cited statements, so no new uniqueness lemma is manufactured from a clause of the item.

For edge cases I checked a constant rank-one sheaf (weight zero), a degree character with scalar c (weight 2 log_q |iota(c)|), arbitrary positive ranks, and the role of nonemptiness: on an empty scheme purity would be vacuous and uniqueness would fail, but the geometric-connectedness convention explicitly excludes that case. Rank zero causes no problem for the determinant line, which is still one-dimensional, though the item's irreducibility already excludes a zero sheaf. No rational-point assumption is introduced; y can have any positive degree. Affineness and properness are not required. Irreducibility is retained in the statement but unused in this determinant-only argument.

I checked delivery-errors B–E: there are no new statement-only nodes, duplicate nodes, unlogged searches or Mathlib leaf claims. Every non-elementary step cites the statement it uses; the finite-image and purity corollary are separate existing nodes, not definition citations standing in for theorems. The topological and residue-field facts are explicitly cited, the dependency union matches uses, and no descendant weight comparison is used, avoiding a cycle back to the item. All four steps are under 2000 characters. The additional lem-wf-weil-fundamental-representation, lem-sc-quasi-compact-kolmogorov-closed-point and lem-kun-closed-point-field tool uses are explained in split_report.tool_uses for maintainer review.

## Unfinished work

None at this one-level split. Dependencies retain their independent DAG work status; this delivery adds no child item. Required server dry run and direct push follow this report.
