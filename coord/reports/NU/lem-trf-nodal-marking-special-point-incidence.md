# Stage-1 worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-nodal-marking-special-point-incidence.json`: statement item, split into six steps; no Mathlib match for the whole statement.
- `citations.json`: verbatim statement quotations for all 16 step citations.
- `report.md`: this report.

No new nodes, no new Mathlib leaves. The sandbox initially contained only dispatcher brief markers; there was no earlier split, report, or search log to recover. The item statement, statement dependencies, source, creation record and blueprint ancestry have been preserved. The five newly executed searches are appended to its historical searches and recorded by msearch in searches.jsonl.

## Attachments

None. Searched `lean/WeilConjectures/` for the item id, nodal/Nodal, special-point and first-Fitting terminology. The results concern Weierstrass geometry or unrelated comments, not a declaration proving this item. The existing field-point factorization dependency is closed, but that does not prove the full item by itself.

## Literature wanted

None.

## Problems in the imported material

The statement needs no correction. The source's reference to Tag 0C59 is not by itself sufficient to apply the existing family theorem: its geometric-fibre hypotheses must first be verified. Step 1 explicitly does that using the existing chosen-nodal-fibres-universal theorem, flatness over a field, and local finite presentation over a Noetherian field. The item had no proof before this delivery.

The latest blueprint was read at `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`, including the unit statement and lem-trf-local-term-locality proof. The nodal-incidence lemma is an auxiliary result in the already imported nearby-cycle alteration branch, not a separate theorem in that current text. The proof follows the assigned branch and does not replace a chapter or unit route. Whole-blueprint searches for nodal, unramified, and incidence give no equivalent blueprint node. Whole-DAG statement/source searches for 0C59, 02G7, Fitting singular schemes, rational-point incidence and field-extension geometry found the dependencies used here; none gives the entire item.

## Unfinished work

None for this one-level split. The dependencies keep their existing status. This stage-1 delivery makes no claim that their Lean proofs are finished.

## Not duplicates

No new nodes are created. In particular the existing nodal-family-fitting-singular, unramified-field-fibre-decomposition, finite-extension-triviality, constant-coproduct-base-change and field-point-factorization nodes are reused instead of being duplicated or specialized into new nodes.

## Tool uses

`lem-weil-pbc-sets-etale-inverse-image-constant-base-change` is a generic scheme-theory tool from another unit. It states the coproduct/pullback isomorphism and compatibility of each coprojection exactly as needed in step 4. No statement in this unit gives that general comparison. Its use is declared in split_report.tool_uses, not in the maintainer-owned top-level tool_uses. The other off-unit inputs are Mathlib leaves or the closed field-point-factorization node.

## Review by NU

I read the item against Stacks curves.tex Tags 0C56 (lemma-node-field-extension), 0C4E (lemma-nodal-lci), 0C59 (lemma-nodal-family), and 0C5B (lemma-base-change-nodal-family); morphisms.tex Tag 02G7 (lemma-unramified-over-field); divisors.tex Tag 0C3I (lemma-base-change-and-fitting-ideal-omega); schemes.tex Tag 0356 (lemma-map-into-reduction) and the gluing lemmas 01JB/01JC; and fields.tex Tag 09GR (lemma-algebraically-closed). I also read the Mathlib flat-over-a-point instance in AlgebraicGeometry/Morphisms/Flat.lean and the local-finite-presentation equivalence in AlgebraicGeometry/Noetherian.lean. No new node requires a separate source audit.

For step 1 I opened each cited statement. The two definitions justify empty closed subschemes in the empty case. lem-pc-flat-field gives flatness for every scheme over k; pqf-lem-lft-fp-locnoeth gives local finite presentation because Spec k is locally Noetherian (the only field ideals are 0 and 1). The chosen-nodal-fibres-universal statement assumes flatness, local finite presentation, pure dimension of the ordinary fibre and the completed-node condition over one algebraic closure per base point; taking k itself verifies precisely these hypotheses. It explicitly concludes the pure-dimensional nodal condition for every algebraically closed extension. I did not infer that condition merely by tensoring completed rings.

For step 2 the nodal-family-fitting-singular statement explicitly gives unramifiedness, support equal to the nonsmooth complement, and the canonical singular-scheme comparison after every base change. All its hypotheses are now present by step 1, including arbitrary geometric extensions. No projectivity, properness, connectedness or separatedness is introduced. Z_L is its scheme-theoretic scalar extension, not a new reduced subscheme.

For step 3 the etale definition explicitly includes unramifiedness, so the unramified-field-fibre-decomposition theorem applies to both F and Z. Its statement permits arbitrary or empty index sets and finite separable extension fields. The finite-extension-triviality Mathlib leaf identifies each such field with k as a k-algebra. I checked the additional finiteness argument: C has a finite affine cover by the finite-type definition; F and Z have closed images by their cited definitions, so adding the complement to an open cover proves they are quasi-compact. The singleton open cover supplied by the decomposition then has a finite subcover. No unproved properness-to-finiteness assertion is used. Disjointness follows from the prescribed smooth marking and the support calculation of step 2.

For step 4 the constant-base-change node states both the isomorphism and its compatibility with individual coprojections. Set U=Spec k, V=Spec L, and take the finite label set of each special scheme. The closed-immersion-base-change Mathlib leaf applies to F, Z and the given R, with no extra hypothesis. Thus different summands stay different even in a nonseparated C_L, and the two special schemes stay disjoint by projection. This verifies that the comparison is a bijection of actual points of C and C_L, rather than a count of branch labels.

For step 5 the field-point-factorization node says exactly that a Spec K morphism whose image belongs to a closed immersion factors uniquely through that immersion. Take K=k and the summand map of the point, not an arbitrary nonreduced test scheme. The factorization is over k by composing with the structure map. The fibre-product definition gives the indicated map into R_L with the same two projections as the scalar-extended point. In the reverse direction the pullback square projects a point of R_L to a point of R over the original special point. This proves the incidence assertion for any closed subscheme; the additional hypothesis that R_L is a reduced component is harmless and never silently asserted for an arbitrary component. I avoided the false general assertion that a map from an arbitrary scheme factors through a closed subscheme merely because its set-theoretic image does.

Step 6 is elementary: restricting the finite bijection along the established incidence equivalence gives inverse maps on the two indicated subsets, so their cardinalities agree. No result about normalization or component-branch numbers is needed. I tested an irreducible curve with a self-node (one point on its component, regardless of two normalization branches), xy=0 (one common singular point on each component), a smooth affine line with empty marking (zero special points), the empty curve, a marking of several points, and a nonseparated smooth line with doubled origin. The proof accommodates each. Nilpotent marking thickenings are excluded by etaleness, and nonreduced components are not smuggled into the hypotheses.

Against delivery-errors B--E: there are no new statement-only nodes to audit; every non-elementary ingredient is a cited node, with its actual statement opened and a verbatim quotation entered in citations.json. No clause is moved to a renamed node; the proof carries the rational-point argument. Statements and source tags are unchanged; TeX uses single escapes in decoded JSON. There is no use of a node's internal proof or a definition for a theorem beyond its recorded assertions. Each proof step is shorter than 2000 characters, so none hides an oversized comparison. The item is strictly below the cited family, decomposition and factorization inputs, not a dependency of them. The first server dry run passed preflight, check_dag and review_split. After correcting only the report citation count from 20 to the actual 16, a final dry run is required before push.
