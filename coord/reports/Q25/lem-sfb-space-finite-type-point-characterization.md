# Stage-1 report: lem-sfb-space-finite-type-point-characterization

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-finite-type-point-characterization.json`: statement, split; four proof steps, no Mathlib match for the whole item. Original statement and statement dependencies retained.
- `citations.json`: 19 verbatim quotations, one for every step/node citation.
- `searches.jsonl`: actual msearch output records for the item. No new DAG nodes or Mathlib leaves.
- `report.md`: this report.

## Attachments

None. I searched the read-only project `lean/WeilConjectures/` by the exact item id and by finite-type-point spellings and algebraic-space terminology. No declaration states this equivalence. Scheme residue-field lemmas are insufficient for attachment.

## WANTED

None. All mathematical sources used are present locally.

## Problems in the starting material

The item was statement-only and had no proof. Its statement agrees with Stacks spaces-morphisms.tex Tag 06EF (lemma-point-finite-type); its clauses are ordered oppositely to Stacks. Tag 06EH is the resulting description of the set, not an independent proof input. No statement dispute or mathematical correction was needed.

The inherited blueprint ancestor is null. `tools/blueprint_refs.py ancestor` also reports null. I preserved the existing ancestor and via metadata, and retained its detailed place describing the path through Tag 0CXU and the alteration input. I read the newest blueprint chapter, the unit `_section.md`, and `sk-thm-sf-ctf-stability-direct-images.proof.md` in `literature/blueprint/latest/`. The live unit JSON retains an older formulation and a different chapter field; I did not edit either fixed record. This item remains a local geometry tool for its assigned route. Whole-blueprint searches for “finite type point”, “06EF”, “field representative”, and local finite type found no equivalent blueprint theorem. The field-representative hit is the unrelated site-perfect-complex definition. `same_as` remains empty.

The Mathlib closed-point criterion returned by semantic searches assumes `JacobsonSpace`. I read Morphisms/Finite.lean lines 209–227 and did not use it as a match for an arbitrary space or scheme. The second phrasing again returned the Jacobson condition. Loogle returned the scheme closed-immersion local-finite-type instance and the same Jacobson criterion; neither supplies this item. The source grep had zero hits for AlgebraicSpace and the finite-type-point spellings. All new search entries are exact queries recorded by msearch; the existing search history is retained.

## Unfinished work

None at stage 1. The existing dependencies are cited as statements; their own future splits are separate items. No Lean file was written and no compiler or build tool was run.

## Not duplicates

No new nodes. The scheme characterization is already `lem-sfb-finite-type-field-point-characterization`; the maximal-ideal existence theorem is already `lem-weil-pbc-proper-ideal-contained-in-maximal`; chart calculus and fibre-product/covering facts also already exist. The selection of a finite type point is a short elementary step from these statements, not a new node or a disguised clause of this item.

## Review by Q25

I read Stacks spaces-morphisms.tex Tag 06EF, statement and both proof paragraphs, and Tag 06EH. I also read morphisms.tex Tag 01TA, including its four equivalent conditions and proof, and algebra.tex Tag 00E0, including maximal-ideal existence and the Zariski closed-set description. The open-immersion source is morphisms.tex Tag 02GP. There are no new nodes needing source review.

In step 1 I checked the full statement of `lem-sfb-finite-type-field-point-characterization`: its condition (iii) is closedness in an affine neighbourhood plus a finite residue extension, not global closedness or a Jacobson hypothesis. A globally closed w stays closed in an affine neighbourhood, and the identity residue extension has degree one. The statement explicitly gives local finite type. `def-weil-residue-field` supplies the residue field, `def-trf-algebraic-space` fixes the field-point convention, and the full statement of `lem-sfb-stack-chartwise-smooth-etale-calculus` supplies both etale implies local finite type and composition. Its hypothesis is representability by algebraic spaces, which maps of algebraic spaces satisfy, and schemes are their representable special cases. This gives the required representative itself, rather than just a property of x.

In step 2 the atlas exists in the statement of `def-trf-algebraic-space`. I checked `lem-trf-space-fibre-products-etale-covers` in full: it gives precisely the scheme V and the surjective etale base change q, including the point-class convention. `def-weil-affine-spectrum` makes Spec K a singleton, so surjectivity implies nonemptiness. The same chartwise calculus gives local finite type for p as the base change of a; the statement of `lem-sfb-space-local-properties-chart-test` explicitly identifies the extended property with the ordinary scheme property when both objects are schemes. The equation ep=aq is the defining fibre-product equation, not an unproved comparison. No Noetherian assumption or finiteness of the atlas was used.

In step 3 I checked the maximal-ideal theorem's actual statement: every nonzero commutative ring has a maximal ideal. Nonemptiness supplies a prime of A, making A nonzero. A prime containing a maximal ideal equals it, hence V(m) is the singleton and is closed in the selected affine open. This is a direct calculation with the affine spectrum definition. Applying the existing scheme characterization to the canonical residue-field map into V, with that affine open and the identity residue extension, gives its local finite type. This is the explicit argument behind the source's instruction to choose a finite type point. I marked only this short assembly elementary; maximal-ideal existence and the scheme characterization are both cited, not asserted as elementary. I did not assume that v is closed in all of V, or that every nonempty scheme has a globally closed point.

In step 4 the calculus supplies composition, and the scheme characterization supplies an affine neighbourhood of the image point in U where it is closed. `lem-weil-pbc-open-immersion-etale` explicitly states that the inclusion of an open subscheme is etale. The calculus composes that inclusion with the original etale atlas. The representable etale convention is in `def-trf-algebraic-space`. Finally the fibre-product equation after r says ep r=aq r; the field-spectrum definition turns qr into the embedding K into L, so the two representatives agree after a common field extension. This verifies exactly the requested image x and gives W=U_0; it does not claim u is globally closed in the original atlas.

I checked the edge cases: the empty space has no x, so the assertion is vacuous; for X=Spec k the identity chart and representative work; for the generic point of Spec of a DVR the generic open is the spectrum of its fraction field, illustrating why a closed chart lift need not be globally closed in X. Nothing uses a Jacobson, Noetherian, quasi-compact, or separated base. I checked that the cited nodes do not reach the item and that proof_deps equals the union of uses. Every non-elementary step is below 2000 characters. I copied quotations directly from all cited statements into citations.json and checked their membership. The off-unit space fibre-product theorem is declared in split_report.tool_uses as a generic chart-construction tool; no trace-formula argument replaces the unit route. The remaining off-unit inputs are definitions or Mathlib leaves. The delivery-errors B–E checks therefore leave no hidden theorem, new duplicate, clause restatement, missing hypothesis, or source-dependent statement alteration.
