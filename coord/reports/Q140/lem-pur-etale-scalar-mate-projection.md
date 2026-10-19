# Stage-1 report: lem-pur-etale-scalar-mate-projection

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-etale-scalar-mate-projection.json: statement node split into four steps; no exact Mathlib match. The statement, statement dependencies, source, creation metadata, unit and blueprint ancestry are unchanged from the current shared repository.
- citations.json: 13 verbatim statement citations covering every node used by the four proof steps; checked against the current repository.
- report.md: this report completes the retained attempt, which already supplied the item, citations, generator script and searches.jsonl.

New nodes: 0. Mathlib leaves: 0. No unit record is changed: this helper is not the unit's key statement.

## Attachments

None. Searched the read-only slopmaster2 WeilConjectures source for the exact blueprint tag and scalar/mate/projection terminology. The rational projection-formula documentation discusses scalar compatibility but does not supply this declaration or all its clauses. General Mathlib adjunction/counit statements and module scalar-change counits do not state the derived sheaf comparison. The existing retained LeanFinder, LeanSearch, Loogle and grep searches and their actual logged results were read and preserved. Additional searches already present in searches.jsonl are now recorded, without rerunning unchanged queries.

## WANTED

None. All source text used is available locally.

## What was wrong or incomplete

The imported item had no proof. The retained sandbox supplied its four-step proof but had no report, so it had not reached the required delivery checks. I compared its statement and metadata with the current shared node and kept them. No statement dispute or source correction is necessary. The Stacks coefficient-change remark 0GL6 asserts commutation for compactly supported image with torsion coefficients; it does not itself state the present arbitrary-ring equality of specified maps. Accordingly the node's proof_origin is agent, and the four steps explicitly establish that equality using canonical comparisons, rather than treating the remark as a stronger theorem.

The relevant current blueprint is main-20261015, sec-six-functors-basics/sk-prop-sf-cbc/prop-finite-compact-support-constructibility.proof.md, Step 5, the coefficient-reduction clause. The item is the direct-image scalar-mate normalization used inside that clause. It does not assert invertibility of the projection map or a compact-support theorem. The stored unit is sk-prop-sf-cbc; no route or unit metadata is altered.

## Not duplicates

No new nodes are proposed. Whole-blueprint search for scalar mate projection returned no match; the ancestry command returns prop-finite-compact-support-constructibility. The retained split reuses the existing scalar/tensor, derived-change-of-rings, K-flat, ringed-topoi pullback, projection-map and restriction-adjunction nodes. The comparison normalization in Step 2 is calculated directly on the specified models; it is not outsourced to a second copy of the item.

## Review by Q140

I read the small-sites/derived-adjunction statements of every cited node and the relevant local Stacks source: more-etale.tex remark-Rf-lower-shriek-change-of-rings (0GL6); sites-cohomology.tex lemma-pullback-tensor-product (07A4), lemma-pullback-K-flat (0G7E), lemma-K-flat-resolution (06YS), lemma-derived-base-change (06YY), and remark-base-change (07A7). I read the current main-20261015 ancestor proof and its coefficient-reduction clause. There are no new nodes with separate sources to review. These sources motivate the tensor models and counit transpose; the source's stronger torsion/properness assumptions are not silently dropped from an isomorphism theorem, because the present conclusion is only equality of two maps and is proved by the displayed calculation.

Step 1 uses lem-pur-change-of-rings-tensor-comparison for its actual natural sheaf isomorphisms e_M, including the morphism formula, lem-pc-kflat-resolution for K-flat resolutions with flat terms, and lem-pur-derived-change-of-rings for computing derived scalar extension on those models. Thus the scalar/tensor identification is natural, rather than merely an objectwise isomorphism. Its left/right tensor order is fixed by symmetry. The statement of lem-sbc-canonical-restrict-scalars-functor-comparisons supplies the canonical inverse-image and direct-image comparisons a and d. I checked the direction of d is U_W R_B -> R_A U_Z and that every use is bounded below. The two B-objects M and N have exactly the boundedness hypotheses imposed by the item; right derived image and exact inverse image keep the displayed objects in D+.

Step 2 cites lem-weil-pbc-ringed-topoi-derived-tensor-pullback for preservation of K-flat complexes with flat terms and the canonical tensor/pullback isomorphism, not just the definition of pullback. It uses the same K-flat-resolution, scalar-change and sheaf scalar/tensor nodes as Step 1 and the actual canonical inverse monoidal comparison in def-kun-projection-formula-map. With C represented by P, extension is P tensor B and forgetting its action retains that tensor complex and its maps. Exact inverse image computes F_A(P tensor B) termwise. Thus both sides of the displayed normalization are the same ordinary pullback/tensor map. Only P must be K-flat; no flatness or K-flatness of the coefficient module B is assumed. This is a direct computation of the fixed comparisons, not a new independently hypothesized lemma or an assertion of the final mate equality.

Step 3 uses precisely the counit clause of lem-sbc-restrict-scalars-derived-adjunction-identities at N. Its stated formula, composed with F_A(d_N), gives epsilon^A F_A(d_N)=U_Z(epsilon^B) a. The next equality is naturality from lem-sbc-canonical-restrict-scalars-functor-comparisons, and the final equality is the defining B-adjoint transpose, using the canonical adjunction specified in def-kun-projection-formula-map. I checked the source of a in that equality is R_B N, and the naturality substitution is beta:M -> R_B N. Both lie in D+. This avoids invoking a bounded-below comparison on an arbitrary unbounded complex.

Step 4 substitutes the previously proved normalization and naturality formula into that transpose. The resulting (epsilon tensor 1) t_C is exactly alpha_{J,B_W[0]} in the statement of def-kun-projection-formula-map. Injectivity of the adjunction Hom bijection proves equality of the original morphisms. Naturality is written as a separate explicit equation in v:J -> J', then obtained by applying L_Z and the Hom bijection. This step is elementary from the displayed equations and the cited definition; it does not invoke an uncited projection-formula theorem. The naturality domain consists only of endpoints satisfying the item's boundedness assumptions.

I checked identity f and identity A -> A, where the formulas reduce by the triangle identity to the identity map, and J=0, B=0 and empty schemes, where both maps are the unique zero map. A nonflat quotient B (for example Z -> Z/2) requires no flatness: the derivation continues to use K-flat resolutions and the explicit boundedness assumptions. Ordinary uncompleted tensor is used throughout. There is no properness, invertibility, torsion or flatness premise smuggled into a step. No statement was weakened.

Against B--E of delivery-errors: all symbols are introduced; every non-elementary input is an existing cited statement; no new node hides a clause of the item; all 13 citation quotes are verbatim current statement substrings; proof_deps is the union of uses; the steps are 1060, 1208, 942 and 969 characters, so none exceeds the 2000-character review threshold. The off-unit generic tools are declared only in split_report.tool_uses for maintainer review. No SGA source is used. No Lean, compiler, Lake, live-project write or direct git command was used.

## What remains

The mathematical split is complete. Required dry-run and push results will be appended after the delivery tool exits.
