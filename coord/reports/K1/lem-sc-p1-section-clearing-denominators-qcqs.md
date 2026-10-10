# Stage-1 split: lem-sc-p1-section-clearing-denominators-qcqs

## Files written

- dag/nodes/sec-picard-framework/lem-sc-p1-section-clearing-denominators-qcqs.json: split, no new nodes or Mathlib leaves.
- citations.json: verbatim statement excerpts for every citation.
- report.md: this review.

## Attachments

None. AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_eq_restrict in WeilConjectures/AlgebraicGeometry/Modules/ClearDenominators.lean:263 requires separation over an affine base, which the qcqs item does not assume.

## WANTED

WANTED: literature/stacks-project/properties.tex, Properties Lemma 01PW (lemma-invert-s-sections), proof of part (2), for lem-sc-p1-section-clearing-denominators-qcqs. The literature source tree is absent from this checkout. I reconstructed the argument from the reviewed Stacks citation in the existing item and the full source proof in WeilConjectures/AlgebraicGeometry/Modules/ClearDenominators.lean:263-384; accordingly proof_origin.by is agent.

## Findings

The source proof assumes affine overlaps via separation over an affine base. That inference fails for a general qcqs scheme. The revised Step 2 instead uses the sibling qcqs restriction-torsion statement on each quasi-compact overlap. No item clause was moved to a new node. Mathlib searches for the item found only structure-sheaf versions (exists_of_res_zero_of_qcqs_of_top, exists_of_res_eq_of_qcqs_of_top), not the invertible-module assertion. LeanSearch was unavailable (HTTP 500).

## Review by K1

I checked the item's statement against the closed Lean theorem at ClearDenominators.lean:263-384 and the existing reviewed 01PW localization node. The Lean theorem does not attach because IsSeparated f and IsAffine S are strictly stronger than qcqs. I read the sibling restriction-torsion statement, the affine tilde-section leaf, the finite affine-cover leaf, the invertible and quasi-coherent definitions, and the tensor quasi-coherence statement before citing them.

Step 1 uses the invertible-module and quasi-coherent definitions to get both properties on a sufficiently small affine neighbourhood of each point. The quasi-compact definition gives a finite subcover. The tilde-section leaf identifies the presenting module with sections on that affine chart (at r=1), then identifies sections on each principal open with its localization. I checked the local equality: if u=v_i/f_i^a_i and a>=a_i, then f_i^(a-a_i)v_i tensor e_i^a restricts to u tensor s^a. The nonvanishing locus is D(f_i) because s(x) is nonzero in the residue fibre exactly when f_i is not in p_x.

Step 2 uses the item's quasi-separated hypothesis to make W_ij=V_i intersect V_j quasi-compact. Since affine opens of W_ij are affine opens of X, the overlap is also quasi-separated. The tensor node states that F tensor L^a is quasi-coherent. The restriction-torsion node states exactly that a section vanishing on the nonvanishing locus is killed by a power of the same invertible section, so it applies to the difference d_ij on W_ij. This replaces the source proof's invalid affine-overlap inference for the present hypotheses.

Step 3 takes the maximum of the finitely many exponents, checks the overlap difference is zero after multiplication, and glues the compatible sections. No uncited theorem is needed beyond the sheaf axiom and finite maximum. Edge cases checked: X=Spec k with s=0 gives the empty nonvanishing open and t=0; s invertible gives m=0; for F=0 all local fractions and differences are zero. I found no new statement to test and no unfinished part.

## Second reading by K1

Source and statement: I read the local copy `/home/ubuntu/c1-stacks-review/properties.tex`, label `lemma-invert-s-sections` (Tag 01PW), lines 2226-2320. Its part (2) assumes exactly a qcqs scheme, an invertible sheaf, a section, and a quasi-coherent module; surjectivity is the item's clearing-denominators conclusion. The source tree remains absent from this repository checkout, as the first review reported.

Step 1: Checked against 01PW's finite trivializing affine cover and local-fraction paragraph, and against the statements of `def-sc-invertible-module`, `pqf-def-coherent`, `def-weil-pbc-quasi-compact-scheme`, and `lem-weil-pbc-spec-module-tilde-sections`. Principal opens refine both local conditions; the cited tilde-section localization supplies the fraction. Verdict: sound, including the residue-fibre test giving `D(f_i)`.

Step 2: Checked against 01PW's quasi-compact-overlap paragraph and the exact statements of `lem-sc-invertible-tensor-qcoherent` and `lem-sc-p1-section-restriction-s-torsion`. Each overlap is qcqs, and its twisted module is quasi-coherent, so the latter lemma kills precisely the displayed difference. Verdict: sound; no affine-overlap assumption.

Step 3: Checked against 01PW's common-exponent and gluing paragraph. The finitely many exponents have a maximum, multiplication makes every overlap difference zero, and the sheaf axiom glues the sections. Verdict: elementary and sound.

New nodes: none; there are no new statements to compare, deduplicate, or search. For the item statement, the empty scheme has the zero section and `m=0`; over a field, `s=0` gives `X_s=empty` and `s` invertible gives `m=0`; the zero module gives `t=0`. These cases agree with the claim.

Changes: appended this source-based second reading. No node or citation needed repair; the six existing citation quotes are verbatim excerpts of the cited statements.
