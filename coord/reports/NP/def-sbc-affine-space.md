## Worker report

Files written: dag/nodes/sec-smooth-base-change/def-sbc-affine-space.json — definition, Mathlib leaf. No new nodes. citations.json is empty because a definition leaf has no proof steps.

Attachments: none. The project file WeilConjectures/Mathlib/AlgebraicGeometry/AffineSpace.lean imports Mathlib.AffineSpace and extends it; it does not declare the entire item itself. No exact blueprint tag was found in the project source. Master sorry declarations were not treated as finished proofs.

WANTED: none.

## Statement corrected

STATEMENT-DISPUTED: the imported ordinary Spec(O_S[x_1,...,x_n]) applies ordinary spectrum to a sheaf, rather than a ring, for a general scheme. Replacing O_S by global sections would also be false: for S=P^1_k and n=0 it gives Spec k rather than S. Stacks 01M0 explicitly uses relative spectrum. I corrected this to its equivalent base-change definition, also written immediately after 01M0, and spelled out the relative-spectrum interpretation. A^0_S=S denotes the canonical isomorphism, not literal equality of chosen scheme objects. This retains arbitrary S and every n>=0; it adds no hypothesis and does not change the unit route. Smoothness is retained as a pointer to the separate theorem, not asserted here.

Nothing unfinished.

## Not duplicates

No new nodes. Blueprint search for affine space and DAG search found def-nagata-relative-affine-space; same_as records that identical notion. That existing node uses symmetric algebra of the free rank-n sheaf, locally the same polynomial ring. No replacement copy was created.

## Review by NP

I read constructions.tex, Tag 01M0 (definition-affine-n-space), and the paragraph in Section 01LZ giving the base-change construction. They assume only a scheme S and a nonnegative integer n, exactly as the corrected item does. I also read the blueprint item, its sk-def-smooth unit and chapter, and the existing def-nagata-relative-affine-space statement. The unit has no proof steps; defining the affine-space notion through Mathlib does not replace its smoothness route.

There are no proof steps and hence no C1/C4 proof citations to audit. For the statement, the scheme convention, ordinary affine spectrum and fibre-product nodes provide the objects used in the displayed base-change definition; the final smoothness reference is only a pointer and is not a dependency (it depends on this item). No new theorem, hidden lemma or clause-restating child was introduced (B1-B4, C5, D1-D5). The literature label/tag was checked in the Stacks tags table (B5); the definition is self-contained and written once in TeX (B2-B4, B7).

I read Mathlib/AlgebraicGeometry/AffineSpace.lean lines 44, 66, 168-198, 228-232, 255-265, 325-330 and 442-451. AffineSpace is the exact base-change construction; over is the first projection. SpecIso and SpecIso_inv_over identify the affine chart and its constants-inclusion structure morphism, and isPullback_map gives the restriction along an affine-open inclusion. The empty-index instance makes that very projection an isomorphism. These are one declaration per clause with the finite-coordinate specialization, not a claim that the whole base is affine. All recorded searches ran through msearch.py; LeanSearch was actually unavailable and is recorded that way. The first grep restricted to a single file has malformed file fields from the wrapper, so I repeated it on AlgebraicGeometry and read the actual paths and lines (B6-B8).

Small cases checked: n=0 gives the projection isomorphism even for nonaffine S=P^1_k; n=1 and S=Spec R gives Spec R[x] with the constants map; S empty gives the empty base change for all n, and zero rings are allowed. No finite-type, Noetherian, field, nonempty, or affine-base assumption was added. The relative-spectrum correction resolves the wrong-object/type error (E1-E4); there are no vague transport arguments (E5), and ordinary versus relative Spec is explicitly distinguished (E6-E7). All imported flags and blueprint metadata are retained. No new nodes require further source or duplicate audits.

## Second reading by NP

- Item statement: checked constructions.tex Tag 01M0, label constructions-definition-affine-n-space, and its following base-change paragraph against every clause; PASS. Both permit arbitrary schemes and n >= 0. The STATEMENT-DISPUTED correction above faithfully repairs ordinary Spec applied to a sheaf; for S = P^1_k and n = 0, taking global sections would incorrectly give Spec k.
- Proof steps: none; PASS for a definition Mathlib leaf. citations.json remains [] because there are no proof citations. Smoothness is only a pointer to sbc-lem-affine-space-smooth, whose statement was read and which depends on this definition; no reverse dependency was added.
- New nodes: none; PASS. Read def-nagata-relative-affine-space: its symmetric-algebra construction and polynomial charts describe the same notion, already recorded in same_as. No duplicate or clause-restating child was introduced.
- Definition dependencies: read def-pc-fibre-product (universal property and projections), def-weil-affine-spectrum (ordinary Spec and induced maps), def-weil-pbc-scheme-conventions (explicitly only a collection of conventions), and def-pc-scheme (scheme and affine/open subscheme notions); PASS after citing the actual scheme definition directly. Relative spectrum in the statement is the alternate description of the explicitly defined base-change object, not an undefined construction on which the definition depends.
- Mathlib leaf: independently read Mathlib/AlgebraicGeometry/AffineSpace.lean lines 38-45, 65-67, 168-198, 218-232, 253-265, 324-330 and 440-451; PASS. AffineSpace with ULift (Fin n) is the displayed pullback (the chosen terminal scheme is canonically Spec Z); over is its first projection. SpecIso and SpecIso_inv_over give the affine-base chart and constants inclusion. isPullback_map applied to an affine-open inclusion gives its restriction. The IsEmpty-coordinate instance makes that same projection an isomorphism at n = 0. The universal characterization of relative spectrum agrees with these polynomial charts; no additional smoothness result is claimed here.
- Search audit: ran independent msearch.py Loogle query AlgebraicGeometry.AffineSpace.SpecIso and grep query pullback.*Spec|SpecIso_inv_over|IsEmpty n on AlgebraicGeometry; PASS. Read the returned declarations rather than relying on search summaries. Existing unavailable LeanSearch and malformed single-file grep are honestly described in the first review. Read the project AffineSpace extension: it imports the Mathlib definition and does not replace it. No master sorry declaration is used as evidence.
- Edge cases and route: PASS for n = 0 over a nonaffine base (projection isomorphism), n = 1 over a field (Spec k[x]), the empty scheme (empty base change), and the zero ring (empty spectrum). Read sk-def-smooth and sec-smooth-base-change records and the imported definition: the unit has no proof steps, and its smoothness route is unchanged. B1-B7 and C1-C4 introduce no hidden new theorem or dependency; E1-E7 reveal no missing hypothesis or unexpanded proof argument.

Changes: added def-pc-scheme to the statement and stmt_deps because the conventions node explicitly defines no notion itself (B3); removed the spurious module name from the earlier one-hit Loogle result so results agree with searches.jsonl; recorded the two independent searches with their actual results. Kept the first worker's definition, source correction, leaf decision, and review otherwise unchanged.
