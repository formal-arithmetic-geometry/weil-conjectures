# Stage-1 delivery: lem-sfb-pointed-cover-compatible-unit-roots

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-pointed-cover-compatible-unit-roots.json: statement split into nine argument steps; mathematical statement and hypotheses preserved, doubled TeX escapes normalized.
- dag/nodes/sec-six-functors-basics/lem-sfb-residue-unit-reduction-surjective.json: statement, Mathlib leaf, exactly ZMod.unitsMap_surjective (Mathlib/Data/ZMod/Units.lean:46). This is one new node and one Mathlib leaf.
- citations.json: every use in every numbered step has a verbatim quote of the cited statement. The full statements are quoted so their hypotheses remain visible.
- searches.jsonl and write_split.py: retained sandbox research log and construction script; these are not project changes.

## Attachments

None for the item. Project-source searches for its blueprint tag and pointed/compatible roots found no declaration with the whole statement. KummerSystem in FieldTheory/KummerFreeSubgroup.lean is data for a single prime-power field tower, not this theorem. ZMod.castHom_unitsLift (SixFunctors/ProEtale/Adic/ZModPowAutLift.lean:163) lifts a unit residue class; it does not itself state the surjectivity theorem for unit groups, so the latter is delivered as the Mathlib leaf rather than an attachment. Existing primitive-root and compatible-Tate-basis statements do not state prescribed normalized roots on this particular cover.

## WANTED

None. All documents needed for this proof are available. I do not use SGA.

## Corrections and scope

There was no proof in the item. I preserved its sources, created record, unit and blueprint chain. The only statement edit removes doubled TeX backslashes; no mathematical hypothesis or conclusion changes. In particular the existence of geometric families is a choice, and functoriality means the normalized sections for transported labels commute with pointed morphisms. It does not mean there is an automorphism-invariant canonical choice of primitive roots in every algebraically closed field. The proof now explicitly distinguishes those assertions.

The inherited Bhatt–Scholze citation supplies background for the already existing pointed-cover node; Lemma 7.4.3 itself is about profinite torsor classification and Construction 7.4.4 about open-subgroup covers. I do not treat those sentences as a direct proof of a new universal-cover theorem or add a noetherian assumption. The actual input is the exact existing statement of lem-sfb-pointed-finite-etale-limit-cover, valid for the connected qcqs base here.

The proof of invertible differences does not assume that a function nonzero at the single marked point is a unit. A split finite algebra provides a polynomial separating two labels; the explicit difference identity gives an inverse. This works in rings with nilpotents and zero divisors.

## Not duplicates

lem-sfb-residue-unit-reduction-surjective vs lem-sc-primitive-root: the new leaf states surjectivity on units of integer residue rings, with no field or roots; the existing node gives cyclicity and existence of scalar roots but not a compatible family or the arithmetic lifting property.
lem-sfb-residue-unit-reduction-surjective vs lem-galois-inverse-limit-surjective: the existing Mathlib leaf assumes surjective maps of finite sets; the new leaf provides the particular arithmetic surjectivity needed before applying it.
lem-sfb-residue-unit-reduction-surjective vs lem-poincare-compatible-primitive-roots: that node produces an abelian sheaf isomorphism on some pro-etale cover for one prime-power tower; the new leaf concerns two arbitrary positive divisibility moduli, and is used inside the direct proof here. Neither is the pointed-cover item in another form.

DAG searches used both statement text and full JSON for unitsMap_surjective, unitsMap, units modulo, residue-unit reduction, monic quotients and compatible primitive roots. I found and reused lem-weil-pbc-monic-quotient-free rather than creating the power-basis node suggested by search results. Whole-blueprint searches with blueprint_refs.py used compatible roots, primitive, unit roots, inverse limit, power basis, units modulo, reduction units, unit group, Kummer, monic quotient and unitsMap_surjective. No blueprint node states the new arithmetic leaf or the full item. The new node has a Mathlib source, no Stacks tag shared with existing nodes. Its blueprint ancestor is None, as the ancestor command reports; its via list prepends the item to the inherited chain.

## Review by Q49

I read the chapter record and the unit sk-thm-sf-ctf-stability, the current main-20261015 direct-image proof paragraph (3), and the item's existing provenance. This is a local expansion of the residual-cover and unit-coordinate argument recorded in former parent steps 7, 8, 20. It does not replace the open-direct-image route or edit a chapter or unit. The item is not a key unit statement, so no realization record is changed.

I read Stacks algebra.tex Tags 00UB/00UC, labels definition-standard-etale and lemma-standard-etale, and etale-cohomology.tex Tag 03PL, label lemma-kummer-sequence, including its full root-algebra proof. The latter explicitly uses the finite free rank-n quotient and invertible derivative. I read categories.tex Tag 086J, label lemma-nonempty-limit, and the existing inverse-limit statement, which adds surjectivity of projections under surjective transitions. I read the blueprint primitive-root statement and proof. For the new arithmetic node I read Mathlib/Data/ZMod/Units.lean lines 25–68: unitsMap is exactly reduction on units, and unitsMap_surjective requires NeZero m and n dividing m. Positive m in the new statement supplies that instance; there is no unrecorded primality condition on m or n. The service hits were read and their queries were logged by msearch.py; the second phrasing again returned the exact declaration. There is no unavailable search disguised as a no-match.

Step 1 uses def-weil-geometric-point for an algebraically closed Omega and lem-sc-primitive-root for cyclicity and cardinality at every prime-to-p modulus. The map E to Omega forces characteristic p, since it is unital and p is prime. The elementary order formula verifies that the power transition sends primitive roots to primitive roots.

Step 2 uses the cyclic generator statement of lem-sc-primitive-root and exactly the surjectivity statement of the new leaf. Writing a prescribed primitive n-th root as a coprime exponent relative to eta^(m/n), lifting that exponent to a unit modulo m, and exponentiating eta proves the actual surjectivity needed in step 3; it is not moved into a new compatible-root node.

Step 3 checks nonempty directedness (1 and products), finiteness, nonemptiness and all transition hypotheses before using lem-galois-inverse-limit-surjective. That node's statement, not merely its source, gives a point of this inverse limit. Identity and composition are exponent identities from step 2.

Step 4 uses def-weil-algebraic-closure for existence of roots of each nonconstant polynomial, lem-sc-primitive-root for the finite torsor cardinality, and the same finite-set inverse-limit node. Nonzero target s(a_j) ensures that every root is nonzero. Given b at level n, a root of X^(m/n)-b lands at level m and maps to b, so this application also has genuinely surjective transitions. Finite products/finite choices require no separate node.

Step 5 uses exactly the basis and finiteness clause of lem-weil-pbc-monic-quotient-free, and the statement of lem-sbc-root-split-away-cover-etale: its hypotheses are a commutative ring, positive n invertible in it, and an arbitrary g. Bezout with p verifies invertibility of n here. With g=a a unit, D(a) is all of Spec A, so its conclusion gives the entire root scheme etale. No local regularity or noetherianity from another root lemma is assumed. Both cited statements were opened in full.

Step 6 uses the stated connectedness and canonical natural splitting of lem-sfb-pointed-finite-etale-limit-cover. Spec E is affine and thus qcqs, connected and nonempty by hypothesis. The polynomial quotient Hom bijection of lem-asd-polynomial-quotient-hom-equivalence and the affine Hom correspondence of def-weil-affine-spectrum identify labels and sections with roots. The partition argument proves uniqueness on this connected cover; the inverse a^(-1)b^(n-1) proves that each lifted root is a unit. This is a direct construction, not a citation of an unstated cover-units theorem.

Step 7 cites those same quotient and splitting statements for substitutions and functoriality in finite covers. I checked the exact equation (X^(m/n))^n=X^m and the direction of the contravariant algebra map. Uniqueness from step 6 gives all power equalities, including that normalized powers have the expected primitive-root labels.

Step 8 uses the same full splitting statement and affine/quotient correspondences. Finite disjoint unions of copies of an affine scheme have the product ring of global sections (sections on a disjoint union are tuples). The inverse image of a coordinate idempotent is represented by a polynomial by the definition of a quotient ring. The displayed two-line polynomial difference identity explicitly constructs the inverse of the difference. No separate lemma, CRT assertion or maximal-ideal criterion is hidden. This short ring calculation is marked elementary and all its geometric inputs are cited.

Step 9 uses the stated pointed naturality of the cover theorem, not a general unspecified transport principle. The quotient Hom bijection proves the base-changed root presentation by evaluating the generator, and the affine Hom correspondence gives equality of root values after pullback. Pullback sends the specified label to its transported label, so uniqueness from step 6 proves equality of the sections; step 7 proves compatibility with powers. The argument allows a geometric-field extension, reading its labels through that field embedding.

I tested n=1 (the unique root of unity is 1, difference assertion vacuous, unit root is a_j), n=m (identity transitions), empty unit family, p=2 and odd n, E=F_p and E=F_p[epsilon]/(epsilon^2). The construction never uses reducedness, integrality or finite type. The zero ring is excluded by nonempty spectrum; the marked point also ensures H is nonzero. The new arithmetic node includes n=1, m=1 and n=m; each is an immediate surjectivity case in the exact Mathlib theorem. A non-prime-to-p n is never used. The graph search checked that the cited off-unit statements do not depend back on this item. Generic off-unit tools are declared in split_report.tool_uses with their precise purpose. Every proof step is below 900 characters, so none exceeds the long-step threshold. All new-node fields, statement-only leaf shape, hypotheses, sources and citations were checked against delivery-errors B–E.

## Unfinished work

No part of this one-level split remains unfinished. Existing unsplit dependencies remain the existing queue's obligations. No Lean file was written, no compilation was run, and neither the repository nor launcher files were changed.

## Dry-run repair

The first dry run required a definition citation and a structured line field on the Mathlib leaf. I opened def-weil-pbc-algebra-hom-quotient: its statement explicitly defines quotient rings and their quotient maps, so I cited it for the integer quotient rings (the unit group is defined inline). I added mathlib_match.line = 46, the line already read and described in how. I updated the verbatim citation to this leaf. No proof or mathematical statement changed.
