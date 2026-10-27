# Stage-1 report: lem-sfb-graded-affine-monomial-models

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-graded-affine-monomial-models.json: statement, split; six proof steps; no exact Mathlib match.
- citations.json: one verbatim statement quote for each node used in each proof step.
- searches.jsonl: records produced by the required msearch.py commands, read before recording their verdicts.
- report.md: this report.

No new nodes and no new Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures/ for the exact blueprint id, graded-affine language, homogeneous generators and monomials; the project has graded sheaf structures and degree-zero local generation, but no declaration giving every clause here. Read WeilConjectures/AlgebraicGeometry/GradedSheafStructures.lean and Sheaf/AlgebraicGeometry/GradedSheafGeneration.lean. The latter defines the required arbitrary homogeneous generation condition; it does not prove this item.

## WANTED

None. The Stacks sources required for the argument are available locally.

## What needed correction

The item was statement-only; its statement is correct and unchanged. In particular, local homogeneous generation is not global surjectivity on arbitrary opens. The proof now first obtains local degreewise monomial expressions and then uses the existing quasi-coherent affine image theorem to obtain sectionwise generation on the affine cover. A module generator of degree b contributes only in degrees d >= b. Algebraic direct sums of modules of affine sections are used exactly as in the statement; the proof does not replace them with global sections of a sheaf direct sum.

The current blueprint is literature/blueprint/latest/. I read its sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, clause (3). The long inherited DAG chain refines that direct-image input via Hilbert/graded-rank arguments; nothing at chapter or unit level is changed. The ancestor command returns from.node = None for this existing chain. I retain the inherited null node, precise place and via list, rather than invent an ancestor. The latest blueprint filenames use sk-thm-sf-ctf-stability-direct-images where inherited ancestry text names det-thm-sf-ctf-stability-direct-images.

## Searches and reuse

I searched the whole DAG for Tags 00K0, 01HV, 01IA and 01IB, and for monomials, finite affine covers, finite-type affine sections, affine generators, affine image/cokernel calculations and stalk localization. I ran blueprint_refs.py search for graded, monomial, 01IB, and graded affine, and its ancestor command for this item. None of the blueprint hits states this combined item. Existing stronger or generic nodes supply all external facts; no new node is justified.

The original item's recorded searches remain intact. New required msearch.py queries (two LeanFinder phrasings, LeanSearch, Loogle and grep) are recorded exactly in the search log and copied to the item's mathlib_searches. I read the returned local-generator/finite-presentation results and the homogeneous-localization span theorem. Mathlib/Algebra/Category/ModuleCat/Sheaf/Generators.lean defines ordinary sheaf generators and local generator data; Quasicoherent.lean handles ordinary finite presentations; HomogeneousLocalization.Away.span_mk_prod_pow_eq_top (HomogeneousLocalization.lean:949) concerns degree-zero localization of an algebra already supplied with ring generators. These do not state the present graded-sheaf affine-model theorem or specialize to it in one line. The Proj cover theorem is a different assertion.

## Not duplicates

No new nodes. Existing finite-type affine generating-sections, image/cokernel, finite free tilde, affine module-germ localization, ring-stalk localization, and residue-field comparison nodes are cited instead of making special cases of them.

## Review by N0

I read Stacks algebra.tex Tag 00K0 (lemma-graded-module-fg), including its monomial proof, schemes.tex Tag 01HV (lemma-spec-sheaves, especially (2), (6), (7)), Tag 01IA (lemma-quasi-coherent-affine), Tag 01IB (lemma-equivalence-quasi-coherent), Tag 01IT (lemma-basis-affine-opens), and the affine quasi-coherent image/cokernel argument of Tag 01IC (lemma-kernel-cokernel-quasi-coherent), together with properties.tex Tag 01PB (lemma-finite-type-module). The monomial and fibre arguments are adaptations written explicitly here, so proof_origin is agent. There are no new nodes requiring independent source reviews.

For step 1 I checked that def-sfb-graded-sheaf-generation supplies sections on a neighbourhood with a spanning condition valid on every smaller open, so restricting to an affine neighbourhood preserves precisely what is needed. lem-weil-pbc-affine-opens-basis explicitly supplies such a neighbourhood. def-weil-pbc-quasi-compact-scheme supplies a finite subcover of this cover. pqf-lem-affine-open-locnoeth states exactly Noetherianness of every affine coordinate ring on a locally Noetherian scheme; only that statement, not its obsolete proof text, is used. It is already a Mathlib leaf. No separatedness or affine-intersection hypothesis is used.

For step 2 I checked pqf-def-coherent: coherence includes finite type, and quasi-coherence of B_1 is an explicit item hypothesis. Restriction of the local finite free surjections gives finite type on U. lem-weil-pbc-affine-finite-type-generating-sections then gives actual finitely many global sections generating the sheaf on this affine U. Its hypotheses are therefore all present. This node is Lean-closed; no extra descent theorem is being assumed.

For step 3 I read both cited generation/graded-structure definitions. The former gives local finite sums of products from degrees 1 and d, and the latter gives the restriction-compatible bilinearity, unit, associative and commutative laws needed to expand them. The induction explicitly includes degree zero, states its assertion on every smaller open, and intersects only finitely many neighbourhoods for each given section and point. It does not assert that those intersections are affine. Thus neither the source's monomial argument nor any unproved algebraic generation theorem is being cited by tag alone.

For step 4 the same generation definition permits arbitrary nonnegative b_j and supplies precisely the degree d-b_j coefficients for b_j <= d. Applying the preceding induction to finitely many coefficients is a direct substitution into that local spanning condition. I wrote out why the exponent sets are finite and what happens when b_j > d. This step is elementary after step 3 and the cited bilinearity laws; it does not restate the item as a new lemma.

For step 5 I opened lem-weil-pbc-spec-tilde-free-module and lem-weil-pbc-quasi-coherent-module-cokernel-image. The first supplies quasi-coherence of the finite free source and the identification of its affine sections with A^N. The second defines the image by local lifts and states in (3) that its sections on an affine open equal the image on sections. Its source and target quasi-coherence hypotheses hold here, the former by the finite free node and the latter by the item. The local expressions make this image equal the entire target, giving the same monomial list on sections. Finally the graded-structure node supplies sectionwise multiplication and action; the assembly uses finite homogeneous support in an algebraic direct sum. This is the precise non-elementary sections step that cannot be replaced by the slogan 'local generators give section generators'.

For step 6 I checked lem-sbc-affine-module-germ-localization: it states localization of the actual module germ map for any quasi-coherent module on any affine open, without a finiteness or Noetherian requirement. lem-weil-pbc-affine-open-stalk-localization identifies the actual ring germ localization and fixes its scalar map. lem-weil-pbc-spec-residue-field-identification supplies the residue-field isomorphism compatible with that map. The tensor-product definition supplies the balanced-map universal property and generation by pure tensors. I wrote the forward map (m/t) tensor c maps to m tensor tbar^(-1)c, its fraction equality check, its balancing over the localized ring, and the inverse m tensor c maps to germ(m) tensor c. Their composites are checked on pure tensors. Thus no uncited associativity or localization-tensor theorem is hidden in the word 'comparison'. The scalar identification is canonical, and the resulting maps are linear over the identified residue field. This is elementary fraction and tensor algebra after the cited localization statements.

I checked delivery-errors B--E individually: no new unsplit proof-bearing or non-self-contained nodes, no duplicate or clause-only nodes, no invented Mathlib leaf or unrun recorded search; every use is a statement-level use with a verbatim quote; no off-route replacement or dependency on the item is introduced; there is no sectionwise surjectivity asserted off affines, no missing Noetherian hypothesis, and no substitution of a proxy stalk. All six steps have fewer than 2000 characters, and each carries its own argument instead of hiding a standard lemma.

Small cases: for the empty scheme choose no charts; for an empty degree-one list the only empty monomial has degree zero and all positive pieces vanish by the induction; for an empty module list every module piece is zero; for d=0 only generators of degree zero contribute; for a sole generator in positive degree b the formula gives zero in degrees below b and includes e at degree b. Zero rings and zero modules satisfy the affine image and finite-generation assertions; a zero-ring affine chart has no points at which a residue-field assertion is required. None of these cases needs an added hypothesis or a statement dispute.

## Unfinished work

None in this stage-1 split. No Lean files were written and no compiler, Lake or build command was run. The required delivery dry run and push follow this report.
