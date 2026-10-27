## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-finite-open-equality-locus.json` (statement, split); `citations.json` (ten verbatim statement quotations). The item's statement and statement dependencies are unchanged. Four proof steps, totalling 2621 characters, use existing nodes only.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. Existing Mathlib leaves reused: finite-closed-map-finite-fibres, affine-opens-basis, base-change-image, open-immersion-base-change, morphism-factors-through-open-subscheme, and the definition leaves. Searches for a separate compatible-point lemma found the existing arbitrary-subset image identity, so no additional point/tensor lemma is needed.

## Attachments

None. Searched the project library for the exact blueprint tag, equality-locus terminology, finite open parts and equalizers. The finite-open-partition thickening declarations and equality of inverse-image sections address different objects; no declaration gives this item.

## Literature and searches

Read Stacks `spaces-more-groupoids.tex`, Tag 04PK, label `lemma-finite-diagonal`, complete statement and proof. Read `morphisms.tex`, Tag 01WN, label `lemma-finite-proper`, and Tag 01S1, label `lemma-base-change-surjective`, including the arbitrary-subset image argument. Read `schemes.tex`, Tags 01HI (`lemma-restrict-map-to-opens`), 01IK (`lemma-open-subspace-scheme`), 01JY (`lemma-base-change-immersion`). Read the latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, particularly (3). The elementary scheme argument is a prerequisite far below its direct-image statement; the inherited ancestry records that chain.

Ran the whole-DAG statement/title searches and blueprint_refs searches for equality locus, finite open, finite closed, fibre product points and open immersion. No blueprint node states this supporting equality-locus result. The item already has a null nearest blueprint ancestor (`blueprint_refs.py ancestor` prints None); retained its inherited ancestry and precise source place rather than inventing a blueprint id.

All six fresh Mathlib searches are logged in searches.jsonl: LeanFinder twice (two phrasings), LeanSearch, Loogle and grep twice. All services answered. Read the hits: formal-unramified diagonals require a morphism and hypotheses unrelated to this equality functor; equalizers of scheme maps are different; general stability of finite/proper/open immersions under base change supplies ingredients only. The second grep finds sheaf equalizer-locus notation rather than this result. Read Mathlib `FormallyUnramified.lean:124-139` and `PullbackCarrier.lean:410-430`. In particular image_preimage_eq_of_isPullback gives exactly the existing base-change-image node, so it is cited rather than recreated. Existing searches in the item are retained; only actual fresh logged searches are appended.

WANTED: none.

## Problems found and corrections

The source ends with 'Now it is clear that V works'. The input statement is correct, but that sentence leaves arbitrary, possibly nonflat base change unproved. The split expands it using the image identity for arbitrary subsets, and explicitly identifies the base-changed open subschemes, rather than treating scheme points as an ordinary set-theoretic fibre product. No statement dispute or source error was found. No Lean was written or compiled, no repository files were changed, and no agents were started.

## Not duplicates

No new nodes. Existing nodes are cited directly instead of creating finite-proper, compatible-point, open-base-change or open-factorization duplicates.

## Review by NQ

I compared the complete item statement with Tag 04PK's proof. Setting its ambient space to a scheme M gives precisely the two finite opens over T, their symmetric-difference image and the universal equality condition. There is no separatedness assumption on M over T in this argument. Finiteness is used only for the restrictions q_i. The restricted structure sheaf and the scheme-test representability clause agree with the source. No new statement needs a separate literature audit.

In step 1 I opened finite-closed-map-finite-fibres: its statement explicitly says the image of every closed subset is closed, which applies to C_i closed in Z_i, not necessarily closed in M. I opened affine-opens-basis: it gives affine neighbourhoods inside any prescribed open V, making the restricted locally ringed space a scheme by def-pc-scheme. The open-immersion definition identifies it with the restriction of the structure sheaf. Complements and finite unions are the elementary topology here. I did not assume intersections of affine opens are affine.

In step 2 the fibre-product definition supplies the universal property used in the written test-map argument: from j_i a = r b one obtains (a,sb), and equality of both projections proves its image is b. I checked open-immersion-base-change has arbitrary scheme base change, so no flatness or finite presentation is required. The image clause of base-change-image gives the inverse image of |Z_i| in |P|. These are statements of the cited nodes, not constructions extracted from their proofs.

In step 3 I checked base-change-image states its identity for EVERY subset C, not just all of its source. This is essential because C_i need not be a subscheme. Applied to q:M to T and h:T' to T it yields s(r^{-1}(C_i)) = h^{-1}(q(C_i)). The two identities combine by preservation of unions under inverse/direct images; empty image is equivalent to empty domain subset. Step 2 identifies their union with the symmetric difference upstairs. The open-immersion definition then upgrades equality of underlying opens to equality of open subschemes with restricted sheaves. There is no reducedness assumption hidden in this upgrade.

In step 4 I opened morphism-factors-through-open-subscheme: it gives UNIQUE scheme factorization for any map whose image lies in an open subscheme. It proves both the bijection and its naturality, since precomposition preserves a factorization and uniqueness identifies the resulting maps. Thus representability is established without an uncited Yoneda or descent assertion. The existing leaves are generic tools; all are mathlib or definition leaves, with no off-route unsplit theorem used.

I checked the small cases: T' empty (both opens upstairs empty and image condition vacuous), Z_1 = Z_2 (D empty and V=T), both opens empty, and just one open empty (V is the complement of that finite open's image). Nilpotent thickenings of T' cause no problem since open subschemes are determined by opens with restricted sheaf; nonflat base change is covered by the arbitrary-subset image lemma. For the doubled-origin affine line over A^1, take its two affine charts Z_i: each q_i is the identity, D={0}, and equality holds exactly away from the origin, verifying the nonseparated ambient case. Checked all quoted statements against uses; citations.json quotes are literal substrings. No step exceeds 2000 characters; no sublemma is hidden in a long step. Sections B-E were checked against the actual files: no new unsplit node, no duplicate clause, no circular proof, no missing non-elementary input, no extra hypotheses and no silent statement change.

The first dry run required longer quotations for def-pc-scheme and def-pc-fibre-product; I replaced both fragments with their complete statements. The mathematical citations and proof remain the same.

## Unfinished work

None in the mathematical split. Delivery validation is run separately by the required server dry run.
