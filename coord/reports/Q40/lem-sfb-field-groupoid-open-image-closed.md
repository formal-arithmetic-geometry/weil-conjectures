# Stage-1 delivery: lem-sfb-field-groupoid-open-image-closed

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-field-groupoid-open-image-closed.json: item, statement unchanged, split into three proof steps.
- lem-sfb-field-groupoid-restriction-open: statement-only supporting lemma, arbitrary field restriction and open surjective middle projection; not in Mathlib.
- lem-sfb-field-groupoid-point-lift: statement-only supporting lemma, adapted lift of an arbitrary point; not in Mathlib.
- lem-sfb-field-groupoid-point-translation: statement-only supporting lemma, translation by an arrow with invertible residue maps; not in Mathlib.
- lem-sfb-scheme-pullback-point-images: Mathlib leaf, AlgebraicGeometry.Scheme.Pullback.range_snd (PullbackCarrier.lean:337) and AlgebraicGeometry.Scheme.Pullback.range_map (same file:355, object-base map specialized to the identity).

All four new files are in the item's chapter. citations.json quotes the actual statements used by each step. Searches were run with the mandatory msearch command; search-results.jsonl retains the complete returned results, and the command's searches.jsonl is retained. No Lean was written or compiled.

## Attachments

None. Searched lean/WeilConjectures/ for the exact blueprint tag, groupoid, restriction, translation and related notions. Its groupoid comments concern descent and invariant neighbourhoods, not the field-groupoid theorem here. Read the existing groupoid definition node and searched lean/Sheaf/ for existing supporting notions as well; no completed declaration of the item was found.

## WANTED

None. Sources are present locally.

## Corrections and scope

The item statement is accurate as an absolute groupoid version of Stacks 04Q6, with base Spec Z in Situation 04Q5. It is retained verbatim: no finite-type, perfectness, quasi-compactness or separatedness assumptions were added. Its empty proof is replaced by the two paragraphs of 04Q6 with the final scheme-point cancellation made explicit. In particular the underlying point set of a scheme groupoid is not silently treated as an ordinary one-object group. The image of the composable-pair map is justified by Mathlib's range_map with identity object map.

The ancestor command returns blueprint.from.node = None; the existing ancestry is inherited, including the long via list. Read the latest blueprint unit and direct-images proof (3), and preserved the item's existing supporting route through the field kernel-relation lemma. The current blueprint proof is broader context; the immediate actual proof source is 04Q6. No unit/chapter file or maintainer field was changed.

## Review by Q40

I read more-groupoids.tex, Situation 04Q5 and Lemma 04Q6, and the full statements and proofs of 04LQ, 04LR and 04LS. I also read groupoids.tex 02VB for restriction, its following definition 02VC, schemes.tex 01JT for genuine scheme fibre-product points, and topology.tex 02YB for the closure argument. The proof follows the source's field-extension and translation route. The closure fact is written directly from open neighbourhoods, so no topology lemma is hidden behind a citation. I checked delivery-errors B through E against the actual files, rather than treating the imported dependencies as sufficient.

Step 1 uses point-lift for a chosen r in the closure: its statement provides a field extension, a point above exactly r, and invertible source and target residue-field maps. The restriction node supplies the actual test-point operations and openness of the middle projection, for arbitrary field extensions. The fibre-product definition gives the Cartesian square by its universal property: specifying a triple of endpoints and an arrow in R1 is the same as specifying an R2 triple and an R1 arrow mapping to its middle arrow. The image leaf's first clause then supplies H'=p2^-1(H), exactly for scheme point images. For any neighbourhood N of r', the open set p2(N) contains r and intersects H, giving a point of N intersecting H'. This proves the needed closure assertion for the chosen lift, not merely existence of some lift in the closure. Continuity makes H' open. The adapted lift can be taken from R2 only, then the same extension is used for R1; no independent or incompatible extensions are chosen.

Step 2 uses the translation node's actual formula, automorphism and identity-image clause, not just a definition of translation. The source and target maps on residue fields are isomorphisms by step 1. Identity compatibility of a puts the identity point in H; consequently L_r(H) is an open neighbourhood of r. The closure hypothesis then supplies a point x in H for which L_r(x) is in H. The groupoid definition states the unit and inverse laws invoked here.

Step 3 is elementary relative to the cited image leaf and groupoid definition: inverse compatibility gives i2(H)=H, and range_map gives a lift of the SPECIFIC point (L_r,i2)(x) of R2 times_V R2. This is stronger and more appropriate than simply lifting two unrelated projections. Its hypotheses hold with S=V, a=b equal to the groupoid morphism, and base map id_V, hence monic. The source/target equations verify that (L_r,i2) is composable. I checked the cancellation on every test scheme: c(c(u t(w),w),i(w)) = c(u t(w),e(t(w))) = u t(w). It is thus an equality of scheme morphisms, not a choice of multiplication on topological points. Since V has one point, the composite u t has constant underlying image r. Composition compatibility then puts r in im(a). This proves closedness after projecting the adapted lift back. All steps are shorter than 2000 characters, with no inline auxiliary comparison lemma left in a long step.

The restriction node matches 04LQ's dotted projection and 02VB's construction. Its explicit source is the last endpoint and target the first, consistent with c(a,b)=a after b. Its statement has no hidden proof or proof sketch. The point-lift node matches both conclusions of 04LR, including arbitrary r and an algebraically closed extension of potentially large transcendence degree; an algebraic closure of k alone is NOT asserted to suffice. The translation node matches 04LS and its explicit inverse: u has s u=id, v has t v=id, v=u(tu)^-1. It deliberately does not claim translation is over k, because tu may be a nontrivial automorphism. I corrected an initially mistyped restriction tag to 02VB after reading the tags table and source; the delivered source is the correct tag.

I read PullbackCarrier.lean:306-380: range_snd is the projection formula and range_map assumes a monic base change map. The identity specialization gives exactly the second clause of the new image leaf. Both lines were verified by msearch grep with the AlgebraicGeometry directory. Searches in the whole DAG included these declaration names, fibre-product point/image terminology, all three new groupoid tags, and the shared restriction tag; blueprint_refs searches included groupoid, 04LQ, 04LR, 04LS, translation, field extension, fibre product and range. The two semantic phrasings for each absent groupoid result returned only unrelated scheme criteria, ordinary groupoids, group objects, or field embedding results. OpenSubgroup.isClosed and GrpObj.mulRight were checked: a scheme-groupoid on Spec k is not generally a topological group, nor a group object over k. They do not specialize to this item or its translation lemma. The field-extension lift requires its own nontrivial argument, not merely SpecToEquivOfField or existence of algebraic embeddings.

Small cases: trivial identity groupoid and identity a give the whole arrow space; the identity-only source groupoid tests that translation still needs the scheme-point argument. For group schemes s=t, this reduces to the familiar open-subgroup proof. For groupoids from nontrivial field automorphisms s and t differ as morphisms despite the one-point object spectrum, which tests both the explicit endpoint convention and the absence of a claim that L_r is k-linear. In characteristic p the field extension is allowed without assuming k perfect. The empty arrow scheme is impossible over a field because of the unit; empty schemes in the image leaf are allowed and make its range equalities empty as required. Nonreduced arrow schemes and positive-dimensional or infinite-type arrow schemes violate none of the hypotheses used.

B1/B2: new non-leaves carry complete self-contained statements only and no proof dependencies; their notions cite field, spectrum, groupoid, field extension, fibre product and residue field definitions as appropriate. B4/B5: single TeX escapes in decoded text and correct Stacks tags. B6/B8: the Mathlib leaf records both declarations with verified lines. C1/C4: citations.json quotes the statements, including the image formula rather than a mere fibre-product definition for the non-elementary point lift. D1/D2: none of the three groupoid nodes restates the item's closed-image assertion or a clause of it. E1/E4: no assumption of finite type, a perfect field, equal source and target maps, or a surjective map on field-valued points was used.

## Not duplicates

lem-sfb-field-groupoid-restriction-open vs lem-sfb-field-groupoid-perfect-restriction: the existing lemma selects a perfect extension with homeomorphic arrow projections; it neither treats an arbitrary extension chosen to adapt a point nor states openness for that extension.
lem-sfb-field-groupoid-restriction-open vs lem-sfb-field-kernel-relation-immersion-closed: the existing lemma concludes closedness from locally closed image and closed immersion from immersion; it does not supply arbitrary field-extension openness. It is an ancestor using this item, so it cannot be cited here.
lem-sfb-field-groupoid-restriction-open vs lem-sfb-fppf-groupoid-restriction-quotient: the existing lemma assumes an fppf object cover and proves quotient invariance/monicity descent; it does not state openness or surjectivity of the middle projection for arbitrary field extensions.
lem-sfb-field-groupoid-restriction-open vs def-sfb-restricted-groupoid-relation: the existing node is an arbitrary relation fibre-product definition and does not assert a groupoid structure or openness/surjectivity of its middle map.
lem-sfb-field-groupoid-restriction-open vs lem-a1-groupoid-invariant-open-restriction-degree: the existing node restricts to an invariant open object subscheme and concerns finite locally free degree; a general field extension is not such an open subscheme.
lem-sfb-field-groupoid-restriction-open vs lem-a1-affine-groupoid-invariant-rank-strata: the existing node assumes finite locally free maps and constructs rank strata; it does not address field extensions of arbitrary groupoids.
lem-sfb-field-groupoid-restriction-open vs lem-a1-clopen-relation-base-change-identification: the existing node is about an equivalence relation and a clopen subscheme after base change; it does not give the middle projection for field-groupoid restriction.
lem-sfb-field-groupoid-point-translation vs lem-sc-translation-automorphism: the existing statement is for a group scheme and a k-rational point with a single structure map; the new statement allows a field-groupoid with distinct source and target field embeddings and a translation that need not preserve a fixed k-structure.
lem-sfb-scheme-pullback-point-images vs lem-a1-space-fibre-product-point: the existing statement concerns common-field point lifts over algebraic spaces, not the range of the induced morphism between two specified scheme fibre products. It has no assertion lifting a prescribed point of the target fibre product with two projections in given images; that is range_map here.

lem-sfb-scheme-pullback-point-images vs lem-sfb-field-groupoid-open-image-closed: the new Mathlib leaf gives general scheme fibre-product image formulas and contains no groupoid or open-image closedness assertion; 04Q6 is recorded as its use site, not as an equivalent statement.

## Unfinished work

None for this one-level split. The three new unsplit supporting lemmas intentionally remain statement-only stage-1 queue items. The fourth new node is a Mathlib leaf.
