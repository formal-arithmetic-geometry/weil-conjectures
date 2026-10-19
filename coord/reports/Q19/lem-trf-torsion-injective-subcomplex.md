# Split report: lem-trf-torsion-injective-subcomplex

## Files written

- dag/nodes/sec-trace-formula/lem-trf-torsion-injective-subcomplex.json: item, statement, split; no Mathlib match. Its original statement and statement dependencies are unchanged.
- dag/nodes/sec-trace-formula/lem-trf-injective-abelian-sheaf-divisible.json: new statement-only node; no Mathlib match; existing project declaration found and recorded for attachment.
- citations.json: verbatim statement excerpts for every node cited by every numbered proof step.

One new node; zero Mathlib leaves. No unit or chapter file is changed.

## Attachments

CategoryTheory.Sheaf.epi_nsmul_id_of_injective belongs to lem-trf-injective-abelian-sheaf-divisible, WeilConjectures/CategoryTheory/Sites/SheafCohomologyTorsion.lean:97-128.

I read the declaration and its proof in the read-only slopmaster2 source. The declaration concludes exactly that multiplication by a nonzero natural number on an injective abelian sheaf is epic. The site's sheafification and universe assumptions are available for the small sites and sufficiently large coefficient universe in the node. The archived local/sorry_map_slopmaster2_7d675a26.jsonl.gz entry has s=false and ts=false, with the same module and declaration (its archived start line is 95, while the checkout starts the declaration at 97). The node records the declaration, with state left to the maintainer's audit tool; it does not claim a new proof. I did not attach the item: searches by its exact tag/id and by torsion, injectives, and quasi-isomorphisms find only divisibility and acyclicity declarations, not the full comparison of complexes.

## WANTED

None. All mathematical sources used are present locally.

## Corrections and choices

The item had no proof and needed no statement correction. It correctly allows unbounded complexes and annihilators that vary with the section and cover member. No STATEMENT-DISPUTED arises.

I read Stacks sites-cohomology.tex, Tag 0DD7, label lemma-torsion, especially lines 4225-4252. Its first paragraph proves divisibility; the next paragraph proves this item using rationalization and its cohomology long exact sequence. The delivered argument is marked proof_origin.by=agent: it expands the same divisibility mechanism directly on local cycles and primitives, instead of introducing rationalization, tensor-flatness, or long-exact-sequence lemmas. This is a choice below the unit's route, not a replacement of its normal-cone specialization route. I also read the main-20261015 sk-i-curve-zero lemma-trf-local-term-locality proof and the unit/chapter records. This helper continues to serve the inherited Orgogozo/0DE5/0DD7 ancestry, with no change of coefficient categories or geometric hypotheses.

Searches of the entire DAG by 0DD7, divisible injectives, torsion subsheaves, and the exact project declaration find no existing divisibility node. The derived reduction lemma lem-sfb-divisible-extension-derived-reduction assumes a divisible sheaf and concerns coefficient reduction; it does not prove injectives divisible. lem-sc-torsion-acyclic-envelope constructs an acyclic envelope on a scheme's etale site; its statement does not supply divisibility on an arbitrary site. Neither is used. Blueprint searches for 'divisible injective', 'injective abelian sheaves are divisible', 'multiplication injective sheaf', 'torsion subcomplex', and 'torsion cohomology injective' found no matching blueprint node. Existing site-local lifting and kernel nodes are reused.

All Mathlib searches were made through msearch.py and are in searches.jsonl. I read the hits, tried a second semantic formulation, and repeated the invalid Loogle query (unknown identifier Epi) with a valid quoted-substring query. Mathlib's AddCommGrpCat.injective_of_divisible, read in Algebra/Category/Grp/Injective.lean:54-57, proves the reverse implication for groups, not the desired sheaf statement. Other hits give cancellation, Grothendieck-category instances, unrelated epimorphisms, or generic injective resolutions and quasi-isomorphisms. The item retains its inherited search records and adds actual searches of this run. The new helper contains only searches actually run in this sandbox.

## Not duplicates

lem-trf-injective-abelian-sheaf-divisible vs lem-trf-torsion-injective-subcomplex: the new node concerns one injective sheaf and the epimorphism n times identity; the item concerns an entire complex, local torsion cohomology, and a comparison of its cohomology with that of a subcomplex. Both surjectivity and injectivity of that comparison are proved in the item's steps 4 and 5.

lem-trf-injective-abelian-sheaf-divisible vs lem-trf-torsion-sheaf-complex-representative: the existing parent gives a bounded-below torsion-term representative of a derived object. It depends on this item and does not state divisibility. The helper does not assert a representative or a quasi-isomorphism and has no dependency on either the parent or the item.

## Unfinished work

No unfinished argument in the item. The helper is left statement-only because its exact project declaration is already proved; the maintainer can confirm the attachment using the recorded audit evidence. No Lean source was written or compiled, and no live project or launcher was modified.

## Review by Q19

I checked the delivery against B-E with the actual cited statements and the source open. The new helper is self-contained: it introduces the small site, its abelian sheaf category, the injective object and the positive integer. Its source is Tag 0DD7 and label lemma-torsion, first proof paragraph, not a changing section number. It has no proof or proof dependencies, is not a clause of the item, and is not a duplicate of either same-tag node. Its blueprint ancestor and complete inherited via chain come from blueprint_refs.py ancestor. No imported metadata is removed. Every proof dependency is the union of the steps' actual uses. Every cited statement is quoted verbatim in citations.json. No non-elementary step exceeds 2000 characters; the longest is under 900.

Step 1 uses the site/sheaf definition and the cochain-complex definition. Finite common refinements let two local annihilators be multiplied, coverings compose when sections glue, and an additive differential preserves annihilation. This is an explicit elementary calculation, rather than a new torsion-sheaf lemma.

Step 2 uses precisely the new helper's epimorphism conclusion and lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective. I opened the latter's statement: it applies to abelian sheaves on any site and gives covering-family lifts, not merely set-sheaf epimorphisms or lifts on an etale site. Thus the proof requires only local division, which the project's epi declaration really supplies. It does not upgrade an epimorphism to global surjectivity.

Step 3 uses the actual quotient formula for cohomology from def-weil-abstract-derived-category; the general-site epimorphism criterion supplies local cycle representatives and local lifts through the image factorization; lem-weil-pbc-sheafification-exact explicitly gives sectionwise kernels. The site/sheaf definition supplies separatedness. I read the criterion's source, Stacks sites-modules.tex, Tag 03CN, label lemma-abelian-abelian, clauses (2), (4), (5), (6). This validates the use of sheaf quotients without treating cohomology over U as the cohomology of sections over U.

Step 4 uses these same three facts plus local division from step 2. For a cycle z representing h, torsion gives n h=0 only after refinement, and zero class then gives db=nz after further refinement. Division in I^(r-1) gives n b'=b, so z-db' is killed by n and represents h. I checked d(z-db')=0 and n(z-db')=nz-db=0 separately. The site definition justifies composing all covers. This proves local surjectivity, and the cited epi criterion converts it to an epimorphism of cohomology sheaves.

Step 5 again uses local representatives, sectionwise kernels, local division and covering composition, with the same cited nodes. It is essential to use torsion of H^(r-1)(I), not just H^r(I): after z=db and nz=0, nb is a cycle; torsion of its class gives mnb=dc. Division is in I^(r-2) by the positive integer mn. Then b-dc' is killed by mn and has boundary z. This makes the original class zero locally and hence globally. I checked the degree of each primitive and both identities; no boundedness or uniform exponent appears.

Step 6 uses the sheaf equalizer/gluing axiom to turn local existence plus uniqueness into an inverse, then the stated definition of a quasi-isomorphism. This avoids an uncited balanced-category theorem. I verified that no point/stalk conservativity assumption is used, so arbitrary small sites, including sites without enough points, are allowed.

Small cases checked: on a point the argument is the usual divisible-abelian-group calculation; the zero complex and zero terms cause no exception; degree shifts do not change any hypothesis; terms in arbitrarily negative degrees are used only at r-1 and r-2 for each fixed r. Integers n=1 or m=1 remain positive and the formulas still hold. Sections with annihilators varying over an infinite cover are handled member by member and are never assigned a global exponent. On an empty covering the sheaf separation/gluing statements give the same conclusions. These checks exposed no false hypothesis or source error. No SGA source is used.
