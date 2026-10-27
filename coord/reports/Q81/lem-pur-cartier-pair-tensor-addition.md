# Q81: lem-pur-cartier-pair-tensor-addition

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-cartier-pair-tensor-addition.json: statement node, split into nine steps; no exact Mathlib match.
- citations.json: verbatim statements for every proof-step citation.
- searches.jsonl: actual recorded Mathlib searches for the item. Its pre-existing searches and their results are retained in the node.
- report.md: this review and delivery record. Sandbox-only Python helpers produced the JSON and citations; they are not library or delivery files.

There are zero new nodes and zero new Mathlib leaves.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for Cartier, relative torsor, tensor and Baer terminology. Existing declarations about products of invertible ideals and ordinary torsor extensions do not state all the framed-relative cohomology, supported extension, and connecting-map clauses of this item. No sorry declaration is treated as a completed attachment.

## WANTED

None. The blueprint and the needed Stacks sources are present locally.

## Defects and corrections

The item was unsplit and did not contain a proof. Its statement already correctly repairs the ancestor's claim that a sum of two effective divisors has the two-element frame (f1,f2). The correct local equation is f1 f2. I retained the item's entire statement, rather than changing the coefficients, the relative normalization, or the allowed divisor hypotheses.

The current blueprint ancestor is main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md, clause (b). I read both its statement and proof. The inherited unit attribution sk-prop-a1-kummer differs from that current path; I preserved the maintainer-owned unit and chapter fields. This is a supporting node, not the statement of that unit, so no unit realization file is delivered. The proof keeps the product-Cartier/torsor route and does not introduce an alternative purity theorem or any forbidden SGA source.

The first draft needed an explicit justification that pulling back a short exact extension stays short exact. I added the generic pushout-short-exact theorem applied in the opposite abelian category, rather than treating a definition of extensions as that theorem. I also added the actual injective-resolution morphism lifting theorem to the coefficient comparison step, and the constant-sheaf definition to the integral open adjunction step.

## Unfinished work

None for this one-level stage-1 split. The proof's existing unsplit dependencies remain their own items; no Lean was written or compiled. The relative extension realization is the one explicitly specified in the item and characterized by lem-sp-relative-torsor-extension. The proof checks its behavior on restriction and product from that characterization, without assuming that the ordinary unframed H1 class determines a relative class.

## Not duplicates

No new nodes were created. Whole-DAG statement/title searches and blueprint_refs searches for torsor, Cartier, relative, contracted product and Baer found the existing tools used below. The broader parent lem-pur-divisor-class is not a dependency: it already depends on this item. In particular I did not cite the parent or move its tensor-addition clause into a replacement node.

## Sources read

- Current blueprint lem-pur-divisor-class.md and its .proof.md, clause (b), and the current smooth-purity chapter text; repository chapter and unit records.
- Stacks divisors.tex, Tags 01WT and 01WU, labels definition-sum-effective-Cartier-divisors and lemma-sum-effective-Cartier-divisors. Their local product argument is written out, so it does not need a new elementary node.
- Stacks sites-cohomology.tex, Tag 03AJ, label lemma-torsors-h1: both the free-extension construction and the injective lifting-torsor construction, and the following first-cohomology/extensions paragraph. The relative calculations are agent-written refinements, not attributed verbatim to Stacks.
- Blueprint master lem-sc-line-bundle-torsor.md, including its Tensor products paragraph and the local quotient map.
- Stacks cohomology.tex, Tag 0G78, remark-support-functorial. This remark alone does not prove the item's enlargement-of-support and connecting identities; the proof instead gives their actual cone maps and invokes complex-SES naturality.
- Stacks homology.tex, Tag 010L, lemma-baer-sum and its preceding direct-sum/diagonal/pushout construction; Tag 0117, lemma-long-exact-sequence-cochain and its functoriality assertion.

## Mathlib review

The saved searches include LeanSearch, Loogle, source grep, and two semantic phrasings through LeanFinder. LeanSearch returned additive hom-complex cohomology and projective-resolution Ext equivalences, tensor product operations and unrelated cotangent H1. Loogle returned additive torsor typeclasses, which concern group actions on types. The first LeanFinder phrasing returned CommRing.Pic tensor group-law lemmas and module/presheaf tensor constructions. The second returned ordinary presheaf-of-groups H1 and cocycle equivalence declarations. None of these constructs relative etale torsors with a specified open section or relates the supported integral extension classes required here. The source grep found no relative-torsor, torsor-Baer or Cartier-tensor match. The inherited five searches are kept, including the honestly unavailable LeanSearch entry. No search was invented, and no unavailable service is recorded as no match.

## Review by Q81

I checked delivery-errors B through E against the node, the cited node statements, and the sources above. There are no new nodes whose completeness, duplication, or elementary status could be obscured by a split. Each of the nine steps is below 2000 characters. The first two are elementary local basis arguments and carry their actual calculation; the subsequent steps use substantive existing statements and are marked non-elementary.

Step 1 uses def-nagata-effective-cartier-ideal for the precise local non-zero-divisor condition, and def-pc-divisor-line-bundle for the ideal and dual line bundle. The product cancellation works over every commutative ring. The support equality is an equality of underlying closed sets; it is not an assertion that the product ideal equals the intersection ideal. The multiplication map and its inverse are checked on actual free generators, not on equality of divisor classes.

Step 2 again uses def-pc-divisor-line-bundle and the Hom dual in def-sc-invertible-module. I checked the section f f-dual obtained by transposing the inclusion, so the framed isomorphism uses the canonical section, not its inverse or merely some trivialization. On the complementary open this section is a frame because f is invertible there. These statements follow from the written basis equations.

Step 3 uses the tensor-to-contracted-product clause of lem-sc-line-bundle-torsor, the quotient universal property in def-sc-contracted-product-presentation and the section-preserving isomorphisms of def-amb-torsor-with-section. The first lemma explicitly allows an arbitrary scheme, not just a curve. I checked the invariant relation (g u,g^{-1} v), the local inverse c to [(c,1)], and the image of the specified section. The binary product is extending the product torsor along the group multiplication map, consistent with the definition's structure-group-change formulation.

Step 4 uses lem-weil-pbc-site-sheaves-enough-injectives for the category in which the resolution is chosen, and lem-amb-relative-cocycle-coordinates for the first-row lifting description, the cycle (iCycles(t),-b), and its equivalence with pointed torsor classes. I opened the actual statement, rather than using a general Yoneda/fully-faithful substitute. Addition of lifts gives the lifting torsor of t1+t2 and the sum of the specified lifts; this is an explicit equivariant local isomorphism. Lem-amb-relative-torsor-forget-normalization says that negating the raw class gives the ordinary lifting-torsor normalization. The item specifies precisely this Ext-normalized class. Both classes change by the same global negation, so the addition equation is preserved, with no unsupported sign change.

Step 5 cites def-amb-relative-etale-cohomology for induced maps from commuting restriction squares and lem-amb-relative-cocycle-coordinates for their action on frames. Its differential calculation proves the exact signed map in the statement. Lem-weil-pbc-injective-resolution-lift-exists applies to the same nonnegative injective resolutions and any coefficient morphism. Lem-amb-relative-torsor-class-naturality explicitly covers every commuting restriction square; lem-amb-relative-torsor-cohomology supplies the canonical coefficient naturality for the classifier. Thus no smoothness of the open inclusion or inverse-image argument is being assumed for an enlargement of support.

Step 6 uses lem-weil-pbc-open-closed-short-exact with the integer constant sheaf, not a finite module sheaf, and lem-weil-pbc-extension-by-zero-adjunction with Lambda = Z. Def-weil-pbc-constant-sheaf specifies sheafification of the constant presheaf; evaluation at one is its universal Hom description. Under the actual open counit the section one maps to one. These are exactly the short exact sequence and natural Hom equivalences required by lem-sp-relative-torsor-extension, whose uniqueness statement includes the equivariant map, its fibre over one, and the vanishing of the prescribed section. I checked all those hypotheses, rather than citing that theorem just for its name.

Step 7 uses the same open-closed sequence to obtain q by the cokernel map of the two open extensions. The resulting map sends supported one to supported one. Def-coef-yoneda-extension-data supplies the endpoint convention. Lem-weil-pbc-pushout-short-exact-sequence is stated for any abelian category; in its opposite category its conclusion is exactly the required pullback short exactness. Its use is therefore a genuine specialization of its statement. The map from P to the pullback is written, including why both its coordinates vanish on W. Relative extension uniqueness identifies the resulting pullback class.

Step 8 uses lem-coef-yoneda-baer-existence in degree one in the abelian category of integral etale sheaves; it states the product, diagonal pullback and addition pushout as actual exact extension data. Def-coef-yoneda-extension-data specifies the same Baer operation. The quotient relation used in def-sc-contracted-product-presentation is explicitly killed by the displayed translation equation for lambda. The resulting map to the Baer extension preserves the fibre over one and the chosen zero section. Lem-sp-relative-torsor-extension then identifies its class with beta_Z. This proves the extension equation independently, and proves that the specified relative extension realization carries exactly the addition and restriction of the cohomology equation to the Baer and pullback operations.

Step 9 uses lem-weil-pbc-injective-resolution-ses for an arbitrary short exact sequence in the same sheaf category; its statement explicitly permits degreewise direct sums with inclusion and projection. Section evaluation therefore preserves these chosen splittings on both opens. Lem-weil-pbc-complex-ses-long-exact-naturality applies to the resulting degreewise short exact relative complexes and the three written restriction maps. Its conclusion is precisely the needed connecting-map square in every degree. The lift-and-differentiate calculation in the step verifies why restriction respects that boundary; def-amb-relative-etale-cohomology identifies the relative complexes being used. Coefficient commutation is the coordinate identity in step 5.

I tested empty divisors (local equation a unit), repeated divisors (equation f squared, possibly nonreduced), intersecting Cartier divisors with no proper-intersection assumption, disconnected schemes and opens, zero coefficients, and the empty complementary open. Cancellation and the support union calculation remain valid over rings with nilpotents. Nothing in the lifting, open-closed or degreewise split arguments requires a Noetherian, smooth or quasi-compact scheme. I did not create a stronger statement needing one of those extra hypotheses.

The generic off-unit tools are declared in split_report.tool_uses: the frame/torsor correspondence; enough injectives and injective comparison; the integral open-closed sequence and open adjunction; relative extension uniqueness; Baer-sum existence; the pushout theorem in the opposite abelian category; horseshoe resolutions; and connecting-map naturality. They support the fixed local Cartier/Kummer route and do not replace a step of the purity unit with another theorem. The server review_split check passed before the final citation refinements; the final deliver.py dry run is required below before pushing.
