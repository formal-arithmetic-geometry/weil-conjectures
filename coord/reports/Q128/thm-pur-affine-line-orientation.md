# Stage-1 repair: thm-pur-affine-line-orientation

## Files written

- `dag/nodes/sec-smooth-purity/thm-pur-affine-line-orientation.json`: split, statement and Lean record unchanged. The original first, second and final steps are retained verbatim.
- `dag/nodes/sec-smooth-purity/lem-pur-supported-hom-pullback.json`: one new unsplit statement; no Mathlib match. It states compatibility of the supported-Hom identification with pullback of a closed pair, for ordinary etale complexes and their finite-coefficient pro-etale realizations.
- `citations.json`: verbatim statement excerpts for every citation of all seven steps.

The provisional nodes `lem-pur-affine-line-kummer-fibre-pullback`, `lem-pur-affine-line-closed-pushforward-base-change` and `lem-pur-affine-line-derived-pushforward-comparison` are not delivered. Their retained searches remain in `searches.jsonl`. The first is replaced by existing torsor-H1 functoriality and the explicit coordinate/transition-section calculation. The last two are specializations of the existing finite-exchange theorem, including its derived clause.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item tag, orientation, Kummer pullback and supported restriction found no declaration stating the complete item. `Orientation.lean` concerns uniqueness/base change of an already supplied orientation. `KummerBaseChange.lean` proves formulas for the abstract Kummer interface; `Derived/Supports.lean` constructs the exceptional restriction under supplied adjoint hypotheses. Neither states the new lemma identifying kernel-derived supported-cohomology pullback with pullback of its Hom representative on the two sites. No compiler was run.

## WANTED

None. Milne's PDF and the Stacks source are present and were read.

## What was wrong and what changed

The human returned original step 3 because its 4,466 characters concealed separate non-elementary arguments. The retained sandbox had begun replacing it by three helper nodes but had not completed delivery after a transport interruption. I continued that work, read its recorded searches and ran its dry run first. The dry run returned a duplicate-source check on the pushforward helpers. Reading the existing finite-exchange statement showed that it supplies both the sheaf comparison and its derived version; those helpers were removed instead of defended as new lemmas.

The final replacement consists of steps 3–6: coordinate-torsor pullback and coefficient extension; supported-boundary pullback and its Hom representative; the existing finite-exchange comparison; and the explicit exceptional counit-mate calculation. The new lemma addresses a real missing comparison: `lem-pur-supported-hom` states naturality in F, not in the closed pair. The four replacement steps have 961, 651, 906 and 1,185 characters respectively. Every non-elementary proof step is below 2,000 characters.

The statement, Lean record, blueprint-update fields, chapter and unit are unchanged. Original steps 1, 2 and 4 are retained verbatim as steps 1, 2 and 7. The current blueprint's supported Cartier-boundary naturality and geometric coordinate normalization are realized by the same route as the returned proof. No isomorphism or uniqueness clause is added. No SGA source is used.

## Not duplicates

- lem-pur-supported-hom-pullback vs lem-pur-supported-hom: the latter identifies pro-etale groups and is natural in F; the new statement asserts compatibility under change of scheme and closed subscheme, with an explicit formula for the source exchange.
- lem-pur-supported-hom-pullback vs lem-amb-closed-support-hom: the latter gives an etale derived-Hom/cone identification for a fixed pair; the new statement is the pullback square and its site comparison.
- lem-pur-supported-hom-pullback vs lem-pur-supported-cup-functoriality: the latter supplies supported-group maps, Kummer pullback and products, but does not identify supported pullback with inverse image of the Hom representative through closed-pushforward exchange.
- lem-pur-supported-hom-pullback vs lemma-weil-pbc-finite-exchange: the latter supplies exchange isomorphisms, including derived exchange, not their compatibility with kernel-derived supported cohomology.
- lem-pur-supported-hom-pullback vs lem-asd-ordinary-supported-kummer and lem-amb-cartier-kummer-map: those concern a particular Cartier/Kummer class, not every bounded-below coefficient complex and every supported class.

Before writing the new node I searched the whole DAG for supported Hom, support/pullback and Ext terminology, and the whole blueprint using `blueprint_refs.py search` with “support pullback”, “supported Hom”, “support Hom” and “closed support”. I opened the candidate statements above. The searches for the retained helpers also included Kummer and tags 0959, 04FX and 04C4, and led to reusing existing facts. No blueprint node states the new compatibility formula. `blueprint_refs.py ancestor` gives the item as the new node's ancestor.

## Review by Q128

I read Milne Section 9, Theorem 9.4, Example 9.5, Proposition 9.6 and the Ext proof on pp. 66–67, and Section 16, Theorems 16.1 and 16.7, Example 16.3 and Proposition 16.11. I read the item's current blueprint update and the unit `sk-prop-a1-kummer` and chapter record. Milne identifies supported sections with Hom from the closed constant sheaf via the closed/open short exact sequence. The new lemma formulates pullback compatibility of that identification, with the specified coefficient and site comparisons. It assumes no relative purity. I also read Stacks 0959 (`lemma-finite-pushforward-commutes-with-base-change`) and its stalk proof, 04FX (`lemma-stalk-pushforward-closed-immersion`), and 04C4. The last concerns big-site exactness, so it is not used as a source for a small-site derived comparison. That comparison is stated directly by the existing finite-exchange node.

Step 1: I opened the datum, finite-type dimension, open-complement bound/definition, ambient closed adjoint, constructible-amplitude, finite-Tor, exceptional-inverse-image and finite-twist local-freeness statements. Their hypotheses are precisely the item's finite coefficients, finite-type schemes and invertible ell. The twist is locally free of rank one and constructible; tensoring locally preserves degree zero, verifying Tor amplitude [0,0] before applying the closed bounds. The empty case uses a nonnegative dimension bound. This step is unchanged.

Step 2: the datum supplies the actual Kummer class. Support exactness supplies its boundary. Gysin structure explicitly gives the shifted degree-zero support object and identifies the boundary with the displayed Hom group. The finite-Tor-category definition gives fullness, while A_Y itself has Tor amplitude [0,0]. Thus this is a morphism in precisely D^b_ctf with shift [2] and twist (1). This step is unchanged.

Step 3: the datum supplies the equation, torsor action, contracted-product relation, coefficient morphism and etale/pro-etale identification. I opened `lem-sc-etale-torsor-h1-functoriality`: clause (1) identifies pullback of a torsor with cohomological pullback, and clause (2) identifies contracted product with coefficient extension. The step's equations check that the pulled-back objects are exactly the fibre's specified ones. It uses no tensor product of the units sheaf over Z/m. The retained hypothesis e divides n gives N=n/e>=1, and m is invertible on the geometric fibre.

Step 4: support exactness explicitly states functoriality in pairs, including complexes and finite-torsion pro-etale coefficients. The old supported-Hom statement supplies the representative; the new lemma supplies exactly the additional scheme-pullback square. This corrects the retained repair's inference of scheme naturality merely from naturality in F. Its formula is quoted verbatim in citations.json.

Step 5: I read `lemma-weil-pbc-finite-exchange`, which states both canonical underived exchange and invertibility of derived exchange. The affine chart quotient proves finiteness of the zero section here. The exact module-inverse-image statement gives the constant coefficient identification, exactness and ordinary adjunction, ensuring the comparison is the actual A-module comparison. The ambient closed-adjoint statement applies to every closed immersion on ordinary etale categories. The adjunct-counit identity states exactly the equation m=epsilon composed with s_*pur_s. No etale assertion is applied to arbitrary pro-etale sheaves.

Step 6: functoriality of the canonical exchange gives the pulled-back representative m'. The two counit equations written in the step prove that its adjunct is beta composed with g^*pur_s, using the cited generic adjunct-counit identity and no invertibility of beta. The new lemma identifies its class with the previously computed supported pullback. The fibre adjunction permits Omega/k not finite type. The exceptional-inverse-image definition transports the etale adjoint to the chapter's etale-origin pro-etale category; the new lemma and existing support exactness match the finite-coefficient supported restrictions. There is no assertion of an adjoint on all pro-etale complexes.

Step 7: I read the full rank-one local-calculation statement. It applies to algebraically closed Omega, invertible ell and the same coefficient tensor twist, and explicitly sends the coordinate boundary to 1. It includes the pro-etale formulation. The order of t at zero is one, and no primitive-root choice changes this normalization. This step is unchanged apart from numbering.

For the new node I checked that it introduces all objects and maps, states a proposition rather than a proof sketch, and has no proof or proof dependencies. It is strictly smaller than the item: it says nothing about orientations, Kummer classes or normalization. For its later split, the argument starts from degree-zero evaluation on 1 in Milne's kernel-of-restriction identification. Under the supported-constant exchange, inverse image preserves that evaluation, so the square of kernels commutes. Compare the inverse image of a resolution with a resolution on X' to derive the square; inverse image need not preserve injectives. The closed/open exact sequence yields the same localization pullback. The finite-coefficient site comparisons applied to this diagram give its pro-etale formulation. These resolution-comparison arguments require a node rather than an elementary assertion in the item.

I tested the new statement for identity h (exchange is identity), empty Z (both groups zero), Z=X (ordinary cohomology/Ext pullback), degree zero (evaluation on 1), zero coefficients and zero F, and geometric points whose residue extension is not finite type. None requires a purity isomorphism. The item handles empty Y vacuously. No unprovided smoothness or finiteness of the geometric-point map is used.

I read the retained search results before reusing them and recorded only actual msearch queries. The new node has LeanSearch, LeanFinder with a second phrasing, Loogle and Mathlib grep searches. Loogle found `CategoryTheory.Abelian.Ext.mapExactFunctor`; I read `Mathlib/Algebra/Homology/DerivedCategory/Ext/Map.lean` including its comparison formulas. It gives abstract transport of Ext, not the required identification with supported sections. The grep hits for “supported” concern degrees of complexes. No hit is an exact statement or one-line specialization of the new node.

This repairs the single return in full: the statement and route are preserved; every concealed non-elementary argument is cited to an existing node or the new compatibility node; the counit calculation is explicit; and the length limit is met. B–E were checked against the opened files: no duplicate provisional node remains, no new node restates a clause of the item, the cited statements supply the facts claimed, and no hypothesis or coefficient-category identification is hidden. Only authorized sandbox files were written.

## What could not be finished

Nothing in the stage-1 split. The new lemma is intentionally statement-only, as required for the next level of the DAG.
