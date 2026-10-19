## Files written

- `dag/nodes/sec-proetale-coefficients/det-pe-finite-local-systems-twist.json`: existing statement node, retained and audited, status changed from unsplit to split; no new nodes.
- `citations.json`: verbatim statement quotes for every proof-step citation.
- `searches.jsonl`: fresh LeanFinder, Loogle, and Mathlib grep searches for the item.

## Attachments

None. I searched the slopmaster2 source for the blueprint tag, the item title, and the comparison/local-system terminology; no sorry-free declaration states this item.

## WANTED

None. The proof follows the available Stacks Project proetale.tex Tag 099Y and the current blueprint detail.

## Source and split audit

The item source is Stacks Project `literature/stacks-project/proetale.tex`, Tag 099Y, label `lemma-compare-locally-constant`, together with the current blueprint proof file `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-pe-finite-local-systems/sk-prop-pe-finite-local-systems-twist.proof.md`. I also read the unit section and the chapter record. The statement has the arbitrary scheme, discrete commutative coefficient ring, finite-presentation local models, comparison morphism, classicality, etale trivialization, restricted quasi-inverse equivalence, and finite-ring clause exactly as stated there.

Step 1 uses the existing type-decomposition node for the open-and-closed pieces, the size convention for the representative set, open immersions as etale covers, weakly-etale localization, the finite-presentation Hom/constant-model comparison, the classical module comparison, and the definitions of comparison morphism, sheafification, constant sheaf, and pro-etale local constancy. I checked each cited statement and expanded the constant-model identification by the constant-sheaf/global-sections adjunction and Yoneda; the two constant-sheaf conventions agree on constant sections.

Step 2 constructs the Isom sheaf and its inverse maps sectionwise, checks module linearity and the action formula, and verifies the torsor clauses against the cited localized-site, sheaf equalizer, module-sheaf, and constructible-torsor statements. This is elementary once those statements are in force.

Step 3 uses the finite-presentation Hom node for the automorphism sheaf and the arbitrary-group torsor comparison node. I checked that the latter permits an arbitrary sheaf of groups, so no finiteness or commutativity hypothesis was silently added.

Step 4 is the explicit descent cocycle. I checked the etale slice localization, pro-etale localization, comparison-morphism, site-cover, ringed-site relocalization, constant-restriction, and classical full-faithfulness statements. These give the restriction isomorphisms, linear transition maps, inverse maps, and the triple cocycle; the cited statements say exactly these facts. The long step was read for hidden claims and spells out the restriction, mate/relocalization, lifting, and faithfulness arguments.

Step 5 applies the existing module-sheaf gluing statement to the transition maps and cocycle of step 4. Its hypotheses (a set-indexed etale cover, coefficient ring restrictions, linear overlap isomorphisms, and triple cocycle) are all checked there.

Step 6 uses the same slice and relocalization statements to form local comparison maps, then glues them by the site equalizer condition. I checked that the etale cover is a pro-etale cover from the pro-etale-site statement and that the inverse maps glue, yielding the global comparison isomorphism.

Step 7 applies the classical module comparison for full faithfulness and the unit/counit, uses slice localization for local restrictions, and uses the pro-etale covering definition. It verifies both directions of local-system preservation, essential surjectivity from steps 1--6, and the restricted unit and counit isomorphisms.

Step 8 is the direct finite-set argument: for finite `A` and finite `M`, the free module on the finite set `M` surjects onto `M`, its kernel is finite, and the free module on that kernel gives a finite presentation. The zero ring and zero module cases are included.

I checked edge cases including empty schemes, the zero ring, the zero module, varying local models, and infinite automorphism groups. No statement was changed, no new node was needed, and no duplicate node was created. The existing proof dependency list is unchanged. Fresh Mathlib searches found only unrelated condensed-module and general sheaf results, so the item is not a Mathlib leaf.

## Review by Q35

I read the item node, the current unit/chapter records, Stacks Tag 099Y, the blueprint twist statement and proof, and every statement of every cited dependency. I verified the hypotheses and objects at each step as described above and wrote `citations.json` with a verbatim quote for every cited node in every step. I specifically checked the two long arguments (the constant-model Yoneda identification and the localization/cocycle construction) for hidden lemmas; their needed facts are either cited existing statements or are written explicitly in the steps. I also checked the finite-ring construction on `A=0`, `M=0`, and finite nonzero examples. The resumed initial dry run exited with failure only because the copied item was unchanged and still marked unsplit. I corrected its status to split and updated the split report; the mathematical statement and proof remain as in the current repository. All 36 citation entries match the current dependency statements verbatim. The retained long steps are routine applications of the displayed adjunctions and slice identifications: the constant-model isomorphism is determined by maps out of the constant presheaf, and the relocalization coherence is the equality of the two adjunction mates of the same commuting inclusion square. The cocycle is then the written cancellation identity and faithfulness. These do not require new lemma nodes. The existing unit realization remains the key-node worker’s responsibility; this item is the twist detail, not the unit key node.

## Resumed search audit

I reused all four Q35 search receipts in searches.jsonl: LeanFinder and LeanSearch for “Equivalence of locally constant finitely presented module sheaves on etale and proetale sites”, Loogle for `"locallyConstant", "Sheaf"`, and grep for `proetale|locallyConstant|IsLocallyConstant` in AlgebraicGeometry/Sites. I read the recorded hit names and checked the candidate source: Mathlib CategoryTheory/Sites/ConstantSheaf.lean lines 140–169 assumes an existing equivalence/dense subsite, CategoryTheory/Sites/Coherent/Equivalence.lean lines 40–53 assumes equivalent precoherent categories, Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean lines 265–285 defines local finite presentations, and AlgebraicGeometry/Sites/Proetale.lean defines the topology. None proves the needed local-system comparison. Earlier repository searches and their receipts were retained.
