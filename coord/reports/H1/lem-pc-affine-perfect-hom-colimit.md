Files written:

- `dag/nodes/sec-picard-framework/lem-pc-affine-perfect-hom-colimit.json` — statement, split proof, no new node; Mathlib searches found no exact affine derived-Hom colimit theorem.
- `citations.json` — verbatim citations for all proof-step uses.

Attachments: none.

WANTED: `literature/stacks-project/perfect.tex`, Lemma 36.29.2, Tag 09RE, for the item and its affine calculation (the repository contains the citation metadata but not the extracted TeX source).

No new nodes were needed. The existing `lem-pc-fp-module-map-descent-affine` supplies finite-presented module-map and eventual-equality descent; `lem-sc-affine-projective-complex-derived-hom` supplies the ordinary Hom-complex model; `lem-pc-module-bounded-flat-kflat` supplies K-flatness of the bounded flat target model. The generic exactness clause is taken from `lem-pc-module-filtered-colimits-tensor` as an explicitly declared tool use.

## Review by H1

I checked the item against the imported Tag 09RE affine clause and the statement used by `lem-pc-perfect-descend-morphisms`. Its hypotheses are preserved: the source complex is bounded finite projective, the target is the scalar extension of a K-flat complex, and every stage is obtained by scalar extension along the filtered ring system. Step 1 uses exactly the existing ordinary-Hom derived-category statement for a bounded-above projective source and the existing bounded-flat K-flat statement; it only specializes the one-point ringed-site formulation to modules over each ring.

For Step 2 I read `lem-pc-fp-module-map-descent-affine`: it explicitly gives descent of maps between fixed finitely presented module base changes and eventual equality. Each finite projective term is finitely presented, and boundedness makes the product in each Hom degree finite. The differential-commutation equations are therefore a finite family of the equalities covered by that node, so the degreewise colimit comparison is justified. Step 3 uses the exact-filtered-colimit clause stated in `lem-pc-module-filtered-colimits-tensor`; exactness preserves kernels and images, hence cohomology, giving the claimed H^0 isomorphism.

I checked the small edge cases: a zero source gives zero Hom on every stage and at the colimit; a complex concentrated in one finite projective degree reduces to the finite-presented module-map clause; and a zero differential leaves the same componentwise argument. I corrected the imported bookkeeping error in `created.item` to this item, changed status to `split`, filled the split report, and recorded the off-unit exactness input as `tool_uses`. The mandated Mathlib searches were rerun; LeanSearch was unavailable and is recorded as such.

## Second reading by H1

- Statement: checked against Stacks Tag 09RE, affine clause, and its use in `lem-pc-perfect-descend-morphisms`; corrected the target to a bounded finite-projective complex so the cited derived-Hom and K-flat hypotheses match.
- Step 1: checked `lem-sc-affine-projective-complex-derived-hom` and `lem-pc-module-bounded-flat-kflat`; boundedness and projectivity now supply exactly the stated ordinary Hom and scalar-extension models.
- Step 2: checked `lem-pc-fp-module-map-descent-affine`; finite products, component maps, differential relations, and eventual equality are all covered by its statement.
- Step 3: checked the cycle and boundary representatives against Step 2; the filtered-colimit cohomology argument is written explicitly as an elementary consequence, with no sheaf-colimit theorem misapplied to varying rings.
- New nodes: none; B1-B7 and duplicate/search checks are vacuous for this split, and the existing cited nodes were opened and verified.
- Changed the item hypothesis and Step 1 to match the bounded perfect affine source and its cited nodes.
- Rewrote Step 3 and `citations.json` to remove the inapplicable sheaf exactness citation and retain the finite-presentation equality citation.
- Removed the obsolete filtered-colimit sheaf node from `proof_deps` and `tool_uses`.

