# Stage-1 report: lem-per-potential-dual-constructible-preservation

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-potential-dual-constructible-preservation.json: statement node, split into nine steps; Mathlib searches find no matching theorem.
- No new nodes and no new Mathlib leaves. citations.json contains a verbatim statement quotation for each step/node citation. searches.jsonl retains the actual searches and their returned summaries. Temporary source extraction and preparation scripts stay in this sandbox.

## Attachments

None. Searched the named read-only slopmaster2 WeilConjectures source by the blueprint tag, potential-dualizing terminology and constructible-dual terminology. The hits concern dualizing objects over a field or constructible finite-Tor categories, not arbitrary pinned potential complexes on excellent schemes. No declaration supplies the item exactly.

## WANTED

None. The ILO volume is present and was read as text extracted from the supplied PDF.

## Findings and corrections

The statement agrees with ILO XVII Proposition 6.2.3.1, printed pp.295–296: prime-power coefficients, Noetherian excellent scheme with ell invertible, dimension function, given potential complex, all bounded constructible inputs. Its statement and statement dependencies are unchanged.

The initial node had no proof. I supplied the field-coefficient noetherian induction, explicit generic-open construction, local-free computation with a global cohomological interval, closed and open stratum adjunctions, prime-power coefficient filtration, and ordinary truncation induction. This follows the source without invoking its later biduality theorem. In particular I do not cite lem-per-gabber-local-duality-general even though its proof contains related material: that theorem is stronger and sits above the present preservation input.

The existing node lem-per-potential-dual-constructibility states the same assertion as the assigned item, including independence of biduality. This is an existing duplicate, not a new node in this delivery. Maintainer consolidation is appropriate; this worker edits only the assigned item and neither edits nor creates another preservation node. Blueprint searches for potential dual and constructibility and the whole-DAG search found no imported blueprint node giving this general excellent-scheme assertion; same_as remains empty. The ancestor is lem-per-artin-gabber-affine-curve, Step 3, through the existing potential-duality chain. The chapter and unit records are read and unchanged.

## Not duplicates

No new nodes. Existing duplicate: lem-per-potential-dual-constructible-preservation vs lem-per-potential-dual-constructibility: the mathematical statements coincide; the assigned item now contains the actual preservation proof. The broader lem-per-gabber-local-duality-general additionally asserts constructibility of K and evaluation biduality and is not used as a black box.

## Unfinished work

No mathematical part is left out of the split. Subsequent splitting of the existing inputs belongs to their own items. Delivery validation is run with the prescribed server-backed command.

## Review by NL

I read ILO XVII 6.2.1.1, 6.2.2.1–6.2.2.2 and 6.2.3.1 in the supplied volume, including the proof on pp.295–296, and checked the exceptional-pullback hypothesis against XVII 4.1.2 on p.280. No SGA source is cited. There are no new statements requiring separate sources. I opened every one of the 21 existing cited node statements; the quotations are copied into citations.json. The uses below are of their statements, not constructions available only inside their proofs.

Step 1 uses lem-per-potential-dualizing-uniqueness only for its explicit assertion that every given potential complex is bounded constructible. This applies to the actual pinned K under exactly the prime, excellence and dimension-function hypotheses. It supplies a finite interval; neither uniqueness nor finite Tor amplitude is used to deduce biduality.

Step 2 uses def-weil-pbc-constructible-complexes for the lisse and bounded-constructible meanings, lem-sf-ext-sheaf-constructible for constructibility of every Ext cohomology sheaf with a site-perfect first input, and lem-weil-pbc-ringed-internal-hom-exact-restriction for restriction to a trivializing etale slice. I checked the coefficient specialization E=Q_ell and n=1 gives F_ell. The lisse sheaf is locally finite free because the coefficients are a field, so the site-perfect hypothesis is satisfied; this reasoning is not applied to a nonfree Z/ell^r sheaf. The dual on a slice is a finite direct sum of K and therefore has the same interval even if ranks vary. prop-weil-pbc-geometric-stalks-exact and lemma-weil-pbc-geometric-stalk-conservative justify detecting that vanishing globally. This separates constructibility from boundedness and avoids assuming a bounded trivializing-cover rank.

Step 3 uses the finite-stratification definition to write the generic-open argument explicitly, rather than hide a generic-lissity lemma. There are finitely many strata and generic points, and the boundaries removed miss all generic points, so the complement is a proper closed subset. Intersecting the strata with Z gives a constructible stratification there. lem-exc-finite-type-localization-excellent explicitly covers both quotients (finite type) and localizations, so excellence survives on the pieces. lem-weil-pbc-noetherian-open-subscheme-noetherian gives Noetherianity of U; quotient rings give it on Z. The induction ranges over closed subsets, all normalizations and all potential complexes; it needs no finite bound on Krull dimension.

Step 4 uses lem-weil-pbc-closed-immersion-proper for compactifiability of i and lem-per-potential-dualizing-finite-pullback for its actual exceptional inverse image. A closed immersion is separated finite type with the identity-open/proper compactification, its source is excellent Noetherian by step 3, and its residue-field extension has transcendence degree zero, so the dimension function is the restriction. Thus the induction hypothesis applies to i^!K. lem-weil-stratum-ambient-hom states the full internal-Hom adjunction in the ordinary etale category for both bounded and unbounded inputs; substituting the closed stratum gives exactly the comparison used. lem-cbc-open-closed-recollement states exactness of closed direct image. Constructibility of that image is written out from the strata and zero complement using def-weil-pbc-constructible-complexes, so no unquoted preservation theorem is assumed.

Step 5 uses the same internal-adjunction statement for the open stratum, whose exceptional inverse image is ordinary restriction in the theorem's definition. The hypotheses of lem-per-quasi-excellent-etale-direct-image-finiteness are checked, not replaced by finite-type-over-a-field assumptions: both schemes are Noetherian and hence qcqs, the target is excellent and hence quasi-excellent, and ell is invertible. lem-weil-pbc-noetherian-open-subscheme-noetherian ensures quasi-compactness of the relevant inverse images of affine opens; lem-weil-pbc-qc-open-immersion-finite-type supplies finite type, and pqf-lem-lft-fp-locnoeth supplies local finite presentation. With quasi-compactness and quasi-separatedness this is finite presentation. Its finite-field case applies precisely to F_ell, and no nonexistent uniform bound for all nonproper direct images is used.

Step 6 cites the actual triangle in lem-cbc-open-closed-recollement. The ringed internal-Hom restriction theorem also explicitly states contravariant triangulatedness, which is the clause used here and later. prop-constructible-derived-subcategory supplies triangulated closure over a finite ring. The two outside objects are bounded by previous steps; consequently their triangle gives boundedness as well as constructible cohomology for the middle object. This closes, rather than assumes, the induction.

Step 7 uses lem-per-potential-hom-coefficient-restriction with m=1 and n=r for potentiality of K_1. Its statement does not require biduality. lem-per-potential-coinduction supplies precisely the internal restriction–coinduction isomorphism for Q in D^+, not a claim that arbitrary coefficient pullback commutes with Hom. The field-case proof can now be applied to K_1 with all hypotheses unchanged. The definition of bounded constructibility shows forgetting scalars preserves the finite strata, finite stalks and cohomological interval.

Step 8 cites thm-constructible-serre for images and quotients, lem-weil-heart-short-exact-triangles for the filtration triangles, the ringed internal-Hom theorem for their dual triangles, and prop-constructible-derived-subcategory for finite extension closure. The elementary part is the finite induction along ell^r M=0 and the observation that each quotient is an F_ell-sheaf; it is not a new general coefficient-change lemma. No finite Tor assumption on M appears.

Step 9 uses precisely the successive-cohomology truncation triangles stated in lem-weil-pbc-truncation-triangle. The ringed internal-Hom theorem gives their duals and signed shift compatibility, and prop-constructible-derived-subcategory gives closure under the resulting finite extensions. The elementary finite induction starts below the lowest cohomology and ends at the highest, so it never assumes that an unbounded input has a finite Postnikov filtration.

For B1–B10, there are no new-node forms, definitions or unsupported leaves; all actual new searches are recorded unchanged, while inherited searches remain intact. For C1–C8, each non-elementary ingredient is an existing node, quoted verbatim; off-unit generic tools are declared only in split_report.tool_uses, and no broad duality theorem is cited. For D1–D5, nine steps carry the argument and zero new nodes repackage its conclusion. For E1–E7, I checked the field versus prime-power distinction, finite presentation of j, excellence of the pieces, boundedness independent of local rank, the compactification of i, and the fixed coefficient rings in all comparisons. Small cases include X empty, zero M, zero-rank L, Z empty, r=1, nonfree M over Z/ell^2, and a complex concentrated in one nonzero degree. In the nonfree case the filtration is essential: the local finite-free field computation is never applied directly to it. No proof step exceeds 2000 characters or hides an additional comparison. I corrected the generic-open paragraph to remove all strata boundaries explicitly, and exposed both Serre closure and the finite-presentation justifications rather than leaving them implicit in the source's short argument.
