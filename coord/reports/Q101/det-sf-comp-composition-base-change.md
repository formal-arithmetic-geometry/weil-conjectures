# Q101 — det-sf-comp-composition-base-change

## Files written
- dag/nodes/sec-six-functors-basics/det-sf-comp-composition-base-change.json: audited split, eight proof steps; not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-derived-composition-adjunction-normalization.json: statement only, unsplit; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-base-change-identity-open-restriction.json: statement only, unsplit; no exact Mathlib match.
- citations.json: one verbatim statement excerpt for every step/node citation.

## Attachments
No attachment for the item itself. The slopmaster2 search found no declaration for its blueprint tag. The nearby Etale/Derived/Package.lean baseChangeLowerShriek and the open-immersion base-change file concern etale fixed-ring bounded-below functors, not all three clauses for ordinary unbounded condensed module objects on Loc(Dctf). The upstream master is reference material only. No Lean files or compiler commands were used.

CategoryTheory.Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv belongs to lem-sfb-derived-composition-adjunction-normalization (conjugacy clause), WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/CompConjugate.lean:46. CategoryTheory.Functor.rightDerivedFunctorCompIso' (Comp.lean:233) gives the comparison, and CategoryTheory.Adjunction.preservesKInjectiveComplexes (Comp.lean:95) supplies the exact-adjoint instance. I read all three declarations. The archived 7d675a26 sorry map marks the conjugacy theorem s=false, ts=false; the composition construction and K-injective preservation are likewise sorry-free in the saved maps. The canonical K-injective representative equation follows by evaluating the defining composite right-derived unit and its uniqueness equation on I, where both resolution units are invertible. This is an attachment candidate for the full node using these declarations and definition unfolding; the node remains statement-only, with declaration names seeded in lean_audit.slopmaster2.decls and the full references in lean_candidates; its closed classification is left to the maintainer's tool. No new proof or Lean file is supplied.

## WANTED
None. All source material used is present locally.

## What was wrong
The sandbox was an unchanged copy of the repository item, with its previous proof and inherited Mathlib records but no report or citations. I retained that argument and its historical statement correction, citations and searches. The current statement already restores the standing scheme setting and does not change in this delivery. The old six-step proof contains substantive derived normalization and open-mate restriction arguments inside its long steps 3 and 5. Those are independent claims with their own hypotheses, and are now the two new statement-only nodes. The remaining proof still performs the actual dense-refinement comparison and cancellation, rather than replacing a clause by a new node.

The recorded unit sk-thm-sf-comp-composition is the old master sec-smooth-purity unit, while this node and its current blueprint lie in sec-six-functors-basics. This maintainer-owned metadata is retained; no unit route was replaced and no unit file edited. Existing accepted tool_uses is retained; split_report.tool_uses keeps the requests actually used.

The earlier density pitfall remains repaired: a dense open need not stay dense under base change (D(t) in A^1 pulled back to the origin is empty). After base change, take a new common dense refinement W of c1', c2', d'. Uniqueness from dense W gives h_a' k = k_a. No interchange is applied with nondense D' as its source.

## What could not be finished
Nothing required for a stage-1 split. The two new nodes deliberately have no proofs or proof dependencies, as required for one-level splitting. The open-restriction lemma remains a future DAG item; the composition lemma has the project attachment candidate recorded above.

## Review by Q101
I read the current main-20261015 item statement and proof, the chapter record, the unit record and current blueprint section, and all statements cited by the item. I checked delivery-errors B through E against the actual files. The item has no exact project attachment or Mathlib specialization: logged searches return underived Scheme.Modules restriction/pushforward or generic derived-adjunction machinery. I read Mathlib's Derived/Adjunction.lean and PushforwardContinuous.lean and the Scheme.Modules composition statements; these Mathlib declarations do not identify the specified K-injective derived composition with its adjunction conjugate and do not prove the pro-etale condensed-module mate identity on the isomorphism locus. A later broader project-source search did find the CompConjugate theorem recorded above; the earlier narrower negative project search was incomplete. Invalid Loogle attempts are recorded as invalid, not evidence of absence; corrected name queries were also run. The inherited Mathlib records are preserved as history, not claimed as searches run by me. Searches from this attempt are recorded exactly from searches.jsonl, including the earlier interrupted attempt's results.

For the new composition node I read Stacks derived.tex Tag 09T5 (lemma-derived-adjoint-functors) and sites-cohomology.tex Tag 0D6E (lemma-derived-pushforward-composition), including the adjacent adjunction proof. The extra assertion is the representative normalization and preservation of the specified adjunction structures. One proves it by the Hom bijections on K-injective representatives: right adjoints to exact functors preserve K-injectives, and the composite Hom bijection is exactly the underived composite in each degree, modulo homotopy. This is a proof plan in this report only. The new node's statement includes exactness, additivity, Grothendieck categories, and the conjugate direction, so no arbitrary right adjoint is silently derived or assumed exact. Identity adjunctions give identity; zero categories give the unique zero comparison. Changing the chosen underived adjunction changes both conjugate maps together, so no assertion of choice-independent arbitrary units is made.

For the new open-restriction node I read sites-cohomology.tex Tags 0D6G (lemma-restrict-direct-image-open), 08FI (lemma-restrict-K-injective-to-open) and remark-base-change, and proetale.tex Tag 09AH (lemma-ses-associated-to-open). On the restricted sites, the vertical maps are identities, not merely abstract equivalences; the restriction section formulas pin down r_h and r_h'. Restriction preserves K-injectives because it is right adjoint to exact extension by zero. Restricting the unit/square/counit formula therefore yields identity units and counits and the identity square comparison. That proves the desired identity, naturally, for every unbounded K. The node needs neither properness nor density; it does require that the inverse image of U be precisely U and h restrict to its identity. With U empty it asserts the unique map in the zero derived category; with h identity it is the triangle identity. With v identity it reduces to the identity mate. The coefficient system is unchanged across all four schemes, with the canonical Cartesian coefficient isomorphisms, and the category is never replaced by a completed category.

Step 1 uses compactification-base-change only to assert the pulled-back factorization is again a compactification. The open adjunction, module pull/push adjunction and composite-adjunction statement give the two right adjoints. Site localization and the explicit direct-image and module-action definitions identify their values on the same fiber product. This calculation is elementary and is left as a step, not a lemma node.

Step 2 uses the conjugate-iso unit equation, whose statement supplies the unique unit-compatible left-adjoint isomorphism. The exactness of extension by zero is explicit in its definition node, and module pullback exactness is explicit in Cartesian coefficients. The derived-category exact-functor clause supplies termwise descent; the ringed open-closed statement supplies j^*j_! = id. Its ringed-site formulation applies through the internal-module equivalence, which explicitly preserves section groups. The open restriction of the common-right-adjoint map is identity, so the cited unit equation fixes the normalization.

Step 3 uses the pullback node for Dctf, sums and Loc preservation, the open localizing-image node for j_!, and coherence-single for the target Loc categories of both compactifications. Finite proper-base-change clause (2), integral clause (3), and rational clause (3) give invertibility on Dctf, with Dctf contained in Dbc. The standing field has characteristic different from ell; all compactification schemes and their fiber products remain separated finite-type k-schemes. The integral argument thus also applies to p'. Z_ell and Q_ell are E=Q_ell cases. The extension node states precisely that the same unit/square/counit mate, invertible on Dctf, is invertible on its ordinary localizing closure. Applying it to j_!K and composing O_c gives clause (2).

Step 4 uses module-derived-pushpull for the adjunctions, Cartesian coefficients for exact pullback, and adjunction-mate for the actual transformation. The corrected module-upper-star-comp statement specifies the conjugate direction; the new normalization lemma identifies its derived conjugate with the K-injective composition comparison. The ringed-topoi composition node gives that comparison on arbitrary ring sheaves and the internal-module equivalence transfers the same sheaves and actions. The mate-pasting statement explicitly supplies pasting along adjunctions and transport by conjugates. Its equation has source b^*Ra_*Rb_* and target Ra'_*Rb'_*b_2^*; no equality of unnamed isomorphisms is being substituted.

Step 5 uses common-dense-refinement's finite-family clause, not its proof, and refinement-morphisms (3) for uniqueness of maps from dense W. Both base schemes are qcqs; every open in a compactification is quasi-compact. The interchange statement with p=id gives e_h uniquely normalized on the open, and its (3) gives invertibility on Loc. Coherence-cocycle explicitly says the comparisons are obtained through any common dense refinement. Thus the rho formula is its stated comparison. All e_h sources are dense, including when their targets are not.

Step 6 uses pullback preservation to put u^*K in Loc. The new open-restriction lemma applies since a refinement is identity on the inverse image of the target open. Interchange (2) gives open normalization of each e and uniqueness for the two maps after O_a; its dense source is W. The equality L_a=M_a is the item's actual compatibility argument, not asserted by the new lemma. Step 7 is naturality plus the stated mate-pasting equality from step 4: precomposing B_p and collecting the proper factors yields B_q, and the remaining open factors are O_d followed by e_k. Step 8 cancels the invertible rho maps and uses exactly the cocycle's common-refinement description. I checked the source and target v^*F_c -> F_W u^* at every point.

The original long steps have been audited for hidden lemmas, not just divided to avoid a length check. The two independent subclaims were extracted; the residual sectionwise right-adjoint calculation and the final naturality/cancellation are routine applications of the cited definitions. Every revised step is under 2000 characters. Neither new statement is a clause of the item: one is generic derived-adjunction calculus, the other concerns any h with an identity open locus and asserts no global base-change isomorphism. No SGA source is used. The proof follows the blueprint compactification route and retains all historical correction fields and import flags.

On resumption I compared the saved item with the current repository: only proof, proof_deps, status, split_report and Mathlib-search fields differ; the statement, its historical correction, import flags and blueprint metadata remain unchanged. I reran no recorded Mathlib query because the statements and search questions are unchanged, and read all saved search results. I checked all 37 citation entries against the current statements, read the four cited Stacks lemmas and the base-change construction, and checked the exact-adjoint and open-identity edge cases again. A new same-tag node, lem-pur-completed-coefficient-pushforward-comparison, appeared since the saved report; I read it and added the distinction below. Its completed-coefficient and strict-tower comparisons neither supply nor subsume the generic specified-adjunction normalization. The required dry run is being polled through its original session.

On this resumption I again read the current chapter and unit records, main-20261015 statement and proof, Stacks 09T5, 0D6E, 0D6G and 08FI, and all current statements cited by the eight steps. All 37 verbatim citation records still match; the proof and search questions are unchanged. The project-wide blueprint-tag search has no exact attachment. I inspected the nearby generic right-derived-composition construction and the etale adjunction-comparison theorem: the generic construction supplies composition, and the etale theorem does not cover the condensed-module open-restriction statement. The subsequent broader search found the generic conjugacy theorem in CompConjugate.lean; the attachment record above supersedes any earlier negative conclusion about project-source conjugacy. I retained the saved logged searches without rerunning them. The dry run passed, and a refreshed tag search found six additional overlapping-tag nodes. I read each and recorded its specific distinction below. The longest retained step is 1684 characters; it constructs the common dense replacement and applies the cited uniqueness and comparison statements, with no independent hidden claim.

## Not duplicates
lem-sfb-base-change-identity-open-restriction vs lem-sbc-abelian-derived-exchange-plus-compatibility: the existing statement concerns the unbounded abelian exchange restricts to the bounded-below exchange, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs sbc-lem-etale-locality: the existing statement concerns etale locality of the base-change map, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs thm-sf-hom-comparison-constructible: the existing statement concerns internal-hom comparison for finite-tor constructible inputs, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs det-cor-sf-direct-image-ctf-open-tor: the existing statement concerns scalar projection formula and the tor bound for an open immersion, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs sk-lem-proper-unbounded-window-ii: the existing statement concerns proper direct image preserves direct sums, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs lem-sfb-ringed-site-perfect-duality: the existing statement concerns perfect-complex duality on a small ringed site, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs lem-sfb-unbounded-site-comparison: the existing statement concerns unbounded comparison: full faithfulness and sums, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs det-ctf-finite-proper-localizing: the existing statement concerns finite-coefficient proper direct image on the localizing categories, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs lem-weil-pbc-etale-localization-exchange: the existing node concerns bounded-below abelian etale exchange for an etale horizontal base change; the new node concerns unbounded condensed pro-etale module objects, arbitrary horizontal v, and identity after restriction to a vertical isomorphism locus.

lem-sfb-base-change-identity-open-restriction vs lemma-weil-pbc-target-locality: the existing statement concerns target locality, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs lem-weil-pbc-ringed-projection-restriction: the existing node identifies restriction of a projection-formula mate involving tensor products; the new node identifies restriction of an arbitrary Cartesian base-change mate, including nonfinite condensed coefficients, at an identity open locus.

lem-sfb-base-change-identity-open-restriction vs lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation: the existing statement concerns derived morphism sheaves evaluate on weakly contractible pro-etale affines, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs lem-weil-pbc-ringed-localization-rhom-calculus: the existing statement concerns derived internal hom and localization of a bounded localization complex, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs lem-weil-pbc-etale-underived-exchange-restriction: the existing statement concerns underived exchange along an etale morphism is the restriction identification, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs lem-pur-kinjective-restrict-localized: the existing theorem says only that restriction preserves K-injectivity; it asserts no comparison of base-change mates or their unit/square/counit normalization.

lem-sfb-base-change-identity-open-restriction vs lem-exc-closed-support-triangle: the existing statement concerns closed-support triangle before restriction, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs lem-pur-kinjective-restrict-localized-adjunction: the existing theorem supplies the underived localized adjunction and exact extension by zero, not identity of the restricted derived base-change map.

lem-sfb-base-change-identity-open-restriction vs thm-fin-projective-line-constructible: the existing statement concerns constructible coefficients on the projective line, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs new-localized-restriction-extension-exists: the existing existence theorem supplies an exact left adjoint to restriction, not normalization of the derived base-change mate.

lem-sfb-base-change-identity-open-restriction vs lem-amb-relative-torsor-cohomology: the existing statement concerns relative first cohomology and torsors with a specified open section, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs lem-amb-unbounded-compact-support-comparisons: the existing statement concerns unbounded ordinary etale compact-support comparisons, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs lem-pur-support-localization-triangle: the existing statement concerns localization triangle for the exceptional inverse image, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs lem-pur-integral-operations-scalar-extension: the existing statement concerns integral derived operations commute with finite scalar extension, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs lem-dg-etale-injective-finite-cech-rows: the existing statement concerns split finite ordered cech rows for injective etale module sheaves, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs lem-weil-pbc-proper-open-comparison-composition: the existing statement concerns composition of proper-open comparison maps, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-base-change-identity-open-restriction vs thm-dg-finite-type-constructibility: the existing statement concerns bounded constructibility of every finite-type direct image, not the specified ordinary unbounded pro-etale condensed-module base-change mate restricted to the vertical identity locus.

lem-sfb-derived-composition-adjunction-normalization vs det-prop-integral-criterion-constant-coefficients: the existing statement concerns constant versus completed integral coefficients, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs sbc-thm-adic-smooth-base-change: the existing statement concerns adic smooth base change, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-sbc-integral-test-pushforward-arrow: the existing statement concerns integral pushforward identifies the two test-base comparison arrows, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-coef-derived-system-evaluation-calculus: the existing statement concerns coherent derived reduction, limit adjunction and fiberwise evaluation, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs prop-coef-integral-dualizing: the existing statement concerns the integral dualizing object and its adjunction, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs sk-lem-sf-kunneth-star: the existing statement concerns ordinary künneth with an identity factor, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-coef-dg-derived-quillen-calculus: the existing statement concerns enhanced derived adjunction and monoidal quillen calculus, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-coef-dg-model-mapping-comparison: the existing statement concerns mapping-complex presentation of an enriched model localization, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-sf-constructible-exceptional-adjunction-coefficients: the existing statement concerns constructible exceptional adjunction and its coefficient comparisons without an ambient datum, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-trf-trace-map-from-external-duality: the existing statement concerns trace morphism from external duality, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-trf-finite-horizontal-shriek-mate: the existing statement concerns compact-support exchange as a mate along finite horizontal arrows, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-trf-weil-shriek-iterates: the existing statement concerns iterates of the weil $!$-pushforward, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-pc-derived-adjunction-target-colimit: the existing statement concerns target hom is the product colimit of transposed numerators, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs def-pc-essentially-constant-ind-diagram: the existing statement concerns essentially constant filtered ind-diagram, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs def-pc-essentially-constant-pro-diagram: the existing statement concerns essentially constant cofiltered pro-diagram, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-pc-derived-adjoint-functors: the existing theorem gives existence of a single derived adjunction, not compatibility of derived conjugate composition with the representative normalization.

lem-sfb-derived-composition-adjunction-normalization vs lem-pc-derived-base-change-unit-compatibility: the existing statement concerns derived mate compatibility with the right-derived unit, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs def-pc-derived-adjunction-hom-diagram: the existing statement concerns product diagram of fraction numerators, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-sc-sheaf-algebra-derived-hom-adjunction-map: the existing statement concerns derived scalar restriction mapderivedcategory adjunction, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-pc-derived-adjunction-source-colimit: the existing statement concerns source hom is the product colimit of numerators, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-sc-derived-open-shriek-derived-adjunction: the existing statement concerns derived extension-by-zero and restriction adjunction, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs new-everywhere-defined-derived-functors: the existing statement concerns everywhere-defined derived functors, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-pc-pre-derived-adjoint-functors-general: the existing statement concerns pre-derived adjunction from essentially constant derived systems, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-pc-derived-adjunction-normalization-unique: the existing theorem proves uniqueness conditional on a representative Hom equation; the new theorem proves that equation for composition and identifies the K-injective representative.

lem-sfb-derived-composition-adjunction-normalization vs lem-pc-ringed-spaces-derived-adjoint: the existing statement concerns derived pullback is left adjoint to derived direct image, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-sc-sheaf-algebra-derived-hom-adjunction: the existing statement concerns the constructed algebra-valued derived hom adjunction, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs new-derived-adjunction-compatibility: the existing statement concerns compatibility of the derived adjunction, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-pc-ringed-spaces-derived-pullback-composition: the existing statement concerns composition of derived pullbacks, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-pc-original-counit-adjunction-transport: the existing statement concerns original-counit transport of the normalized scheme pullback adjunction, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs det-sf-comp-coherence-refinement: the existing statement concerns the refinement map on the localizing category, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs det-prop-p1-adjunction-rational-triangle: the existing statement concerns triangle identities for the rational projective line, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs det-thm-sf-ctf-stability-direct-images: the existing statement concerns pullback, tensor product and direct images on $\dctf$ at all coefficient stages, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs det-sf-comp-coherence-cocycle: the existing statement concerns independence of the compactification and the cocycle condition, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs det-prop-int-brown-construction: the existing statement concerns the integral compactly supported direct image on localizing categories, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-sfb-divisible-extension-derived-reduction: the existing statement concerns derived reduction of an extension by a divisible sheaf, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-sfb-quasifinite-compact-support-exact: the existing statement concerns quasi-finite compact support is exact and agrees with compactifications, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs det-proper-heart-bound-torsion: the existing statement concerns the torsion bound over a weakly contractible base, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs det-sf-mate-open-restriction: the existing statement concerns open immersions and open restriction for $f^!$, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs det-thm-restriction-local: the existing statement concerns local factorization of $f^!$ on an affine chart, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs def-sfb-dc-open-lower-shriek-adjunction: the existing statement concerns the adjunction $j_!\dashv lj^*$ on $d_{\mathrm{cons}}$, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-weil-pbc-ringed-topoi-derived-pushforward-composition: the existing statement gives ringed-topoi composition and its K-injective representative, but does not state compatibility with the specified derived adjunctions; the new node works for arbitrary exact additive left adjoints and identifies both units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-weil-pbc-etale-shriek-qcqs-composition: the existing statement concerns composition of qcqs etale compact-support candidates, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lemma-weil-pbc-frobenius-tower-compatibility: the existing statement concerns frobenius compatibility with tower transitions, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-weil-pbc-ring-sheaf-change-adjunction: the existing statement concerns derived adjunctions under compatible changes of ring sheaves, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs def-weil-pbc-composite-adjunction: the existing statement concerns composite of two adjunctions; the identity adjunction, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-weil-pbc-exchange-identity-pasting: the existing statement concerns identity and pasting equations for exchange, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs def-weil-pbc-derived-direct-image-composition: the existing definition chooses conjugate composition on bounded-below abelian etale categories; the new theorem identifies it with the K-injective comparison for arbitrary exact additive adjoints on unbounded categories.

lem-sfb-derived-composition-adjunction-normalization vs prop-weil-pbc-derived-inverse-image-adjunction: the existing statement concerns derived adjunction of inverse and direct image on d^+, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs def-weil-pbc-adjunction-conjugate: the existing definition concerns conjugation in categories and does not assert any derived-functor normalization.

lem-sfb-derived-composition-adjunction-normalization vs lem-weil-pbc-frobenius-exchange-restriction: the existing statement concerns finite-level exchange is the restricted ambient exchange, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-weil-pbc-etale-shriek-compactification-independence: the existing statement concerns compactification independence on the qcqs etale site, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs thm-weil-pbc-site-comparison: the existing statement concerns bounded-below site comparison, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs def-weil-pbc-derived-exchange: the existing statement concerns derived exchange map, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-fin-finite-boundary-comparison: the existing statement concerns a proper direct image detects a comparison off a finite boundary, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-kun-unbounded-exchange-agrees: the existing statement concerns the unbounded exchange extends the bounded exchange, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-pur-coefficient-evaluation-derived-left-adjoint: the existing statement concerns derived extension from one level of a varying-coefficient system, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-pur-sheaf-ring-derived-coefficient-adjunction: the existing statement concerns derived change of rings along a map of ring sheaves is left adjoint to restriction of scalars, with normalized unit and transposes, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-weil-ringed-tower-pushforward-limit-comparison: the existing statement concerns derived pushforward commutes canonically with strict tower inverse limit, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs thm-asd-smooth-tensor: the existing statement concerns smooth cohomological duality without a chosen orientation, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-sf-integral-direct-image-constructible: the existing statement concerns the integral derived direct image of a constructible complex along a finite-type morphism is constructible, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-kun-kunneth-map-agrees: the existing statement concerns compatibility of the kunneth map with leray, proper base change and the projection formula, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-kun-module-abelian-kinjective-direct-image-acyclic: the existing statement concerns abelian direct-image acyclicity of a module k-injective complex, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-pur-support-site-comparison: the existing statement concerns etale-proetale comparison for supported sections and their exterior products, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-sf-compact-support-restriction-of-scalars: the existing statement concerns finite-level compact-support direct image commutes with restriction of scalars, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-amb-etale-compact-comparisons: the existing statement concerns the etale compact-support comparisons, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-pur-compact-support-integral-coefficient-comparison: the existing statement concerns integral compact support under finite free coefficient extension, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-weil-derived-direct-image-composition: the existing statement concerns composition of derived direct images, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-kun-bc-kunneth-compat: the existing statement concerns cohomology of the base change map through the kunneth identification, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-pur-system-level-left-extension: the existing statement concerns derived left extension from coefficient levels, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-kun-etale-module-abelian-ringed-presentation: the existing statement concerns simultaneous ringed presentations of coefficient forgetting and abelian etale direct image, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-amb-unbounded-compact-support-comparisons: the existing statement concerns unbounded ordinary etale compact-support comparisons, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-pur-retracted-support-localization-comparison: the existing statement concerns localization and boundary comparison for a closed section with a retraction, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-kun-0f14b: the existing statement concerns kunneth formula, one proper factor, $\kunzn$-coefficients, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs det-sp-integral-direct-image-tower: the existing statement concerns tower description of the integral compactly supported direct image, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs def-weil-derived-direct-image: the existing statement concerns derived direct image, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-sp-proper-open-tower-comparison: the existing statement concerns open-adjunction normalization of proper/open interchange on strict coefficient towers, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-kun-0f14a: the existing statement concerns kunneth formula, one proper factor, integer coefficients, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-cbc-strict-tower-proper-open-calculus: the existing statement concerns normalized proper/open calculus on strict pro-etale towers, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-weil-pbc-proper-open-comparison-composition: the existing statement concerns composition of proper-open comparison maps, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-weil-derived-scalar-extension-restriction-adjunction: the existing statement concerns derived reduction modulo varpi^n is left adjoint to restriction of scalars, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-sp-ringed-topos-binary-descent: the existing statement concerns binary derived open descent for modules on a ringed topos, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-pur-coefficient-system-derived-comparison: the existing statement concerns derived direct image and evaluation of coefficient systems, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-weil-proetale-direct-image-restriction-of-scalars: the existing statement concerns derived pro-etale direct image commutes with restriction of scalars, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-kun-unbounded-abelian-exchange-comparison: the existing statement concerns unbounded coefficient forgetting identifies canonical etale exchange, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-fin-finite-boundary-reconstruction: the existing statement concerns recovering constructibility at a finite boundary, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-weil-compact-support-reduction-tower-functor: the existing statement concerns coherent compact-support reduction tower functor, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-pur-ordinary-kunneth-finite-ring: the existing statement concerns ordinary kunneth at a finite coefficient ring, rather than the K-injective comparison for composition of arbitrary exact additive left-adjoint functors with prescribed conjugate units and counits.

lem-sfb-derived-composition-adjunction-normalization vs lem-kun-derived-adjoint-square-comparison: the existing statement transports an adjunct-compatible square through exact horizontal functors V,W and assumes a right-derived property for D(W)RR; here the outer right functor R_a need not be exact, and the issue is composition of two adjunctions rather than such a square.

lem-sfb-derived-composition-adjunction-normalization vs lem-pur-completed-coefficient-pushforward-comparison: the existing node compares completed, constant and finite quotient coefficient pushforwards, including strict reduction towers; the new node identifies the K-injective composition map for arbitrary exact additive left adjoints with the conjugate of their specified composite adjunction, with no coefficient tower or completion.

lem-sfb-derived-composition-adjunction-normalization vs det-thm-sf-pf-adic-open: the existing theorem gives integral completeness, finite reduction and constructibility for an open direct image; it does not compare derived composite adjunctions or their K-injective representative normalization.

lem-sfb-derived-composition-adjunction-normalization vs det-lem-int-ext-bound: the existing theorem gives Ext-vanishing bounds for constructible integral sheaves, not composition or conjugation of derived adjunctions.

lem-sfb-derived-composition-adjunction-normalization vs det-uniform-constructible-ext-torsion: the existing theorem gives finite-coefficient local-cohomology amplitude and cohomology vanishing bounds, not a derived composition comparison.

lem-sfb-derived-composition-adjunction-normalization vs lem-weil-pbc-derived-adjunction-shift: the existing theorem identifies compatibility with integer shifts for one ringed-topos derived adjunction; the new node identifies composition across three arbitrary Grothendieck abelian categories and its K-injective representative.

lem-sfb-derived-composition-adjunction-normalization vs fix-prop-adjunctions: the existing statement is formal in specified comparisons on bounded constructible coefficient categories, with completed integral pullback. It does not identify the ordinary unbounded K-injective composition comparison with the conjugate of a specified underived isomorphism.

lem-sfb-derived-composition-adjunction-normalization vs lem-sp-direct-image-change-ring-transpose: the existing theorem identifies a finite scalar-extension exchange transpose with a projection morphism for a proper map; the new node concerns composition of arbitrary exact additive left adjoints and normalization of their derived conjugates.

lem-sfb-derived-composition-adjunction-normalization vs lem-pur-comparison-unit-injective-model: the existing statement identifies the unit of one bounded-below etale/pro-etale comparison adjunction using an injective resolution for finite discrete coefficients. It does not compare composition of arbitrary exact additive adjunctions on unbounded derived categories, nor identify the conjugate of a specified composite left-adjoint isomorphism with the K-injective composition comparison.
