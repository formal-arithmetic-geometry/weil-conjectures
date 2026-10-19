# Stage-1 report: lem-trf-etale-closed-complement-sets

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-closed-complement-sets.json`: statement, split into six proof steps; no exact Mathlib match.
- No new nodes, no new Mathlib leaves, and no unit file changed.
- Sandbox evidence: `citations.json` gives verbatim statement excerpts for every step citation; `searches.jsonl` records the actual new Mathlib queries. Existing item searches are retained.

## Attachments

None. I searched the whole read-only slopmaster2 `WeilConjectures/` for the exact blueprint tag and inspected the closed-immersion/open-closed files for the notions. There is no exact tag hit. `AlgebraicGeometry.Etale.full_lowerStar_of_isClosedImmersion` and `faithful_lowerStar_of_isClosedImmersion` in `SixFunctors/Etale/UpperLowerStar/ClosedImmersion.lean` cover arbitrary coefficients, but do not give the essential-image characterization. The counit/full-faithfulness result in `SixFunctors/OpenClosed/ClosedImmersion.lean` has Grothendieck abelian coefficient hypotheses; `mem_essImage_lowerStar_of_isZero_upperStar` in `OpenClosed/Supported.lean` also has abelian coefficient hypotheses. None supplies all clauses for sheaves of sets. Upstream master was not treated as proof evidence.

## WANTED

None. All literature used is present.

## Corrections and statement audit

The imported statement agrees with Stacks `etale-cohomology.tex`, Tag 04CA, label `proposition-closed-immersion-pushforward`, part (1) and its final assertion. There is no statement dispute. I added references identifying the set-sheaf category and its concrete adjunction; the objects, hypotheses and conclusions are unchanged.

The main issue to avoid was using the abelian theorem as a theorem for sets. `lem-kun-04ca` only states the abelian version. The recorded Lean theorem for `prop-openclosed-lowerstar-fully-faithful` also assumes abelian coefficients. Neither is cited in this split. Instead I use the first, geometric assertion of `lemma-openclosed-stalk-lowerstar`: initiality of the base-change functor on pointed etale neighbourhoods. That assertion is coefficient-independent, and is independently backed by the node's closed declaration `AlgebraicGeometry.Scheme.initial_pointSmallEtaleElementsBaseChange`. I opened its source in `WeilConjectures/Mathlib/AlgebraicGeometry/Sites/EtalePoint.lean`, including the theorem at line 425. The following stalk isomorphism declaration in `OpenClosed/Stalk.lean` has abelian hypotheses, and is not the claim used.

The six steps give the argument of 04CA: set-valued adjunction setup; on-closed-image stalk comparison; the actual counit isomorphism; full faithfulness; terminal restriction off the closed image; and the converse via the actual unit. In particular neither direction is outsourced to a new node restating the item.

## Searches and reuse

Before writing I searched the whole DAG by `04CA`, `04FX`, `03PU`, `03Q1`, closed immersion, stalk, initiality, cofinality, full faithfulness and terminal sheaf. I ran `tools/blueprint_refs.py ancestor lem-trf-etale-closed-complement-sets` and searches for closed immersion, 04FX, 03PU, 04CA, stalk, fully faithful, terminal sheaf and cofinal. The ancestor is `lem-trf-local-term-locality`; no other imported blueprint node states the full set-valued assertion. Its inherited ancestry and the current main-20261015 normal-cone/open-closed route are preserved. This item is not the key statement of `sk-i-curve-zero`, so its realized fields are untouched.

The new msearch calls used both semantic services, Loogle and grep, with a second semantic phrasing. LeanFinder returned scheme-immersion constructions, etale forgetful functors, and structural module sheaf pushforwards. LeanSearch returned site definitions and the empty-cover terminal-value theorem, not the geometric essential-image assertion. Loogle and the grep in `AlgebraicGeometry/Sites` returned no hits. The useful empty-cover fact is a two-line application of the existing set-sheaf definition and stays in step 1. No service was unavailable in these new searches. No new node needs a new search record.

## Not duplicates

No new nodes. In particular `lem-kun-04ca` remains the abelian version, and `lemma-openclosed-stalk-lowerstar` already supplies the required geometric initiality. The existing Mathlib leaf `lem-weil-pbc-initial-functor-limit` supplies the general reindexing theorem. Creating either a new 04FX set-stalk node or a general final-colimit node would duplicate these usable statements.

## Review by NI

I read Stacks `etale-cohomology.tex` at Tag 04CA (`proposition-closed-immersion-pushforward`, including its proof), Tag 04FX (`lemma-stalk-pushforward-closed-immersion`, including both cases and the cofinality argument), Tag 03PU (`theorem-exactness-stalks`, sets clause), and Tag 03Q1 (`lemma-stalk-pullback`, part (3) and its proof by neighbourhood colimits). I also read `categories.tex` at Tag 002R (`lemma-initial`) and 04E7 (`lemma-cofinal`), and the existing blueprint's closed-pushforward neighbourhood proof. The chapter and unit records, the main-20261015 `lem-trf-local-term-locality.proof.md`, and all cited node statements were opened. There are no new node sources to audit.

Step 1 uses the set-valued adjunction statement in `lem-weil-pbc-sets-etale-inverse-image-composition-units`, which explicitly says both that inverse image is left adjoint and that direct image evaluates as H(U times_S T). It uses `def-trf-geometric-morphism` only for the adjunction datum, and the size convention only to choose small representatives. `def-weil-pbc-etale-sheaf-of-sets` supplies the equalizer condition including the empty cover; its two products are singleton sets. `lem-weil-pbc-open-immersion-etale` ensures the empty open really is a site object. This is an elementary specialization of those statements, not a hidden theorem about closed immersions.

Step 2 uses only the initiality sentence of `lemma-openclosed-stalk-lowerstar`; the quote in citations.json stops before its coefficient-ambiguous consequence. It explicitly converts initiality into the set-valued comparison via `lem-weil-pbc-initial-functor-limit` on the covariant function-set diagram W maps to Hom(G(W), A). Contravariance of G makes this diagram covariant. The colimit definition identifies compatible function families with maps out of the stalk colimits, and testing both source and target constructs the inverse. Thus this does not silently dualize initial to final, appeal to a missing colimit theorem, or use the abelian stalk declaration. The formula on germs is the canonical cocone map. All neighbourhood categories are taken within the size convention of step 1.

Step 3 uses the exact unit-germ formula of `lem-weil-pbc-sets-etale-inverse-image-stalk-germ`, not merely an unspecified stalk isomorphism. The triangle identity is evaluated on a section b of G(V_Z); the resulting equation shows that the actual counit stalk is r composed with c. Bijectivity of c also proves that the tested pulled-back germs exhaust its source. The cited detection node states isomorphism detection for sheaves of sets, on arbitrary schemes; I apply it to Z. This repairs the potential gap of establishing an abstract isomorphism without identifying the counit.

Step 4 is elementary adjunction algebra: transpose a map RG to RH and precompose with the inverse counit. Naturality shows that this bijection inverts the direct-image map on Hom sets. No unrecorded category-theoretic full-faithfulness theorem is needed.

Step 5 uses the Mathlib open-immersion-etale node to regard U as a site object, then the site's fibre products to refine every neighbourhood into U and two neighbourhoods into one common such refinement. Its direct image values are the singleton G(empty) from step 1. This explicitly proves existence and equality of all germs off Z. The set-valued inverse-image stalk node applied to j and the sets isomorphism-detection leaf on U imply the unique map to the terminal sheaf is invertible. I corrected an initial draft here by explicitly citing that open immersions are etale and writing the common refinement rather than saying only that germs agree.

Step 6 uses the concrete unit-section formula and the inverse-image germ formula to compute c composed with r composed with eta as the identity on every represented germ. Since c and r are already bijective, eta itself is bijective on the closed-image stalks. For the complement, both source and target are singleton sets, respectively by the hypothesis and step 5. The closed-immersion definition's affine quotient clause justifies the point dichotomy: a field-valued map whose prime belongs to V(I) kills I and factors uniquely through the quotient. The final detection citation is again the set-sheaf theorem, now on X. This establishes the unit of the specified adjunction, not a different map.

I checked that the only geometric hypothesis used is that i is a closed immersion with the stated complementary open; no Noetherian, quasi-compact, reduced, torsion, finite coefficient or finite-type assumption enters. The argument handles Z empty (the essential image is the terminal sheaf), U empty (every sheaf is in the essential image, including nilpotent closed thickenings), X empty (the sheaf category is terminal), a nonreduced closed immersion, and sheaves with empty stalks on Z. Empty stalks on Z stay empty, not singleton; singleton values occur only on the open complement. This distinction also tests the rejection of the abelian zero-support theorem as a set-sheaf substitute.

All non-elementary facts are cited statements: geometric neighbourhood initiality, initial-functor limits, inverse-image germs, and set-stalk detection. The remaining calculations are written in the item's steps. Every proof-step citation has a verbatim statement excerpt in citations.json. The longest non-elementary step is below 2000 characters. No statement-only node contains a proof, no cycle is introduced by a new node, and no forbidden SGA source is used. The off-unit geometric/set-sheaf tools are declared in split_report.tool_uses; they are also recorded as Lean-closed, and the limit/detection/open-immersion tools are Mathlib leaves.

## Unfinished

No mathematical part remains. This is a stage-1 delivery only; no Lean was written and no compiler, Lake command or build tool was run. The required server dry run and push are the delivery checks.
