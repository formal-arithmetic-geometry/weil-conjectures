# Stage-1 delivery: lem-per-alteration-cover-closed-fibre-shrink

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-alteration-cover-closed-fibre-shrink.json`: statement, now split into eight steps. No Mathlib match; retained the earlier attempt's proof, source references, and logged searches after comparing with the current unsplit repository item.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-alteration-site-localization.json`: one new statement-only node, unsplit. No exact Mathlib match. `CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget` is a candidate for its topology clause, not for the equivalence of alteration categories.
- `citations.json`: one verbatim statement quote for every step/node citation (31 pairs).
- `report.md`: this report and self-review. `searches.jsonl` retains the actual previous search outputs; no search has been invented or rerun merely because the earlier attempt lacked a final answer.

## Attachments

None. Searched the project source under `WeilConjectures/` for the item's blueprint tag, closed-fibre and alteration-cover terminology, and alteration/localization terminology. No project declaration states the gluing result or the new localization result. General closed-fibre statements about pro-etale covers, henselian connectedness and cohomological base change concern different sites and do not provide an attachment. Upstream master was reference material only.

## Literature wanted

None. The ILO book is present; its existing sandbox text was read against the relevant numbered propositions. No SGA source is used.

## Changes and discrepancies

The current repository item agrees with `original-item.json` in the sandbox: it already contains the corrected punctured-scheme conclusion and the warning about ILO II 4.1.1. Its statement and protected provenance fields are retained. The new work is a proof and one subsidiary comparison statement, not another copy of a conclusion clause.

The finite family of pointed neighborhoods is completely decomposed over the punctured scheme, not necessarily over all of S. For example, for an excellent DVR with uniformizer pi, the sole nonclosed point is the generic point, and its pointed neighborhood can be D(pi); it misses the closed point. One cannot use these neighborhoods alone as a covering of S. Instead, after pulling them to each P_i, the open V_i supplies every point over the closed point. This repairs the inference that would otherwise fail.

## Source error

ILO III Proposition 6.2, printed p.44, invokes II 4.1.1 for both the alteration and prime-to-ell alteration cases. The statement and proof of II 4.1.1, printed p.31, give only the alteration-topology shrinking result. I do not assert that the prime-to-ell conclusion is false; that citation does not prove it. The present item already explicitly corrects this gap by including the pointed-neighborhood induction input. The proof uses II 2.1.1--2.1.2 and 2.3.1 on each P_i, then composition and refinement. It does not infer the prime-to-ell version of II 4.1.1 from the ordinary alteration version.

## Not duplicates

lem-per-alteration-site-localization vs lem-per-alteration-cover-calculus: the existing statement gives fibre products, composition and pullback within alt/S (and dominant base change), but does not identify alt/T with the slice of alt/S or compare the two generated topologies. The new node supplies exactly this ambient-site comparison; the item cites the existing calculus separately for actual pullbacks and compositions.

lem-per-alteration-site-localization vs def-per-prime-to-ell-alteration-topology: the existing node defines the category and the generators; it does not state the equivalence or topology-localization theorem.

lem-per-alteration-site-localization vs lem-per-dominant-part-coreflection: the existing node gives the dominant reduction functor, its universal property and etale comparison, not the equivalence of alteration slice sites. These are distinct statements even though their sources overlap in ILO II 1.2.

lem-per-alteration-site-localization vs lem-per-alteration-finite-normal-generator-tree: the existing node gives finite normal integral refinement trees, not site localization. Both use II 2.3.1 for different purposes.

lem-per-alteration-site-localization vs lem-per-alteration-generators-reduced-base-change: reduced dominant base change of generating families is a covering-calculus assertion; it does not assert an equivalence between alt/T and an over category.

Searched all DAG nodes and the whole imported blueprint with `tools/blueprint_refs.py` for alteration, alt/S, alteration site, localization and 1.1.10, and read the relevant alteration-node statements. No existing node states the new comparison. The ancestor command confirms `lem-per-artin-gabber-affine-curve`; the new node's `from` has the item prepended to its ancestor chain. Its `same_as` is empty.

## Mathlib search assessment

The previous attempt's logged item searches return ordinary scheme gluing, ordinary etale topology and scheme-cover declarations. Those do not assert regular prime-to-ell alteration-cover gluing. The inherited item's original three search records are preserved as repository provenance, and are not claimed as searches run by this continuation. The actual Q130 search log includes two phrasings for the item and two for the new comparison. Loogle's initial unknown-identifier response is recorded as unavailable; the later valid etale-topology query returned results.

For the new node, the generic topology localization search returned `CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget`. I read `Mathlib/CategoryTheory/Sites/Over.lean` lines 540--548: its hypotheses are a precoverage with pullbacks and stability under base change, and its conclusion concerns the over category of the same category. It does not construct alt/T, prove that an S-morphism between alteration objects is generically finite dominant over T, or identify the intrinsic generating maps. Hence this is an unsplit node with a candidate, not a Mathlib leaf. The second semantic phrasing returned Noetherian-scheme and generic site constructions only; the alteration/completely-decomposed grep had no hits. Every new-node query is copied exactly from `searches.jsonl`.

## Review by Q130

I read ILO II Proposition 1.1.10, Definition 1.2.2, observations 1.2.3, the dominant-part construction 1.2.5 and Proposition 1.2.6, Definitions 2.1.1--2.1.2, Corollary 2.2.4, and the generators and following remark in 2.3.1--2.3.2, printed pp.24--28. I also read the local-descent argument of III 6.2 on pp.43--44 and II 4.1.1 on p.31. These sources justify the route used and show exactly why the unsupported shrinking citation must be replaced. For the new node, II 1.1.10 and the first paragraph of the proof of 1.2.6 supply the category-over-an-object identification; the generator definitions are intrinsic to each arrow and supply the topology comparison after localization. The statement is standalone, introduces S, ell and T, defines the slice and the localized covering condition, and has no embedded proof.

Step 1 uses `def-per-prime-to-ell-alteration-topology` for finite type of P_i and Q_tj over their bases; `def-sbc-locally-finite-presentation` and `def-weil-finite-type-morphism` spell out why finite presentation implies finite type. The exact statements of `lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-noetherian-open-subscheme-noetherian`, `lem-weil-pbc-qc-open-immersion-finite-type`, and `lem-sfb-finite-type-composition-base-change` provide the Noetherian, open-subscheme, open-immersion and composition assertions used. In particular, the open immersions are quasi-compact because inverse images of affine opens are opens in Noetherian schemes. This verifies the finiteness hypotheses before applying the later scheme lemmas.

Step 2 uses `lem-weil-pbc-etale-scheme-base-change` for the restricted etale neighborhoods. `def-weil-open-immersion` identifies their local rings under restriction. The statement of `lem-per-completely-decomposed-etale-finite-subcover` has precisely the rational residue-field lifting condition constructed here, and only requires a Noetherian target. It therefore applies to U, not to all of S. No properness of P_i or separation of the punctured scheme is smuggled into this argument.

Step 3 uses the etale-comparison clause of `lem-per-dominant-part-coreflection` first for T_t over the reduced integral base S and then for V_i over P_i. This shows that no vertical component or nilpotent survives in those sources. `lem-weil-pbc-open-immersion-etale` applies to the actual open immersion V_i into P_i. The affine residue-field statement `lem-weil-pbc-etale-algebra-residue-field-separable` gives finite extensions for T_t; the generic degrees for Q_tj over S are finite by composing its finite extension over T_t with that one. These are exactly the object conditions in `def-per-prime-to-ell-alteration-topology`. There is no assertion that the individual maps Q_tj to S are themselves singleton covers.

Step 4 uses the new `lem-per-alteration-site-localization` at the Noetherian alteration object T_t established in Steps 1 and 3. Its last sentence states exactly that the given family covering T_t in alt/T_t is covering T_t in ambient alt/S. This was the genuine comparison missing from the older argument: none of the existing calculus nodes explicitly states it. The subsidiary lemma is strictly smaller than the item's regularity-and-boundary gluing assertion and contains no such gluing clause.

Step 5 uses `lem-per-alteration-cover-calculus` for the categorical fibre product and the etale-comparison clause of `lem-per-dominant-part-coreflection` to identify it with the ordinary product when T_t to S is etale. `lem-weil-pbc-etale-scheme-base-change` and `lem-weil-pbc-open-immersion-etale` give the etale maps into P_i. `def-pc-fibre-product` supplies the actual point over kappa(p): the rational point of T_t above u gives a section after extension from kappa(u) to kappa(p). Its residue field is exactly kappa(p), since it embeds back into the base field over that base field. The V_i branch handles every p over s. Thus the generator condition in `def-per-prime-to-ell-alteration-topology` is verified for every point of P_i, including the closed fibre.

Step 6 applies the pullback and composition clauses of `lem-per-alteration-cover-calculus` entirely within alt/S, after Step 4 established the correct ambient site. Each source R_itj has a genuine projection to Q_tj, so the constructed covering family refines the desired V_i,Q_tj family. Upward closure follows by the explicitly written sieve-transitivity argument using the axioms in `def-weil-pbc-topos` and the definition of generated sieve in `def-per-prime-to-ell-alteration-topology`. No regularity is assumed for a dominant fibre product R_itj; regularity is only used for the larger family after this refinement argument.

Step 7 uses both clauses (1) and (2) of `rem-pc-regular-normal`: regular schemes are normal, and a Noetherian normal scheme has finitely many disjoint clopen integral components. This is the sole non-Mathlib off-unit tool, declared in `split_report.tool_uses`; the curve-perverse unit gives no substitute for this scheme fact. The component-cover and composition clauses of `lem-per-alteration-cover-calculus` give the covering. The component sources remain dominant because the original sources are alteration objects, and regularity is local by `def-weil-open-immersion` and `def-weil-regular-scheme`.

Step 8 is the elementary restriction of `def-trf-strict-normal-crossings-boundary` to a clopen component, using the unchanged local rings from `def-weil-open-immersion`. Each integral boundary component belongs to exactly one clopen component, so one merely discards those outside it. The effective Cartier ideal, radical condition and all intersection local rings and dimension equalities are literally restrictions. This verifies the boundary conclusion, including empty boundary; no separate boundary transport theorem is being silently used.

I checked B1--B10: the new node has no proof, is self-contained, cites actual definitions, uses single TeX escapes, has precise numbered ILO places, makes no false Mathlib-leaf claim, and carries a populated blueprint reference. C1--C8: every non-elementary input is a cited statement, no proof-internal construction is borrowed, the quotes in `citations.json` are verbatim, and the off-unit tool is explicitly justified. D1--D5: the item actually constructs F and the cover on P_i, then carries out the composition/refinement and boundary restriction; the new node is only a comparison used in Step 4. E1--E7: I verified the Noetherian and finite-type hypotheses, the actual scheme fibre products, the finite generic residue extensions, and the distinction between a cover of U, of T_t, of P_i, and of S. No step exceeds 2000 characters.

Small cases: when S is a field, U is empty and F can be empty, while V_i contains the entire P_i and hence already covers. Empty P_i or Q_tj contribute no components; a covering cannot have all sources empty when its target is nonempty. An empty T_t is allowed only if no specified point is required; each indexed T_t here has its specified point. A DVR with T_eta=D(pi) tests the missing closed point and the need for the V_i branch. Reducible regular sources have clopen components, so there is no crossing between components on restriction. For the new localization statement, T empty yields empty slices and the asserted equivalence; a nonempty disconnected T tests the generic-point requirement component by component, and a vertical X to T is excluded by the alteration-object hypotheses. No surjectivity of T to S is needed. The chapter and unit route is unchanged; this is the inherited finiteness/duality input under the Artin--Gabber affine-curve node, not a replacement of Fourier exactness.

## Unfinished work

No part of the item's natural-language split remains unfinished. The new comparison node is deliberately statement-only and queued for its own later split, as required for a one-level delivery. Mechanical preflight and delivery results are reported by the delivery command.
