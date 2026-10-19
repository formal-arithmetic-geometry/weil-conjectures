# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-permissible-boundary-preservation.json`: repaired five-step split; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-permissible-coordinate-chart.json`: retained local chart lemma and added the regular-system-of-parameters and closed-immersion dependencies; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-etale-regular-intersection-descent.json`: retained pointwise étale-local descent statement; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-strict-transform-flat-etale-base-change.json`: new statement-only auxiliary lemma; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-etale-component-coordinate-identification.json`: new statement-only auxiliary lemma; no Mathlib match.
- `citations.json`: updated verbatim quotes for all five proof steps.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, permissible-boundary terms, blowup names, normal-crossings names, and all four auxiliary node ids; no sorry-free project declaration states the item or either new lemma.

## Not duplicates

- `lem-trf-permissible-coordinate-chart` vs `lem-trf-nc-maximal-branch-blowup`: the existing node concerns a maximal-branch center and branch-count decrease; this node gives the explicit affine chart ring and all coordinate hyperplane intersections for an arbitrary parameter-generated center.
- `lem-trf-permissible-coordinate-chart` vs `def-nagata-blowup-chart-ring`: the existing definition only defines an affine chart algebra; this node asserts regularity and the local boundary/intersection equations.
- `lem-trf-etale-regular-intersection-descent` vs `lem-trf-etale-reduced-cartier-descent`: the existing node descends reduced induced structure and effective Cartier divisors; this node descends regularity and codimension of a specified family of intersections from local rings at étale points.
- `lem-trf-strict-transform-flat-etale-base-change` vs `prop-nagata-strict-transform-closed-fiber-product`: the existing proposition identifies a constructed chart model with a strict transform; the new statement gives compatibility of that strict transform with a flat étale base change under a generic-point hypothesis.
- `lem-trf-etale-component-coordinate-identification` vs `lem-trf-etale-regular-intersection-descent`: the existing node is a global descent criterion; the new statement identifies individual regular global components with single local coordinate hyperplanes and records generic-point behavior.

- `lem-trf-etale-regular-intersection-descent` vs `def-weil-pbc-finite-etale-category`: the existing node defines a finite étale category and has no regularity or codimension conclusion.
- `lem-trf-etale-regular-intersection-descent` vs `lem-weil-pbc-etale-affine-chart-descent`: the existing node spreads an affine chart property through an inverse system; it does not descend regular intersections.
- `lem-trf-etale-regular-intersection-descent` vs `lem-weil-pbc-etale-base-change-finite-limits`: the existing node gives finite limits and étale-site base-change functoriality, not regularity or codimension.
- `lem-trf-etale-regular-intersection-descent` vs `lem-weil-pbc-etale-covering-base-change`: the existing node says étale coverings remain jointly surjective after base change, not that intersections descend.
- `lem-trf-etale-regular-intersection-descent` vs `lem-weil-pbc-etale-fibre-discrete-separable-points`: the existing node describes étale fibres, with no closed-subscheme regularity statement.
- `lem-trf-etale-regular-intersection-descent` vs `lem-weil-pbc-etale-scheme-base-change`: the existing node states stability of étale morphisms under base change, not regular-intersection descent.
- `lem-trf-etale-regular-intersection-descent` vs `lem-sbc-etale-regular-divisor-base-change`: the existing node treats one principal regular divisor under one affine map; this node handles finite families of scheme-theoretic intersections and codimensions pointwise.

lem-trf-strict-transform-flat-etale-base-change vs lemma-nagata-dense-flat-pullback: the latter assumes scheme-theoretic density and preserves that density; it does not identify the strict transform of a closed subscheme in the base-changed blowup.

lem-trf-strict-transform-flat-etale-base-change vs lem-sbc-stalk-normalization-dense-part: the latter concerns normalization and generic finite étale data on a smooth family, not strict-transform closure in a blowup.

lem-trf-strict-transform-flat-etale-base-change vs lem-sbc-finite-etale-open-generic-algebra: the latter constructs the generic algebra of a finite étale cover; it has no strict-transform conclusion. These are the existing source nodes carrying 081I; none states the new assertion.

## WANTED:

None. ILO Exposé VIII and the cited Stacks files are present locally; the two auxiliary statements are recorded as unsplit agent-level facts because Mathlib has no corresponding strict-transform or component-identification theorem.

## What was wrong or missing

The returned version incorrectly treated `Spec O_{W,w} -> X` as an étale neighborhood. Step 2 now chooses an actual étale map `W° -> X`, forms `X^+ ×_X W°`, and only then localizes the standard chart at the chosen point. The chart lemma is therefore applied to the localization of a genuine étale base change.

The old step 3 falsely applied regular-intersection descent to all irreducible components of `B^+`, which is invalid when the parent boundary has self-intersecting components (for example a nodal cubic). The repaired step uses the coordinate equations directly for the normal-crossings assertion for `B^+` and applies regular-intersection descent only to the exceptional component and strict transforms of the regular components of `H`.

The old proof did not establish that a global `H` component pulls back to one coordinate hyperplane. The two statement-only lemmas supply strict-transform flat-base-change compatibility and identification of the actual distinct regular irreducible components of a reduced divisor with single coordinate hyperplanes. The component lemma is applied only to H on X; its generic-point clause verifies the base-change lemma hypothesis before the blowup charts are used. The chart node now cites both `def-weil-pbc-regular-system-of-parameters` and `def-weil-closed-immersion` as required by its statement.

## Repair of the current return

STATEMENT-DISPUTED: the returned component-identification node was false because it allowed nonmaximal irreducible closed subschemes among the D_a. In X = A², D_1 = origin and D_2 = V(y), their reduced union is the coordinate hyperplane V(y), but the pullback of D_1 under the identity is a point. I corrected the auxiliary statement, requiring D_1,...,D_m to be exactly the distinct irreducible components of D, with reduced induced structure. The item statement and its hypotheses are unchanged.

- E2: the corrected component node excludes that counterexample by maximality of the components. Its conclusion gives a bijection between components through x and the hyperplanes through w.
- B3: the coordinate system is now a regular system of parameters of R = O_{W,w}, explicitly d generators of the maximal ideal, with representatives on V; a coordinate hyperplane is the closed subscheme V(t_i). Added the actual regularity, parameter and irreducible-component definition dependencies.
- B1/B2: deleted the final strict-transform hence-clause and its dependency. The new node remains statement-only, without an internal proof or lemma citation for its conclusion.
- E5/E3: step 2 identifies the original regular H components on X. Step 3 then base-changes their strict transforms and invokes the chart clause. The chosen point tilde y lies over both y and w, in the nonempty spectrum of their residue-field tensor product. No application assumes the desired regularity of a strict transform.
- B5/B3: the strict-transform base-change node now cites Stacks 081I, morphisms.tex, label lemma-flat-base-change-scheme-theoretic-image, and cites def-weil-flat-morphism for flatness. For a finite-type center the complement inclusion is quasi-compact locally on each affine chart; on that complement the boundary is closed, so its map into the blowup is quasi-compact, as required by 081I. The generic-point hypothesis retained in this node is supplied by step 2.
- C1: step 1 now cites lemma-nagata-strict-transform-restrict for restriction off E, including its projection compatibility.
- C8: removed the entire worker-written split_report.tool_uses. Generic tools are described below for maintainer judgment, without writing approval metadata.

I compared the retained returned files with the current shared item: the current item is still unsplit, its statement and statement dependencies agree with the retained version, and the repair changes the auxiliary statement and source, proof steps/dependencies, citation file and review. The delivery tool rebuilds the one-item commit on the current server base. Searches and the previous report's findings are retained; only the two changed search questions were searched again. The new queries and returned types were read and appended from searches.jsonl. No new node was added beyond the four retained auxiliary nodes.

## Generic tools for maintainer judgment

The Nagata blowup properness, complement isomorphism, flat-base-change theorem, strict-transform definition and restriction lemma are generic blowup tools used by the ILO chart route. The properness definition, finite-type Noetherianity, finite-component theorem, reduction definition and étale base-change theorem supply their ordinary scheme-theoretic infrastructure. The regular-normal decomposition theorem rem-pc-regular-normal is used only after regularity of E has been descended, to obtain its disjoint open components. None replaces a step of the unit route. There is no node in the item's unit providing these generic assertions; the maintainer determines their accepted tool-use metadata.

## Review by NJ

I read ILO VIII §§4.1.2–4.1.4(i) on printed p. 117, Remark 4.2.2(i) on p. 118, and Lemma 4.2.9 with its chart computation on p. 121. The item asserts precisely the preservation those passages give for one permissible blowup, allowing an initially normal-crossings B and a strict sub-boundary H. The source's criterion uses the actual irreducible components, which is now also explicit in the corrected auxiliary statement. The chapter and unit route and the ancestor lem-trf-local-term-locality are retained.

For the chart node I reread the ring A_j and its clauses against the ratios t_i/t_j in ILO 4.2.9. For the component node I used the same coordinate setting and ILO's criterion in 4.2.2(i), checking its added maximality hypothesis. For the descent node I read Stacks 025N (proposition-etale-regular) and 039S (lemma-etale-dimension) in etale.tex: the local maps on the ambient scheme and each closed intersection are étale, so regularity and the relevant local dimensions descend. For the strict-transform node I read 081I in morphisms.tex, including quasi-compactness of the image map; it is the flat-base-change statement about scheme-theoretic images needed for closure. I also read 080F in divisors.tex and checked that it concerns a flat scheme or module over the blowup base, not the flat change of ambient base asserted here. The source correction is therefore substantive.

Step 1: I opened all six cited statements. Properness gives finite type exactly by def-weil-proper-morphism; finite-type-over-Noetherian gives the Noetherian blowup, and the finite-component theorem gives finite index sets. The complement theorem identifies the blowup away from M, and the newly cited strict-transform restriction lemma gives exactly the compatible ordinary-pullback identification used there. The center ideal is finite type because the ambient scheme is Noetherian.

Step 2: I opened the corrected component statement and checked every hypothesis at D = H on the original X: local Noetherianity, actual distinct components, reduced structure, regularity of each H_a, an actual étale W, and the regular parameters and product equation at w. The subset equation for H follows by choosing the coordinate branches belonging to the reduced union H. The lemma gives a distinct hyperplane per original component and the generic-point conclusion. It is never applied to H-plus.

Step 3: I opened the étale base-change statement, the blowup comparison and its defining statement, the strict-transform flat-base-change node, and all clauses of the chart node. The first gives étaleness of Y to X-plus; the second is the comparison isomorphism for the flat map W to X. A point over the pair (y,w) exists because their residue-field tensor product over k(x) is nonzero. Localization is performed only after forming this genuine étale base change. The composite is now written in order: identify H_a with its coordinate hyperplane before blowing up, base-change H_a's strict transform, and apply the chart lemma to that hyperplane. The chart lemma gives the exceptional equation and regular intersections. This establishes the local hypotheses without assuming the regularity being proved.

Step 4: I checked both clauses of reduced-Cartier descent, so the calculated reduced supports are the actual pullback closed subschemes and effective Cartier descends. The finite family for regular-intersection descent is E together with the nonempty H_a strict transforms; it does not presuppose regularity of the global components of B-plus. The empty intersection supplies ambient regularity, and every nonempty selected intersection has the chart's codimension. Only after E is regular do I apply rem-pc-regular-normal. I opened its complete statement and Stacks 0569/033M (properties.tex, lemma-regular-normal and lemma-normal-Noetherian); its Noetherian hypothesis follows from step 1. Its disjoint open component conclusion lets the regularity and intersection results pass to the actual exceptional components, including a disconnected center. The nonempty strict transforms are closures of irreducible opens and are consequently irreducible. This is an ordinary closure argument, not an application of the component lemma to unknown transforms.

Step 5: I read both definitions cited here. The scheme-theoretic closure defining strict transform, restriction off the center, and the displayed chart support equations give the two identities as reduced closed subschemes. The coordinate inclusions show the component assertion. The finite-component statement applies to the Noetherian closed boundary, and the empty-product convention includes H empty.

For B1–B9 and C1–C8 I checked that each new node is a self-contained statement with no proof steps, that its notions have definition dependencies, that its blueprint origin and same_as searches remain recorded, and that no existing source or blueprint node supplies a duplicate. The new 081I source overlaps only the three nodes distinguished above. I read all returned search hits; they give generic étale or flat infrastructure and image-support lemmas, without the required component correspondence or scheme-theoretic strict-transform equality. No invented search is recorded. I also replaced the retained chart statement’s literal newline escape with a real line break. Every citation now quotes the exact full statement including hypotheses from the file used by its step.

I tested the corrected component statement on two coordinate axes in A², a single regular divisor, an étale cover with several sheets (shrinking around the chosen sheet), and the empty divisor. The origin-inside-a-line counterexample is explicitly excluded by the new maximal-component hypothesis. For the chart and item I checked a principal center (the blowup is an isomorphism and a component contained in the center has empty strict transform), a two-parameter center, H empty, a disconnected regular center, and a self-intersecting B with only its regular sub-boundary H used in the component identification. The mixed-characteristic chart R = Z_p[[x]], J = {p,x}, has p = xu in the x-chart; the exceptional equation remains x and the surviving strict transform is u, so the same argument applies. The point and base-change hypotheses hold in these cases. All five non-elementary proof steps are shorter than 2000 characters. No target statement, live file, Lean source, compiler, Lake invocation or build was changed or run.
