# Q135: det-cor-affine-space-rational-line

## Files written

- `dag/nodes/sec-six-functors-basics/det-cor-affine-space-rational-line.json`: statement; repair split of the existing proof. The rational condensed-coefficient adjunction is not in Mathlib. Ten proof steps replace six; only the original first step is reworked, and subsequent step references are renumbered.
- `citations.json`: 30 verbatim statement excerpts for all citations in the ten steps.
- `report.md`: this report. `searches.jsonl` retains the interrupted attempt's searches and adds resumed searches.

New nodes: 0. New Mathlib leaves: 0. Existing geometry statements, including Mathlib leaves, already cover every hidden lemma. No unit file is changed; this item realizes the d=1 part of the unit, whose statement is realized by the induction node.

## Attachments

None. I searched the project under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id, affine-line adjunction, affineLine adjunction names, and the geometry notions. The Fourier localization-restriction adjunction lemmas are different statements. The item's Lean audit is `none` on both branches. No finished project declaration states all three clauses with these condensed rational coefficient categories and counit compatibility. The existing Lean record is retained exactly.

## WANTED

None. The current blueprint and the Stacks sources used here are present locally.

## Repair of the dedicated return

The 2026-10-17 return names one fault: the old first step (2108 characters) contains non-elementary geometry arguments inline. I preserved the item's entire statement and Lean record. The old first step is replaced by five short steps, with the standard chart and proper projection as before. Affine-morphism permanence now supplies the affine-line separatedness, composition permanence supplies separatedness of the total spaces over k, and qcqs permanence supplies the quasi-compactness of the total spaces and the open immersion. This removes the inline diagonal-composition and localization-affineness arguments instead of merely distributing them across shorter paragraphs. The five following arguments are retained, with numerical cross-references changed to the new numbering. No theorem about purity or a different coefficient category is substituted.

There is no new statement dispute. The previous split_report mentioned the earlier restoration of standalone base and coefficient hypotheses. Those hypotheses and that statement are left intact in this repair.

The old geometry step cited `lem-pc-quasi-compact-local-on-target`. This repair uses the existing stronger qcqs-morphism permanence statement after checking its source and target hypotheses, so that citation is no longer needed. Definitions of polynomial charts make affineness and finite type immediate; creating a separate node for that two-line calculation would violate the rule on elementary nodes. Creating a new composition or affine-permanence node would duplicate the DAG.

## Unfinished work

None in the stage-1 repair. No Lean has been written or compiled. Dry-run and delivery results are recorded below when available.

## Not duplicates

No new nodes or same-tag pairs. I searched the whole DAG and whole blueprint for affine-space projections, locally finite presentation, composition, separatedness, finite type, and quasi-compact opens; the searches led to the existing affine-morphism, proper/fp, qcqs-over-affine and qcqs-morphism permanence nodes. In particular, composition is already clause (e) of `lem-weil-pbc-proper-fp-permanence`; no new composition leaf is warranted. The finite-coefficient affine-space adjunction is not the present rational coefficient statement, and the induction node states the general-dimensional result using this item, so neither replaces the present item.

## Mathlib searches and source checks

The earlier log was read and retained. Its geometric hits were inspected in Mathlib: `AffineSpace.lean:374,384` (affineness and locally finite presentation); `Morphisms/Separated.lean:75,119` (composition and affine separatedness); `Morphisms/FiniteType.lean:68`; `Morphisms/QuasiCompact.lean:69`; and `Morphisms/FinitePresentation.lean:108`. They supply geometry already represented in the DAG, rather than the condensed-coefficient exceptional adjunction. Current semantic searches for the latter return ordinary sheaf adjunctions and localization/shift results, which do not state it. A resumed LeanSearch request returned a rate-limit response and is recorded as unavailable. No unavailable search is evidence of absence. Every appended mathlib_searches entry is copied from a real entry in this sandbox's search log; no new node is created.

## Review by Q135

I read the current main-20261015 item and its unit and chapter: the unit composes the open adjunction with the projective-line adjunction and then applies uniqueness. The repair retains precisely that route. For the geometry I read Stacks constructions.tex Definition 01M0 and its polynomial-chart paragraph, morphisms.tex Definitions 01S6, 01T1, 01W1, Lemmas 01S7 and 01T3, and schemes.tex Lemmas 01K4, 01K6, 01KU and 03GI. I read the statements of all 24 nodes cited by the final proof; each citation has its verbatim excerpt in citations.json. No new node requires a separate source audit.

Step 1 uses the standard-chart node for an open immersion over V, the projective-space definition for the homogeneous-coordinate convention, and the proper-projective-space node for properness with the two-element coordinate set. These statements give those facts over every scheme, so the possibly empty V and the dimension convention cause no gap. I also read the chart node's main-20261015 blueprint_update: its version with an extra homogeneous coordinate gives the same line chart and the same equality qj=p.

Step 2 uses the concrete inverse-image chart in `def-nagata-relative-affine-space`, the actual definition of an affine morphism, and the definition of finite type. The inverse image of every affine W is Spec R[t]; it is affine, with the one generator t, giving the required one-member finite affine cover. This calculation is elementary and introduces no new lemma. It is valid also for the zero ring, nonreduced rings, and empty base. No Noetherian assumption or finiteness of a chosen cover of V enters it.

Step 3 uses clause (3) of affine-morphism permanence for separatedness and quasi-compactness of p. It uses the definition of properness, and then finite type, to obtain the corresponding properties of q. The qcqs-over-affine statement explicitly gives that a separated finite-type scheme over a field is qcqs; this applies to V. Clause (2) of qcqs-morphism permanence then gives quasi-compactness of each total space. Only its quasi-compactness clause is used here: quasi-separatedness of a proper map is not silently assumed or borrowed from an uncited lemma.

Step 4 uses clause (e) of proper/fp permanence, whose statement separately covers composition of separated maps and composition of locally finite-type maps. Both component maps have those properties. The affine-scheme qcqs node makes Spec k quasi-separated. Clause (1) of qcqs-morphism permanence applies because the total spaces were proved quasi-compact in step 3; it makes each composite structure map quasi-compact. Combining this with local finite type is exactly the finite-type definition. Finally qcqs-over-affine supplies quasi-separatedness of each total space. These citations replace the old hidden diagonal-composition argument and check that all schemes remain in the standing category over the original k. No hypothesis about V being affine is introduced.

Step 5 applies clause (1) of qcqs-morphism permanence to j, with quasi-compact source from step 3 and quasi-separated target from step 4. It gives precisely the quasi-compactness required in the compactification definition, alongside the open immersion, proper q and factorization already proved. This also replaces the old inline principal-open localization argument with a stated existing lemma, without any purity theorem.

Step 6, formerly step 2, uses clause (2) of `det-def-localizing-closure-ctf-equals-bc` on the three qcqs schemes for the SAME Lambda=E or Qlb. Clause (1) of `det-sf-mate-open-restriction` explicitly supplies preservation and the restricted open adjunction. Its quasi-compact-open and standing-setting hypotheses were verified in steps 1–5. No other clause of that stronger node is used.

Step 7, formerly step 3, uses the compactification-specific derived-shriek definition, the chosen compactification in `sk-prop-sf-existence`, and the isomorphism between any two compactifications stated by the coherence/cocycle node. The last requires separated finite-type p and qcqs V; those were proved. The full-subcategory equality from step 6 puts the comparison on the categories in the item.

Step 8, formerly step 4, uses the composition isomorphism explicitly included in the module pushforward/pullback statement, exactness explicitly asserted by Cartesian coefficients, the derived-pullback definition, and the twist compatibility explicitly stated in the twists node. Since p differs from ell, ell is invertible on the schemes over k. The coefficients remain the specified condensed rings throughout, including the finite-subextension convention for Qlb. Passing an exact isomorphism degreewise to complexes, and the displayed even shift's termwise calculation, are the routine derived-definition consequences already written in that retained step.

Step 9, formerly step 5, uses the projective-line triangle node's explicit consequence Rq_* left adjoint to q^*(1)[2], not merely an assertion about a trace. The retained chain of Hom bijections composes it with the adjunction in step 6 and the isomorphisms in steps 7–8. Naturality and the inverse composite are spelled out. This is a proof of the item's adjunction, not a new node restating its clause.

Step 10, formerly step 6, uses the Brown right adjoint supplied by the existence node and the full statement of uniqueness of right adjoints, including the transpose formula and unique counit-compatible natural isomorphism. Thus it proves the specified final compatibility, rather than only the existence of some isomorphism of functors.

I checked delivery-errors B–E against these files. All statements are unchanged, all dependency ids are existing and unmerged, proof_deps is exactly the union of uses, and every use is backed by an exact statement quote. No new node duplicates a fact, hides a proof in its statement, or restates a clause of the item. There is no new induction or comparison hidden in the repaired geometry. All ten steps are below 2000 characters (maximum 966); the repaired geometry steps are at most 767. I checked the empty-base case, the zero-ring affine chart, and arbitrary nonreduced/nonaffine separated finite-type V: all cited geometry lemmas apply as stated. The same checks apply to both rational coefficient choices. No SGA source is cited. The generic off-unit geometry uses are declared in split_report.tool_uses; existing maintainer-owned tool metadata is preserved.
