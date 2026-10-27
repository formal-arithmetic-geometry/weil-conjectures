# Stage-1 report: lem-pur-strict-local-smooth-transfer

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-strict-local-smooth-transfer.json: statement, split in six steps; no Mathlib match.
- citations.json: verbatim statement quotations for each citation in every proof step.
- report.md: this report. searches.jsonl is the search command's unmodified log.

There are zero new nodes and zero new Mathlib leaves. The item statement and its statement dependencies are unchanged. No unit record is changed: this item is not the key statement of its unit. The sandbox initially contained only dispatcher brief markers; there was no earlier split to recover.

## Attachments

None. I searched the live WeilConjectures source by the exact blueprint tag and by strict-henselian, constant-sheaf and affine-line terminology. The affine-line theorems in WeilConjectures/EtaleCohomology/Purity/Smooth/AffineLine.lean, notably nonempty_iso_rightDerivedLowerStar_affineLine and isIso_unit_constantComplex_affineLine (lines 116 and 137), concern the affine-line projection to its base and assume a separated finite-type base over k. The present h is the projection from the base extension to the affine line over k, and R has no finite-type assumption. Those declarations do not attach to this item.

## Literature wanted

None. The sources used are present locally. No SGA source was used.

## Findings and corrections

The imported statement is correct. In particular smooth base change is applied with the smooth arrow f:A1_k -> Spec k and the qcqs arrow g:Spec R -> Spec k. Smoothness of the projection to Spec R would not justify the exchange used here. The source already gets this orientation right. No statement dispute, weakened conclusion, new base hypothesis or coefficient-category change was needed.

The blueprint proof leaves implicit two identifications which are now written out: the base-change composite is the actual h-adjunction unit by the g triangle identity, and derived sections of this unit is the actual cohomology pullback and preserves the constants map. I corrected a provisional non-existent stalk-criterion id to the existing abelian geometric-stalk conservativity node before producing citations, and corrected the source label to Stacks 03PU (theorem-exactness-stalks). I also cited the derived inverse-image adjunction, rather than the sheaf-level definition alone, for the derived triangle identity and unit representative.

## What remains unfinished

Nothing within this one-level stage-1 split. The existing cited nodes retain their own current proof status. No Lean was written and no compiler, Lake or build tool was run.

## Not duplicates

No new node is proposed, so there are no new/existing pairs requiring distinction. DAG and blueprint searches reused affine-space smoothness, affine-morphism permanence, constant pullback and connected constant sections, strict-henselian acyclicity, geometric-point evaluation, geometric-stalk conservativity, exact-functor/cohomology comparison, smooth base change, the explicit derived exchange definition, derived adjunction, and derived-unit/Leray pullback. In particular I did not create a second strict-henselian cohomology lemma, a restatement of the item's unit assertion, or a separate lemma for the elementary triangle calculation.

The imported blueprint search for “smooth transfer” found no duplicate item; “strictly henselian” found the general cohomology node and other strict-local results. The nearest blueprint ancestor is lem-pur-frame-independence through lem-pur-affine-line-ordinary-invariance and lem-pur-supported-affine-line-homotopy, as recorded in the existing blueprint field. The current main-20261015 affine-line proof lives under sec-six-functors-basics/sk-prop-a1-kummer; its Reduction to a geometric fibre paragraph supplies precisely this smooth-square argument. I read that paragraph and the current frame-independence shear paragraph. The earlier unit record's text agrees with the reduction used here.

## Mathlib searches

I retained the item's inherited Q116 search records and added only actual Q153 searches recorded by msearch.py in searches.jsonl: two LeanFinder phrasings, LeanSearch, Loogle and grep. All services returned normally. The first LeanFinder phrasing returned KaehlerDifferential.isBaseChange_of_formallyEtale, StandardEtalePair hom equivalences, and formal-etale algebra facts. The second returned formally-etale localization, etale/quasifinite algebra and formally-unramified scheme facts. LeanSearch returned stability of algebraic smoothness under base change, rather than the smooth base-change cohomology theorem. Loogle returned no hits. Grep in AlgebraicGeometry returned the constant-sheaf import in Sites/ElladicCohomology.lean; I read the imported Sites/ConstantSheaf.lean, which constructs continuous-map sheaves and does not state this assertion. None gives the required derived etale unit, even by a one-line specialization.

## Review by Q153

I read Stacks etale-cohomology.tex at 0EYU (theorem-smooth-base-change), 03QO (lemma-vanishing-etale-cohomology-strictly-henselian), 03P5 (remark-constant-locally-constant-maps), and 03QT/03QU (theorem-equivalence-sheaves-point and lemma-compare-cohomology-point). For the derived-sections map I read cohomology.tex at 01EZ (lemma-before-Leray), 01F9 (equation-functorial-derived) and 01FB (remark-explain-arrow). I compared them with the six steps and opened every cited DAG statement. No new node needs a separate source review.

Step 1 takes smoothness of every affine-space projection from sbc-lem-affine-space-smooth, qcqs of an affine morphism from lem-weil-pbc-affine-morphism-permanence, and the canonical identification of constant inverse images from lem-kun-pullback-constant. The ring tensor calculation gives the specified square and the only nonempty open of Spec k verifies affinity directly. This supplies exactly f smooth, g qcqs and torsion killed by a unit required in the statement of sbc-thm-smooth-base-change. No claim of smoothness for g is used.

Step 2 uses the actual constant-section isomorphism in lem-weil-pbc-constant-sheaf-sections-connected, not just an abstract H0 equivalence. I proved the required nonempty connectedness directly from the unique maximal ideal. The acyclicity node covers every abelian sheaf and every strictly henselian local ring, so it requires neither finiteness nor Noetherianness; it applies to R and to the algebraically closed field k. The geometric-point-cohomology node identifies the germ maps from global sections with all geometric stalks over Spec k. These are exactly its stated clauses, with the algebraic-closure assumption on k verified.

Step 3 reads g_*I from the derived-direct-image definition and its evaluation formula, uses the derived adjunction's explicit unit on a resolution, and uses the exact-functor/cohomology lemma to move exact global sections past Hq. This computes the cohomology maps of the unit, including its H0 constant-section map; it does not merely identify the target objects. The existing abelian stalk-conservativity node then applies to those cohomology sheaf maps. The last inference is the definition of a quasi-isomorphism and localization. No unproved general derived equivalence over a point is hidden here.

Step 4 uses the degreewise abelian smooth base-change theorem, with all hypotheses from step 1. The derived exchange definition explicitly states that its cohomology is that degreewise map; this avoids substituting a theorem for finite-ring constructible complexes or adic coefficients. Its exact inverse-image clause also justifies the displayed source's cohomology and vanishing in negative degrees. A representative of the map is a quasi-isomorphism by the same localization argument as step 3.

Step 5 takes the precise transpose formula from sbc-def-base-change-map and the actual derived adjunction from prop-weil-pbc-derived-inverse-image-adjunction. I substituted the unit a, obtained e^{-1}(epsilon_g o g^{-1}eta_g), and reduced it to the identity by the triangle identity. Equality under the adjunction bijection proves equality with eta_h. This is a short elementary calculation from those interfaces, not an additional purity or base-change lemma.

Step 6 uses clauses (1) and (2) of lem-weil-pbc-cohomology-pullback-derived-unit: the natural Leray isomorphism and the specified pullback of the derived unit. The constants calculation uses exactly the resolution choices permitted by def-weil-pbc-cohomology-pullback (resolve h^{-1}J, then take the composite coefficient resolution) and the normalized constant-section formula in lem-weil-pbc-sets-etale-inverse-image-constant-sheaf. Although the last node is stated for sets, forgetting an abelian sheaf gives precisely the same sections and pullback; the maps in the calculation are already homomorphisms. The equality is on the representing complexes, so it proves equality of the derived constants morphisms, not just equality on H0.

I tested R=k (the identity base change), B=0, positive-characteristic k with ell different from its characteristic, and nonreduced strictly henselian R (e.g. k[epsilon]/epsilon^2). The proof uses only the strict-local acyclicity and affine qcqs properties of R, so it also covers rings of unbounded dimension or without Noetherian hypotheses. The zero ring is excluded by the local-ring convention with a proper maximal ideal. I did not use ordinary affine-line homotopy invariance to prove this transfer, so there is no reverse dependence on its parent. Every citation quote was checked as a literal substring of the cited statement. All six steps are shorter than 2000 characters. Against delivery-errors B–E I checked statement-only requirements (vacuous for new nodes), exact coefficient and site hypotheses, citations rather than proof internals, absence of restatement nodes, and the canonical maps rather than abstract isomorphisms. Generic tools from other units are declared in split_report.tool_uses and preserve the unit's prescribed route.

## Validation

The server review_split check passed with zero new nodes. The final deliver.py --no-push and delivery results are recorded below once completed.

The first dry run rejected the direct-image citation quotation because the displayed formula alone had fewer than the required 40 characters. I expanded it to the complete resolution-computation passage of the same statement; no mathematical dependency changed. I also verified the 03PU source tag directly in tags/tags and read theorem-exactness-stalks in the source.

Final dry run: deliver.py Q153 lem-pur-strict-local-smooth-transfer --no-push exited 0 and printed “OK (not pushed) ... at 0d1af4c7a74: preflight passed”. All server preflight, DAG and split checks passed. Proceeding to the authorized direct push.
