# Q144 — lem-trf-proper-compact-unit-reduction

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-proper-compact-unit-reduction.json`: item, statement; six-step split; not a Mathlib leaf.
- `citations.json`: a verbatim statement quotation for each step/node citation.
- `searches.jsonl`: actual msearch results retained without alteration.
- `report.md`: this report.

No new nodes, no Mathlib leaves, and no unit metadata changes. The item statement and its ten statement dependencies are preserved.

## Attachments

None. Searched WeilConjectures under the read-only slopmaster2 source for the exact blueprint tag and for proper/compact/coefficient/unit combinations. The tag has no hit. Read TraceFormula/Adic.lean's coefficient-change discussion and nonempty_rightDerivedLowerShriek_comp_iso, and the ordinary proper-unit/graph constructions in TraceFormula/Correspondence.lean. Adic.lean explicitly says derived ring scalar extension is not supplied by its abstract coefficient framework; the cohomology theorem takes supplied functor comparisons and does not assert this item’s unit/composition square. Ordinary sheaf adjunction declarations also do not state this square. Nothing qualifies for ATTACH.

## Wanted literature

None. The proof is an agent-written expansion of the current main-20261015 blueprint proof (3), global operator paragraph, not a claim that the Stacks sources themselves state the pro-etale coefficient square. The needed more specific compatibilities already have nodes.

## What was wrong or incomplete

The item had an empty proof. The parent blueprint's assertion of compatibility with compact-support transport needs two distinct equalities: the unit equation for the right mate of the inverse coefficient/pullback comparison, and the coefficient/composition equation for the canonical compact-support maps. Naturality of the compact-support comparison alone would not prove the unit equality. Neither the statement nor the route is disputed or changed.

No earlier attempt had written an item node, report, citations or searches in this sandbox. I checked for an active delivery process before beginning; none existed. Only brief-marker files were present.

## Not duplicates

No new nodes were created. Whole-DAG and blueprint searches for coefficient/unit, proper/compact and coefficient/composition found the existing generic lemmas used here. In particular the generic mate-unit fact is the existing Mathlib leaf lem-pur-mate-unit-compatibility, not a new helper. No clause of the item was moved into a new node.

## Review by Q144

I read the item’s current statement, its source prop-trf-adic-coefficient-morphism-systems.proof.md, proof (3), and the recorded chapter and sk-prop-trace-adic unit. This preserves the finite-level coefficient and global-operator route; it does not use a purity theorem or an SGA source. The elementary calculation below the unit follows the canonical proper graph construction already specified in the item.

I read the actual statements of every cited node. Step 1 uses clause 2 of det-sp-scalar-extension-functor, clauses (i), (iii), (iv) of thm-sf-ctf-stability, and clause (ii) of lem-sf-proetale-constructible-origin. These state respectively preservation under finite scalar extension, preservation under the three operations used, and the existence of bounded etale-origin witnesses. Here h is proper, hence separated finite type, a_X is separated finite type, and all inputs are bounded constructible finite Tor. A and B are finite ell-primary rings; B need not be flat or perfect over A. This verifies the input conditions on the coefficient-composition theorem and the bounded-above condition for point sections. In particular we never replace constructibility by site-perfectness.

Step 2 uses the tensor comparison of lem-fix-compact-support-coefficient-change, the actual formula Rp_*j_! in def-compact-support-direct-image-detailed, the proper-transpose and refinement clauses of lem-sp-et-proet-coefficient-compatibility, the explicitly B-linear map and projection identification of lem-sp-direct-image-change-ring-transpose, and the canonical pullback comparison of lem-fix-operation-reduction. Choosing the proper compactification (id,h) makes the proper coefficient map precisely the mate of mu inverse. Its normalization is stated by the cited nodes; I have not inferred a B-linear identity from equality after restriction of scalars, nor used an unrecorded construction inside a proof. The two definitions of the coefficient map agree by their specified transpose and the refinement assertion.

Step 3 uses the exact displayed unit equation in lem-pur-mate-unit-compatibility, with L1=P_A, R1=F_A, L2=P_B, R2=F_B, G=H=T_X, alpha=mu inverse. The resulting formula has gamma followed by F_B(mu), in that order. I checked Mathlib/CategoryTheory/Adjunction/Mates.lean lines 136–142, theorem unit_mateEquiv: it states this equation. Stacks categories.tex Tag 0B65, label lemma-transformation-between-functors-and-adjoints, provides the adjunction-normalization source, but its counit statement alone is not cited as a unit theorem.

Step 4 uses the explicit last composition equality and refinement identity in the statement of lem-sp-et-proet-coefficient-compatibility. Taking f=h, g=a_X yields equation (C) because a_X h=a_X. The proper candidate supplies F_R; the comparison is the same canonical proper/composition map as in the item. I read Stacks more-etale.tex Tag 0GL6, label remark-Rf-lower-shriek-change-of-rings, and Tag 0F7J, label lemma-shriek-composition, including its compactification construction. Those tags supply the source operations; the stronger normalized pro-etale coherence is explicitly the cited node's agent-stated theorem, not attributed verbatim to either tag. I also read the current blueprint det-sp-reduction-direct-image.proof.md Step 1 to check the transpose normalization.

Step 5 has no new mathematical input. It displays each substitution: naturality of d at eta, equation (C), naturality of C_B at mu, and equation (U). Functoriality then gives the sheaf-level equality. Every term is typed in the B-coefficient derived category on s. This is a routine diagram paste, not a hidden comparison lemma, and is marked elementary.

Step 6 uses exactly the naturality assertion of lem-trf-point-sections-finite-reduction and the unit/proper operator formula of prop-trf-graph-operator. The natural point-sections isomorphism is applied to the bounded point complexes checked in step 1. Writing beta_M as Gamma(d_M) sigma makes its match with the item explicit. Applying naturality of sigma to the sheaf-level arrow yields the displayed ordinary D(B) equation. Naturality in K follows by composing these named natural transformations, without a new existence or uniqueness claim.

The item proof is marked agent-written, with the current blueprint as source. Existing generic off-unit statements are declared in split_report.tool_uses with the reason each is a tool. I checked the graph below every main comparison used here for a path back to the item and found none. Each citation record quotes a verbatim entire cited statement, so the precise clauses and their hypotheses remain available to the reviewer.

Small cases: for j=N, scalar change, mu and coefficient comparisons become their canonical identities and the formula reduces to b=b. For h=id the mate unit and compact-support composition reduce to unit identifications. For K=0 and X empty all arrows have zero source/target. For a proper h on nonproper X the proof uses h proper only, not a_X proper; compact support remains Ra_X!, so no improper replacement by ordinary global sections occurs. The proof never assumes h etale, invertible, smooth, or Frobenius, nor that K is locally free across a stratification.

I checked delivery-errors B–E: there are no new nodes requiring additional definitions or duplicate-tag explanations; the item preserves its blueprint ancestry and statement; all non-elementary inputs are cited by their statements; the mate direction and domains have been verified; the proof does not merely cite a new version of its conclusion. All six steps are shorter than 2000 characters, and the only calculation step consists of explicit naturality substitutions. No statement dispute was found.

## Unfinished work

None in the one-level split. Dependencies retain their existing stage-1 states for their own workers. The delivery preflight and push are run after this report is written.
