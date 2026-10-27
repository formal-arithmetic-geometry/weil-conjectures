# Stage-1 report: lem-trf-fixed-family-affine-span-model

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fixed-family-affine-span-model.json`: existing statement, now split; no exact Mathlib match.
- `citations.json`: one verbatim statement quote for every step/node citation.
- `report.md`: this report.

No new nodes; zero new Mathlib leaves. `searches.jsonl` records the actual required command output; `write_split.py` is sandbox-only working material.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the exact blueprint id and the notions affine span / fixed family. No declaration states the whole item. The existing closed declarations `AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation` and `AlgebraicGeometry.Scheme.exists_pullback_hom_of_isLimit` supply parts of the already attached node `thm-pd-spreading-out`, not an attachment for this item.

## WANTED

None. All sources used are in literature.

## Findings and corrections

The statement is correct as supplied and is unchanged. Its original empty proof did not justify simultaneous descent while keeping the target families fixed. The split first descends only U; it does not replace P_0 or Q_0 by unrelated models. It then descends the two arrows successively, carrying the first to the second arrow's stage by actual base change. A separate projection calculation identifies both limit arrows with the specified ones.

I read `literature/stacks-project/limits.tex`, Tags 01ZM (label lemma-descend-finite-presentation, especially (1),(2)) and 01ZN (label lemma-descend-affine-finite-presentation), as well as `more-morphisms.tex`, Tag 0GDX (lemma-relative-map-approximation-pre), its finite-stage diagram paragraph. The latter explicitly preserves X_i and Y_i while descending U_i. Its additional etale and point assertions are not used here.

The current `literature/blueprint/latest/` local-term statement and proof, and its sk-i-curve-zero section, use the contracting-correspondence route rather than this historical approximation branch. The existing item's `blueprint.from` records that historical provenance explicitly. I preserved it and recorded which auxiliary paragraph this item realizes; no unit or chapter route is rewritten. Whole-blueprint searches for finite presentation, span and 01ZN found no blueprint statement of this simultaneous fixed-target affine span, so `same_as` remains empty. Searches of the whole DAG for 01ZM/01ZN and the descent concepts found the cited general results, avoiding duplicate creation.

Required Mathlib searches were run through msearch with leanfinder, loogle, grep and leansearch, then a second leanfinder phrasing. The actual query texts and results were appended without altering the inherited 2026-10-22 records. This run's LeanSearch was available. Read the source of `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` (Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean:1232) and `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit` (Mathlib/Algebra/Category/Ring/FinitePresentation.lean:81). These descend maps into a finitely presented object; they do not supply this item's source model plus the two fixed target arrows in one specialization. Other hits are affineness results, affine space instances or finite-presentation criteria. No new node is warranted.

## Unfinished work

None in the mathematical split. Server validation and direct delivery follow this report.

## Not duplicates

No new nodes were created. The source-object descent and morphism descent reuse `thm-pd-spreading-out`; the affine-stage claim reuses `lem-weil-pbc-descend-affine`; the morphism and base-change facts reuse their existing nodes. In particular, the item is not replaced by a newly named restatement of either clause.

## Review by Q23

I checked B through E of delivery-errors in full against the source and node statements, including the repeated historical version. Every object in the unchanged statement is introduced, its notion dependencies remain appropriate, and every proof step's uses are included in proof_deps. No new unsplit statement or definition was added. Every quote in citations.json is copied verbatim from the cited statement (full statements are used so that all clauses taken in that step are visible).

Step 1 uses `lem-weil-pbc-affine-scheme-qcqs` precisely for affineness implying qcqs, and `lem-weil-pbc-morphism-affine-schemes-affine` precisely for affine transitions. The latter states that every morphism between affine schemes is affine (Stacks 01SH); it does not require finite presentation. The restriction to the tail is proved using cone legs and a common upper bound, rather than an unquoted cofinality theorem. Nonemptiness and directedness supply all these upper bounds.

Step 2 uses part (1) of `thm-pd-spreading-out`, which explicitly gives a finitely presented source model and a base-change isomorphism. Its hypotheses hold because the stages are affine, hence qcqs, and transitions are affine. The statement of `lem-weil-pbc-qcqs-morphism-permanence` (2) gives qcqs of that source from its finite-presentation structure map; (3) states the base-change preservation of finite presentation needed both for this source and for the actual prescribed target models. I checked the source's Tag 01TS base-change statement in morphisms.tex, together with the qcqs permanence statements in schemes.tex.

Step 3 uses the final clause of `lem-weil-pbc-limit-affine-transition` to obtain that B is affine, then the 01SH node to see the limit source map is affine. `lem-weil-pbc-descend-affine` is exactly the 01ZN statement: an affine limit map between base changes of qcqs objects is affine at some later stage. It does not demand finite presentation of that map. Its S_j, W_j and Y_j=S_j hypotheses were checked, and the limit source is identified with U over B, not merely as an abstract scheme. Affine-morphism permanence (2) makes the stage source affine over the affine S_k. Finite-presentation preservation is from the already cited permanence (3), and the isomorphism to U uses only the fibre-product universal property.

Step 4 uses part (2) of `thm-pd-spreading-out` twice, each time with the actual fixed finitely presented source and target over the current base. The first targets P_k, the second Q_l. There is no assumption that a or c is etale or finitely presented. The base-change permanence node provides precisely the hypotheses after stage enlargement. The unique projection-preserving isomorphism in `def-pc-fibre-product` identifies iterated base changes with P_l, Q_r, etc.; it is not an appeal to an unspecified comparison lemma.

Step 5 uses affine-morphism permanence (1),(2) for later affineness, and qcqs-morphism permanence (3) for finite presentation. These are statements of those nodes, not arguments borrowed from their proofs.

Step 6 is elementary relative to the fibre-product universal property: both composites have the same target projection and the same B-structure projection, so uniqueness identifies them. I wrote the equalities for alpha and beta explicitly, including theta_rl and e_r, so no undocumented transport or eventual equality theorem is hidden. No equality of separately chosen stage maps needs descent: the first map is pulled back directly.

For the reused generic facts I read the source places above, the affine permanence material (01SH and adjacent affine-morphism results), and the existing node statements. The off-unit generic qcqs/affine permanence facts are declared in split_report.tool_uses; the other tools are Mathlib leaves, definitions or Lean-closed. Nothing here replaces a unit-level trace argument.

Small cases checked: a one-element index set gives a model at that same index; empty U or an eventually empty base is permitted by the cited existence and affineness statements; no nonempty fibres or surjective transitions are presumed. Arbitrary non-injective ring transition maps cause no problem, since the proof uses actual base change and the general limit-descent statements. Both target models remain exactly the base changes of P_0 and Q_0 even when their arrows have unrelated descent stages. There are no new statements to test. All six steps are under 2000 characters, and none hides a separately formulated comparison lemma: the only comparison calculation is the elementary universal-property argument displayed in step 6.
