# Stage-1 report: lem-sfb-relative-flat-closed-kernel-base-change

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-flat-closed-kernel-base-change.json: item, statement, split in four steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-tor-independent-closed-pushforward-comparison.json: new statement-only unsplit lemma, Stacks Tag 0E23; no Mathlib match.
- citations.json: verbatim statement quotes for every use in all four item steps.
- searches.jsonl: actual msearch.py search records; the item retains its inherited searches and appends the new searches.

## Attachments

None for the item or new node. Searches of the live WeilConjectures source by the exact blueprint tag, Tor independence, closed derived base change, and relative-flat closed kernels did not find a declaration proving the item. The existing derivedPullback_structureSheaf theorem supplies only the unit identification in step 4, not the closed-kernel comparison. Pro-etale open/closed exchange has different coefficients and does not attach here.

## WANTED

None. All sources needed for this split are present under literature/stacks-project/.

## Findings and corrections

The item was unsplit and no earlier sandbox node or report was present. Its statement is correct and unchanged. It has no exact Lean attachment. The general Tor-independent comparison was missing from the DAG: the only 0E23 text hits were the item and its derived-Chow parent. The common-base Tor-independence criterion already exists as lem-sfb-flat-families-tor-independent and was reused rather than recreating 0CTA as another node.

The source for the item is more-morphisms.tex Tag 0CTA (lemma-case-of-tor-independence), followed by perfect.tex Tag 0E23 (lemma-compare-base-change-closed-immersion). The source for the sole new node is exactly Tag 0E23, including its proof's explicit unbounded-K clause and the direction of the canonical map. I also read the arbitrary-base descent paragraph of Tag 0CSJ (lemma-derived-chow), which explains why the parent needs this item.

The current blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, clause (3), and the latest unit _section.md. This is an inherited algebraic auxiliary chain below that unit, not an attempt to replace its six-functor route. blueprint_refs.py ancestor returns None for the item, so the inherited null blueprint ancestor is preserved and the new node prepends the item to its inherited via chain. Its exact from.place specifies the 0E23 comparison in the 0CSJ arbitrary-base descent argument. Whole-blueprint searches for Tor independent, Tor-independent, 0CTA, 0E23, compare-base-change-closed-immersion and closed immersion found no equivalent blueprint assertion. The latest blueprint states neither this specific relative-flat closed-kernel lemma nor the general 0E23 comparison as a separate node.

## Mathlib search assessment

All new searches ran through the mandated msearch.py and are recorded exactly with the results digest and actual hit names in each node. Two different natural-language formulations were used for the item and several for the general comparison. Loogle queried "pullback", "structureSheaf" and "baseChange", "derived"; source grep queried Tor independence/derived closed pullback globally and baseChange/base_change under AlgebraicGeometry/Modules. No matching theorem resulted. I read Modules/Sheaf.lean around lines 397--420: restrictUnitIso and restrictFunctorAdjCounitIso concern an OPEN immersion, not the derived Tor-independent closed comparison. IdealSheaf/Functorial.lean lines 79--98 gives the ordinary pullback ideal and isPullback_of_isClosedImmersion, also not this derived statement. The abstract CategoryTheory.Tor hits construct Tor or make it vanish for a projective factor; they do not assert scheme derived base change. LieAlgebra.derivedSeries_baseChange is unrelated. No Mathlib leaves were created.

## Not duplicates

lem-sfb-tor-independent-closed-pushforward-comparison vs lem-sfb-relative-flat-closed-kernel-base-change: the new lemma handles an arbitrary Tor-independent cartesian square and every complex K; it does not establish Tor independence from the relative-flat product hypotheses. The item proves that missing geometric input using two existing lemmas, then specializes the comparison and identifies its unit and exact direct images. Thus this is an independent generic comparison tool, not the item's conclusion under a new name.

lem-sfb-tor-independent-closed-pushforward-comparison vs lem-sfb-derived-chow-neighbourhood: the parent constructs a projective graph neighbourhood and a pseudo-coherent supported kernel. It does not state an arbitrary-K base-change comparison, and is not used in this item's proof.

lem-sfb-tor-independent-closed-pushforward-comparison vs lem-sfb-flat-families-tor-independent: the existing node proves stalkwise Tor vanishing from common-base flatness; it contains no derived direct-image comparison. It is used unchanged in step 2.

lem-sfb-tor-independent-closed-pushforward-comparison vs lem-pc-tor-independent-perfect-tensor-base-change: the latter concerns a perfect tensor factor and qcqs derived global sections, not arbitrary complexes pushed along a closed immersion. No perfectness or qcqs hypothesis is available or needed here.

lem-sfb-tor-independent-closed-pushforward-comparison vs lem-pc-closed-module-pushforward-homology: the latter supplies exactness of ordinary closed module pushforward but no derived pullback comparison. It is used in step 4.

## Review by O2

I read B--E of delivery-errors.md and checked the actual statements of every node cited by the four steps; citations.json copies the relevant full statements verbatim. The new node is a complete standalone statement, introduces all four schemes and both projections, spells out Tor independence, and records the precise canonical map via derived adjunction. It carries no proof or proof dependencies. The source uses all unbounded complexes and imposes no quasi-coherence, Noetherianity or finite-presentation restriction, so none has been added. The composition and adjunction notions in its map are backed by the statements of lem-pc-ringed-spaces-derived-pullback-composition and lem-pc-ringed-spaces-derived-adjoint-general, both read before recording the dependencies.

In step 1, def-pc-fibre-product is used only for the universal-property rebracketing: maps to X_0,Y_0,S with the equal maps to S_0 describe both products. lem-weil-pbc-flat-morphism-base-change says exactly that a base change of a flat morphism is flat, so it applies to Y_0 -> S_0 after base change by X_0. lem-weil-pbc-closed-immersion-base-change supplies closedness of i. No flatness of X_0/S_0 or of a is used. These three statements were opened and their full text is quoted for this step.

In step 2, I instantiated lem-sfb-flat-families-tor-independent with common base X_0, source W_0, target T_0, source-to-target map i_0, and extension X=X_0 times_{S_0} S. Its statement explicitly allows arbitrary extension and does not require i_0 to be flat. Its two flatness assumptions are the given one on W_0/X_0 and the one established in step 1. The product rebracketing makes its target projection precisely q. This is exactly the Tor independence claimed by 0CTA, and the cited node's statement contains the needed stalkwise quantification, not merely a definition of flatness.

In step 3, the new node applies with Z=W_0, X=T_0, X'=T, Z'=W, f=q, g=r. The square is cartesian by the item's definition of W. Closedness of i_0 is a hypothesis; all Tor vanishings are supplied by step 2. Its statement gives the map in exactly the required direction on every K, and K=O_{W_0}[0] is permitted. I compared it line by line with perfect.tex Tag 0E23, including the source proof's exact pushforward assertion and stalkwise comparison. This is a statement of an isomorphism in the derived category, not a per-degree substitute.

In step 4, lem-sc-derived-pullback-structure-sheaf-local explicitly gives Lr^*O_{W_0}[0] isomorphic to O_W[0] without flatness. lem-pc-closed-module-pushforward-homology is about ordinary modules over the ambient O, not modules over a direct-image algebra. Homology preservation applies degree by degree to the three adjacent terms of an arbitrary complex, so acyclic complexes remain acyclic. Applying the exact functor termwise therefore computes its derived functor; on a single sheaf it gives precisely the single ordinary pushforward. This elementary deduction is written in the step, not hidden as a new node. The canonical map is fixed by the 0E23 adjoint and the tensor-unit identification, so the argument supplies the canonical isomorphism asserted by the item rather than an unexplained comparison of cohomology groups.

I tested empty W_0 (both sides zero), identity base change (identity comparison), W_0=T_0 (the tensor-unit case), and nonflat base change from Z to F_p with X_0=Spec Z and Y_0=W_0=Spec Z[t]: the ambient and source remain flat over X_0 and the formula gives F_p[t] in degree zero. Tor independence is essential to the new statement: the self-base-change of Spec F_p -> Spec Z has nonzero Tor_1^Z(F_p,F_p), so the statement without this hypothesis is false; the new node retains it. There is no division by a section, no regularity or finiteness argument, and no condition excluding zero rings or empty schemes.

The four proof steps total fewer than 3000 characters, and none is longer than 2000. Every non-elementary fact is a cited statement; the product reassociation and exact-functor deduction are fully written out. There is no cycle: the new node depends on definitions and established generic derived adjunction/composition tools, not on the item or any of its descendants. Other-unit generic tools are declared in split_report.tool_uses; none replaces the unit's route. No SGA source was used, and no repository/launcher file, Lean source, compiler, Lake or build tool was touched.

## Unfinished work

The sole new node remains unsplit as required for a one-level split. Its later worker has the full 0E23 statement and precise source, rather than an inline proof hidden in this report's delivered node. There is no unfinished step in the item's assembly proof.
