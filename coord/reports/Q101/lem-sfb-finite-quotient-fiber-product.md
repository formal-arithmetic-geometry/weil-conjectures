# Stage 1 worker report — returned split repaired

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-finite-quotient-fiber-product.json` — the statement and complete Lean record are unchanged. Old steps 1, 2 and 4 are retained verbatim. Old step 3 is replaced by five short steps, with its original separation/coordinate-recovery/base-equality route.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-compact-discrete-quotient-realization.json` — one new statement node, a Mathlib leaf for `DiscreteQuotient.exists_of_compat`, `Mathlib/Topology/DiscreteQuotient.lean:341`. No unsplit new nodes.
- `citations.json` — verbatim statement quotations for step 3's existing clopen-basis leaf and step 6's new realization leaf.
- `searches.jsonl` — earlier searches retained; actual additional searches and their results appended by `msearch.py`. The new leaf records the queries actually run for it.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item's blueprint tag, `finite_quotient_fiber_product`, finite/clopen partitions, `exists_of_compat`, `eq_of_forall_proj_eq`, and coherent discrete quotients found no project declaration stating the item or the new lemma. The upstream master reference was also searched for the auxiliary declaration names; it supplies no attachment. Mathlib declarations are treated as leaves, never as project attachments.

## WANTED

None. All mathematical sources used are already available locally.

## What was checked and corrected

The return has one point: step 3 is non-elementary, exceeds 2000 characters, and hides lemmas; extract its arguments while preserving the statement, Lean record, route and other steps. This report supersedes the earlier report's claim that no extraction was needed. The sandbox item was compared field by field with the current shared node: before this repair the only difference was `status` (`split` in the sandbox versus the returned `unsplit` on the shared base). The retained proof and earlier searches were reused. The required initial dry run completed successfully at `c9b0561d3c`; this was a diagnostic run of the old split, not the repair delivery.

The repair replaces old step 3 as follows. New step 3 obtains point separation from the existing clopen-basis leaf. Step 4 uses those separating partitions to prove injectivity, with the explicit compatible triples `t_r(alpha)`. Step 5 extracts compatible source-block choices from a coherent family in the finite fibre sets. Step 6 cites the new exact Mathlib realization leaf in place of the finite-intersection/compactness argument previously carried inline. Its application explicitly checks the passage between clopen partitions and discrete quotients. Step 7 uses the inverse-image partitions of every base partition to prove equality of the two images and then surjectivity. All step texts are below 2000 characters (lengths 560, 1134, 335, 567, 434, 1024, 727, 537). The old compactness, refinement, and final homeomorphism steps remain verbatim; their arguments were not relocated into another node.

The new lemma has hypotheses only about one compact space and a coherent family on all its discrete quotients. It does not mention a span, compatible triples, finite fibre products, injectivity, or a homeomorphism. It therefore isolates the compactness argument rather than restating a clause of the item. There is no proof or proof sketch inside its statement, and its proof/dependency lists are empty as required for a Mathlib leaf.

I searched the whole DAG for `exists_of_compat`, `eq_of_forall_proj_eq`, the Stacks tags 08ZY and 005D, clopen partitions, and discrete quotients. I ran `tools/blueprint_refs.py search` for `discrete quotient`, `clopen partition`, `separate points`, `08ZY`, and `005D`, and checked the ancestor output. The only clopen-partition blueprint hits concern w-contractible scheme covering refinements and w-local schemes, not coherent quotient classes of an arbitrary compact space. The new node has the original nearest blueprint ancestor and the item in its `via` list.

The retained log already contained successful searches for the realization and separation declarations. I read those results and their pinned source. Additional LeanFinder searches found `DiscreteQuotient.exists_of_compat`; Loogle and grep identify the exact theorem. The new leaf records its four actual queries. The exact source at lines 341–352 assumes only `CompactSpace X` and the compatibility equation under `ofLE`, and concludes existence of a point with all specified quotient projections. Lines 76–80 define a discrete quotient by a setoid with open classes. The line-328 point-separation theorem was also read, but no redundant separation node was created: the existing clopen-basis statement already gives separation in two elementary lines. The parent item's existing searches and null Mathlib match are retained.

## Review by Q101

I read the standing stage-1 brief, the stage-1 rules, SETUP's three levels and requirements, delivery-errors B–E, GOAL, the sync rules, the fixed chapter and unit, the item, and its blueprint ancestor's Fibre products paragraph in the main-20261015 snapshot. I read Stacks `topology.tex` at 08ZY (`lemma-profinite`, the finite-clopen-partition proof), 005D (`lemma-intersection-closed-in-quasi-compact`), 0A2P (`lemma-describe-limits`, the compatibility subspace topology), and 08YE (`lemma-bijective-map`). For the new leaf I read the exact pinned Mathlib declaration and its proof at `Topology/DiscreteQuotient.lean:341–352`, together with the definition and order convention in that file. The lemma is the general form of the source-point recovery in 08ZY's surjectivity argument using 005D; unlike 08ZY's full equivalence, it requires neither Hausdorffness nor total disconnectedness.

The item statement still introduces precisely the same spaces, maps, partitions, refinement direction, finite fibres, pullback subspace and canonical map as before. I checked equality of the statement string and equality of the complete `lean` JSON object against the current shared repository, and equality of all three retained step objects. No target, statement or Lean record was changed.

Step 1 still gives the closed equalizer in a compact Hausdorff product and proves total disconnectedness by its two projections. Hausdorffness of the base is used to close the equalizer, and total disconnectedness of the sources is used only for the connected-subset projection argument. Step 2 still constructs a nonempty directed set and checks the refinement maps commute with both base maps. In particular nonempty source blocks have nonempty images, so the claimed containing base block really exists. These are the previously reviewed steps, retained in the requested repair.

Step 3 cites `lem-weil-pbc-profinite-clopen-basis`. I opened its statement: for each point of an open set in a compact Hausdorff totally disconnected space, it supplies a clopen neighbourhood inside that open set. Hausdorffness first supplies an open set missing the other point; the cited conclusion then gives the separating two-block partition, with empty blocks discarded. This is the original separation argument, now its own short step with its actual dependency. Step 4 uses that established separation and the explicitly defined `t_r(alpha)` triples to prove equality of both coordinates. It needs no further topological lemma.

Step 5 uses exactly the refinement maps established in step 2 and coherence of the family. Component r of `x_i` agrees with the choice from the source-only partition triple because `i` refines that triple. For a refinement of source partitions the corresponding triples refine in the same direction, so their chosen blocks are nested. This is a direct component calculation, not an inverse-limit existence theorem.

Step 6 cites `lem-sfb-compact-discrete-quotient-realization`. I checked that its statement supplies existence of a point with every quotient projection equal to the chosen class, not merely a universal property or a definition. To verify its hypotheses, the step proves that open equivalence classes on a compact space form a finite cover and that every such class is also closed (its complement is the union of the others). It thus obtains the partition to which step 5 applies. The nesting from step 5 is exactly the required `ofLE` equation. Conversely each finite clopen partition gives the equivalence relation of lying in the same block, so the resulting point belongs to every previously chosen block. Both directions are direct identifications of classes, with no unproved comparison theorem. Compactness is available for each source; Hausdorffness or total disconnectedness is not silently assumed by this leaf. The old finite-intersection argument is entirely discharged by the named Mathlib theorem rather than left inline.

Step 7 uses continuity only to ensure the inverse-image blocks of a base clopen partition are clopen; discarding empty blocks gives the required source partitions. Membership of `x_i` in `B_i` supplies equality of its two base blocks. Step 6 places the recovered points in those source blocks, and step 3's separation in the compact Hausdorff totally disconnected base forces equality of their images. Hence the recovered pair lies in P and has the required coordinate at every index. This proves surjectivity without asserting that any finite-stage map is surjective. Step 8, the unchanged old step 4, checks coordinate continuity and applies the compact-to-Hausdorff bijection criterion of 08YE with the topology explicitly specified in the item.

For small cases, the new leaf on an empty compact space has no possible chosen class in its empty quotient; the conditional assertion is therefore correct without choosing a point of an empty set. On a finite discrete space the equality quotient pins down the realizing point. On a nonempty indiscrete compact space only the one-class quotient occurs, so any point realizes the family, confirming that neither uniqueness nor Hausdorffness has been added. The item also survives an empty source, both sources empty, empty pullbacks from disjoint images, a one-point base, finite discrete spans, and identity maps of a Cantor space. Empty sources make the relevant finite fibre sets empty and prevent a coherent family; disjoint images are handled by the base-separation step. No surjectivity hypothesis on refinement maps or on `P -> B_i` was used.

I checked B1–B9 for the new leaf: a self-contained TeX statement, inline definition of discrete quotient and refinement, no proof hidden in the statement, exact Stacks tags/labels plus pinned Mathlib file and line, genuine recorded searches, empty proof fields, valid blueprint ancestry, and no existing equivalent node. Every cited statement is copied verbatim into `citations.json`. No DAG edge leads back to the item: the new leaf has only the universe convention as a statement dependency. The existing basis leaf is already a Mathlib tool, and the new leaf is in the item's own unit, so no off-unit route declaration is required. No SGA route, source correction, statement dispute, Lean edit, or compilation was introduced. This repairs the sole return point by extracting the non-elementary compactness lemma and keeping the other short arguments explicit.

## Not duplicates

lem-sfb-compact-discrete-quotient-realization vs lem-sfb-finite-quotient-fiber-product: realization for one compact space and all its discrete quotients does not give the span's compatible triples, coordinate extraction, base equality, injectivity or topological homeomorphism; those remain in the item's proof.

lem-sfb-compact-discrete-quotient-realization vs lem-sfb-integers-profinite-tower: the latter constructs a particular adic integer inverse limit and finite quotient factorization; it does not state realization of all coherent discrete quotient classes of an arbitrary compact space.

lem-sfb-compact-discrete-quotient-realization vs lem-weil-pbc-profinite-limit-function-factorization: the latter descends a locally constant function from an already given profinite limit; it neither constructs a point realizing quotient classes nor applies to arbitrary compact spaces without separation assumptions.

lem-sfb-compact-discrete-quotient-realization vs det-pe-stonean-projective: the latter characterizes extremally disconnected compact Hausdorff spaces by projectivity and sections, not coherent classes on arbitrary compact spaces.

lem-sfb-compact-discrete-quotient-realization vs det-pe-condensed-point-basis: the latter identifies ind-etale algebras over a separably closed field with locally constant function algebras; it does not state point realization.

lem-sfb-compact-discrete-quotient-realization vs lem-weil-pbc-quasicompact-components-clopen-intersection: the latter identifies connected components with intersections of clopen neighbourhoods under spectral-type hypotheses; no compatible quotient family is part of that statement.

lem-sfb-compact-discrete-quotient-realization vs lem-weil-pbc-spectral-proconstructible-closure-specialization: the latter concerns specializations from intersections of constructible subsets of a spectral space, not arbitrary compact spaces and discrete quotients.

lem-sfb-compact-discrete-quotient-realization vs lem-weil-pbc-profinite-clopen-basis: a clopen neighbourhood basis supplies the elementary separation step but does not supply simultaneous realization of a coherent family; the basis leaf also assumes compact Hausdorff total disconnectedness, absent from the new lemma.

lem-sfb-compact-discrete-quotient-realization vs det-pe-wcb-clopen-partition: refinement of a pro-etale covering of a w-contractible affine scheme does not imply the arbitrary compact-space point-realization assertion.

lem-sfb-compact-discrete-quotient-realization vs lem-weil-pbc-w-local-partition: comparison of partitions on a w-local affine scheme and its closed-point set does not state realization of coherent quotient classes.

## What could not be finished

Nothing remains in the mathematical stage-1 repair. Delivery validation is recorded by the delivery tool.
