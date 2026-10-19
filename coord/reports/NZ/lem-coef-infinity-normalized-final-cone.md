# Worker report: lem-coef-infinity-normalized-final-cone

1. Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-normalized-final-cone.json`: item, split in six steps; statement unchanged; no full Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-slice-right-fibration.json`: new statement, unsplit; no Mathlib match. Gives the join-slice projection for arbitrary small diagrams, the quasicategory property, and its vertex-slice Kan fibers.
- `dag/nodes/sec-six-functors/lem-coef-right-fibration-contractible-fibers.json`: new statement, unsplit; no Mathlib match. Converts right-horn lifting and weakly contractible Kan fibers to all boundary lifts.
- `dag/nodes/sec-six-functors/lem-coef-infinity-slice-equivalence-final.json`: new statement, unsplit; no Mathlib match. Characterizes all final objects of a vertex slice by equivalence arrows in the original quasicategory.
- `citations.json`: verbatim statement quotations for every citation in all six proof steps.

2. Attachments

None. Read-only searches of both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` by the item tag and by normalized cone, pinched mappings, quasicategory, slice, terminal object, and fibration found no exact project declaration. Ordinary slice/sheaf results do not state this coherent simplicial theorem. No upstream sorry was treated as a finished proof.

3. Sources wanted

WANTED: archival copy of Kerodon Corollary 4.7.3.21 (02J4), for the item. Read its complete proof online at https://kerodon.net/tag/02J4.

WANTED: archival copy of Kerodon Proposition 4.3.6.1 (018F), Construction 4.6.5.1 (01KX), and Proposition 4.6.5.5 (01L0), for `lem-coef-infinity-slice-right-fibration`.

WANTED: archival copy of Kerodon Proposition 4.4.2.14 (01NU), for `lem-coef-right-fibration-contractible-fibers`.

WANTED: archival copy of Kerodon Proposition 4.7.3.20 (02J2), and Proposition 4.6.5.10 (01L5) for the mapping-space convention, for `lem-coef-infinity-slice-equivalence-final`.

These were read online without downloading or modifying the literature. The identifiers are Kerodon tags, not Stacks tags. Stacks provides the ordinary simplicial lifting tool (08NM), not the quasicategorical slice/finality results. The item is marked `proof_origin.by = agent` because its proof source is not locally archived. No SGA source is used.

4. Audit findings

The assigned item is missing from the shared side snapshot. It exists as an unsplit node in `/home/ubuntu/weil-nt-live-dag/nodes/sec-six-functors/`, the authoritative live mirror used by delivery. I copied that input into the sandbox without changing any live file. It has no Lean audit declaration. The shared `blueprint_refs.py ancestor` consequently prints `None`; I retained the actual live node's ancestor `prop-coef-integral-exceptional-adjoint` and its full ancestry. The existing unit is `sk-prop-sf-biduality-general`; that maintainer-owned binding was retained. I read that unit, the six-functors chapter, and paragraph 2 of the current main-20261015 integral-adjoint proof. The present split serves its existing stable-enhancement infrastructure and does not replace a unit step.

There was no proof to repair and no false statement was found. The proof now explains the strict normalization, not merely existence of a cone up to equivalence. It does not use the parent terminal-anodyne theorem or final-index-colimit consequence, which would make the argument circular. No target statement or coefficient category was changed.

5. Unfinished work

The three new foundations are deliberately statement-only nodes, with no proof sketches in their statements and no proof dependencies. They are the next items to split. The item itself is complete at this split level. The required dry run validates its delivery format before handoff.

## Not duplicates

The DAG and whole imported blueprint were searched by `018F`, `01NU`, `02J2`, `slice`, `right fibration`, `contractible fibers`, and final/terminal cone phrases. No blueprint node states any new result. All Mathlib searches used the required msearch.py command, and each new node has LeanFinder, LeanSearch, Loogle, grep, and a second semantic phrasing. Raw outputs are in `search-results.json`; the command log is `searches.jsonl`. Candidate files were read before recording absence: ordinary `Over.mkIdTerminal` is not a theorem about higher mapping spaces; `SSet.quasicategory_iff_of_isTerminal` refers to a terminal simplicial set, not a terminal vertex; Mathlib's available fibrations lift all horns, while a right fibration assumes only the positive-index horns.

lem-coef-infinity-slice-right-fibration vs def-cbc-enhanced-diagrams-cones: the existing node defines the pinched mapping simplices and comma cones; it asserts neither the join-slice construction nor a horn-lifting theorem for its projection.

lem-coef-infinity-slice-right-fibration vs lem-cbc-enhanced-functor-cone-calculus: the existing statement treats internal functor and arrow-comma cone categories, not join slices or right-fibration projection properties. A comparison of different slice models cannot be silently assumed.

lem-coef-infinity-slice-right-fibration vs lem-coef-infinity-anodyne-cocones: the existing theorem treats pushout joins and cocone restriction along a right-anodyne inclusion; it states no slice projection theorem. Its proof is not a substitute for that missing statement.

lem-coef-infinity-slice-right-fibration vs lem-coef-infinity-mapping-excision: the existing theorem concerns coherent mapping spaces for a pushout of indexing shapes, with an injective gluing leg; it has no slice projection or right-horn lifting assertion.

lem-coef-infinity-slice-right-fibration vs lem-coef-infinity-pinch-comparison: the existing theorem compares pinched and arrow mapping-space models; it does not construct join slices for arbitrary diagrams or prove their projection lifts right horns.

lem-coef-infinity-slice-right-fibration vs lem-coef-infinity-terminal-anodyne: the parent characterizes right anodyneness of a terminal vertex inclusion; the new theorem is about projection of an arbitrary diagram's join slice, with no finality assumption on a vertex and no normalized cone. Using the parent would be circular.

lem-coef-infinity-slice-equivalence-final vs lem-cbc-enhanced-functor-cone-calculus: the existing general comma mapping-fiber formula does not identify the different join-slice model, or characterize arbitrary equivalence arrows as final objects of that model.

lem-coef-infinity-slice-equivalence-final vs lem-coef-infinity-anodyne-cocones: restriction of cocones along right-anodyne indices supplies no criterion for final objects inside a fixed target slice.

lem-coef-infinity-slice-equivalence-final vs lem-coef-infinity-mapping-excision: pushout-index mapping-space excision supplies no characterization of final vertices in a join slice.

lem-coef-infinity-slice-equivalence-final vs lem-coef-infinity-pinch-comparison: the latter permits comparison of mapping-space models but does not prove contractibility for equivalence arrows regarded as objects in a slice.

lem-coef-infinity-slice-equivalence-final vs lem-coef-infinity-terminal-anodyne: the new theorem characterizes final objects of C over t by equivalences into t, without t being final in C and without any normalized identity cone. The parent is about the inclusion of t in C itself and depends on this item.

lem-coef-right-fibration-contractible-fibers vs lem-coef-infinity-right-fibration-exponentiation: the existing theorem proves a particular internal-hom restriction map trivial Kan by a right-anodyne inclusion hypothesis. The new theorem takes an arbitrary right fibration and tests all its vertex fibers; there is no index inclusion or exponential assumption.

lem-coef-infinity-slice-right-fibration vs lem-coef-infinity-arrow-target-right-fibration: the latter uses unpinched arrows Fun(Delta1,C) at a fixed target. The new result is the different join-slice model, for arbitrary diagram K; the comparison between them is a theorem, not a definitional equality.

lem-coef-infinity-slice-equivalence-final vs lem-coef-infinity-normalized-final-cone: the new statement has no identity extension or section and no finality hypothesis on t in C. Even when t is not final in C, the identity of t is final in its slice. The item's actual converse still requires the two mapping-space maps and their retract equations.

lem-coef-right-fibration-contractible-fibers vs lem-coef-infinity-normalized-final-cone: the new statement applies to arbitrary maps of simplicial sets, with no quasicategory, vertex, cone, or section; the item's construction of the relevant map and section remains in its proof.

## Review by NZ

For the item I read the full proof of 02J4, including its reference to the trivial-Kan slice projection and its reverse mapping-space retract. I also read 06R2 and 06R1 to check that this is the intended route, and read the current blueprint paragraph and unit rather than substituting an unrelated six-functor argument. For the new slice node I read 018F in full and checked its arbitrary small diagram hypothesis; 01KX identifies precisely the right-pinched fibers, and 01L0 supplies the Kan property. For the general fiber criterion I read all of 01NU: its implication (3) to (1) assumes no quasicategory structure on the base. For the equivalence/finality node I read 02J2 and 01L5: the former treats the join slice, and the latter justifies using the project's right-pinched mapping model for finality.

Step 1 uses only the slice node's stated construction, quasicategory, right-fibration and fiber clauses; the right-pinched initial face is the whole face, not merely its vertices. Step 2 uses the entire implication of the fiber criterion; Step 1 and the item's hypothesis supply all its assumptions, including the Kan condition. Step 3 uses the precise statement of the existing Mathlib leaf `lem-weil-pbc-trivial-kan-lifts-monomorphisms`, which I opened; it permits an arbitrary degreewise injection, exactly the inclusion of all constant t-simplices, and returns both strict equations required for the section. I also read Stacks simplicial.tex, definition-trivial-kan and lemma-trivial-kan (08NL and 08NM), and the existing definition and Mathlib `SSet.rlp_monomorphisms` source. Dimension zero is included, so the prescribed identity vertex is not lost.

Step 4 uses the explicitly stated slice simplices and operators, rather than a future proof of the slice node. I wrote the mixed-simplex rule for F and the converse restriction rule for G; the simplicial equations identify faces/degeneracies and the endpoint condition gives exactly the degenerate t-edge. This is a direct construction from the join and slice definitions, marked elementary. Step 5 takes precisely the finality conclusion of the third new node at the identity equivalence, and uses the mapping-simplex definition in `def-cbc-enhanced-diagrams-cones`, which I opened. Postcomposition with G and q gives actual simplicial maps and their composite is literally identity in every degree. Step 6 writes out the elementary retract argument on components and all based homotopy groups using the opened weak-homotopy-equivalence definition. Every node cited in every step has a verbatim matching statement quotation in citations.json; no theorem is inferred merely from a definition node.

I tested the item on a point, the nerve of 0→1 at each endpoint, a discrete two-point nerve, and the one-object nerve of a nontrivial group. Only the final endpoint of 0→1 admits the normalized cone; the discrete two-point example has an empty incoming mapping space; a normalized cone on a nontrivial one-object group would force every automorphism to be identity by naturality, so neither side holds. The empty quasicategory has no chosen vertex and hence is outside the item's hypotheses.

For the new slice theorem, the empty indexing shape gives q=id, and a point target gives a point slice. For a vertex slice of the arrow category, the source projection has the expected right-horn orientation; at t=0 it is the inclusion of 0, not of 1. For the fiber criterion, an empty base satisfies the conclusion vacuously, an empty fiber over a present vertex fails the hypothesis, and a two-point discrete fiber is Kan but not weakly contractible, so cannot be used to infer trivial Kan. For the slice-finality theorem, in the arrow category over 1 the identity is final and 0→1 is not, while in a groupoid every arrow into t is an equivalence and final in the slice. These cases check the hypotheses that a mere nonempty fiber, ordinary homotopy-category terminal object, or arbitrary arrow into t would incorrectly suppress.

Against delivery-errors B–E: all new objects and constructions are introduced in their own statements, theorem facts are separated from their definitions, and all three children remain unsplit. The new nodes contain no identity-cone extension, normalized section or right-anodyne characterization; they are genuine slice/fibration foundations, not clauses of the item under new names. The lifting and retract computations remain in the item. All non-elementary facts have cited nodes, the statement quotations match their uses, and the new dependencies point downward without citing the parent or its consequences. Generic enhanced definitions from another unit are declared in split_report.tool_uses; the existing lifting leaf is a generic Mathlib tool. No top-level tool_uses, units, source checkouts or shared repository files were edited. I corrected the draft Mathlib source line references after obtaining their actual locations from the required grep command.

## Dry run

Validation command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py NZ lem-coef-infinity-normalized-final-cone --no-push`. The command performs the citation, logged-search, duplicate and maintainer preflight checks in its temporary worktree; its terminal output records the result. Handoff as READY requires its final OK. No push is requested.

## Second reading by NZ

I read delivery-errors B–E, GOAL.md and dag-sync.md first, then opened the sandbox nodes and their cited statements. The item agrees hypothesis by hypothesis with [Kerodon 02J4, Corollary 4.7.3.21(1)](https://kerodon.net/tag/02J4): an arbitrary quasicategory with a chosen vertex, a strict section taking that vertex to its identity, and finality expressed using right-pinched spaces. I checked the mapping-space convention against 01KX and 01L5. No statement dispute or statement correction is needed. These tags belong to Kerodon; there is no corresponding Stacks quasicategory assertion to read. I read the applicable local Stacks source `simplicial.tex`, labels `definition-trivial-kan` (08NL) and `lemma-trivial-kan` (08NM), for the boundary-lifting definition and the existing lifting leaf. The current main-20261015 integral-adjoint proof paragraph 2, the recorded unit and chapter retain their route; this is inherited below-unit simplicial infrastructure.

- Step 1: checked the full slice/right-fibration/fiber statement of `lem-coef-infinity-slice-right-fibration` against 018F, 01KX and 01L0; the whole initial face is constant, the horn indices are positive including the last, and the identity edge lies over t. PASS.
- Step 2: checked `lem-coef-right-fibration-contractible-fibers` against 01NU(3) ⇒ (1); Step 1 supplies the right fibration and Kan fibers and the forward hypothesis supplies weak contractibility. Neither J being Kan nor a prior global weak equivalence is needed. PASS.
- Step 3: opened the complete statement and Mathlib match of `lem-weil-pbc-trivial-kan-lifts-monomorphisms`; the singleton simplicial subset is degreewise injective, the square commutes strictly, and the lifting conclusion includes both strict equations. Read `CategoryWithFibrations.lean:127–131` and local Stacks 08NM, `lemma-trivial-kan`; dimension-zero surjectivity is present. PASS.
- Step 4: checked the cited join-slice definition and wrote the exact mixed-simplex map using rho, then checked an arbitrary monotone operator in its mixed, base-only and cone-only cases. The inverse restriction formula also checks simpliciality and the degenerate edge, so this is elementary from the cited construction. PASS after expanding the operator check.
- Step 5: opened `lem-coef-infinity-slice-equivalence-final` and checked 02J2(1) ⇔ (2), with 01L5 for the right-pinched convention; the identity has degenerate inverse triangles. The opened mapping-space definition in `def-cbc-enhanced-diagrams-cones` makes postcomposition by G and q simplicial. Their endpoints and composite follow from G(t)=e and qG=id in every degree; no comparison between different slice models is used. PASS.
- Step 6: opened the realization, components and based-homotopy-group definitions in `def-cbc-enhanced-diagrams-cones`; postcomposition by the realized retraction gives a retraction of the component set and every based homotopy group, as written. This elementary calculation proves weak contractibility even with the project's realization definition. PASS.
- New node `lem-coef-infinity-slice-right-fibration`: compared all clauses with 018F (arbitrary K, quasicategory C, right projection, slice quasicategory), 01KX (degreewise vertex fiber) and 01L0 (Kan). Empty K gives q=id; a point C gives a point slice; C=N(0→1), t=0 gives the right-oriented source projection from the vertex 0. Statement-only, all objects introduced, definitions cited, single TeX escaping, and source tags with exact proposition/construction labels satisfy B1–B7. Not elementary or a clause of the item; no existing node found by tags and join-slice/right-fibration keyword searches in both DAG views. The existing arrow-target node uses the different internal-arrow model; no unstated comparison identifies it with this construction. PASS; retain.
- New node `lem-coef-right-fibration-contractible-fibers`: compared with 01NU(3) ⇒ (1), including arbitrary base and nonempty weakly contractible Kan fibers; empty base is vacuous, empty fibers fail, and two discrete points are Kan but fail contractibility. Statement-only, self-contained horns/fibers, cited definitions, source label and TeX satisfy B1–B7. This non-elementary lifting criterion for arbitrary maps is neither the section/cone criterion nor the existing right-anodyne exponentiation theorem. Both DAG views searched by 01NU and contractible-fiber phrases; no duplicate. PASS; retain.
- New node `lem-coef-infinity-slice-equivalence-final`: compared with 02J2(1) ⇔ (2), 01L5 and 01L0, without assuming t final in C. In N(0→1) over 1, id_1 is final but 0→1 is not; in a groupoid every arrow into t is an equivalence and final in its slice. Statement-only, all endpoints and notions introduced/cited, precise source labels and TeX satisfy B1–B7. This classification of arbitrary slice vertices is not a normalized identity-cone clause or the existing comma-cone calculus; searched both DAG views by 02J2 and slice/finality/equivalence phrases. PASS; retain.

I independently searched the whole imported blueprint using `blueprint_refs.py search` for right fibration, slice and final object: no node states these three foundations. I also searched the two read-only Lean source trees by normalized-final-cone, right-pinched, quasicategory and right-fibration phrases, finding no exact declaration to attach. Fresh required msearch LeanFinder queries used over simplicial set, acyclic fibration/point fibers, and terminal vertices/invertible arrows vocabulary; the original outputs remain in searches.jsonl and their log records are appended to each relevant node. The additional msearch grep of AlgebraicTopology for RightFibration/right_fibration/rightFibration and over/quasicategory combinations returned no hits. I opened the returned Quasicategory horn fillers, all-horn fibration declarations, trivial-fibration definitions and ordinary Over.mkIdTerminal sources: none states the relevant higher-categorical theorem, so no new Mathlib leaf is justified.

For the item I checked the point, the empty quasicategory (no chosen t, so outside the hypotheses), the two endpoints of N(0→1), a discrete two-point category and the nerve of a nontrivial one-object group. The final endpoint alone admits the normalized cone in the arrow example; the missing incoming map obstructs the discrete example; naturality of a cone whose t-component is the identity forces every group element to be the identity. These tests preserve the normalization requirement. No SGA source is used. All citations.json quotations were rechecked verbatim against the repaired node set and the opened existing statements; no cited statement changed, so valid quotations were retained.

Changes made:

- Expanded Step 4 with the explicit rho formula and all three operator cases, replacing an abbreviated compatibility claim (E5).
- Corrected the item's unknown-identifier Loogle result to an invalid-query verdict; it is not absence evidence. Valid independent searches remain recorded.
- Added my independent Mathlib searches and source-based verdicts to all three children and recorded this second reading. No nodes were added or removed and no statements changed.

Second-reader dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py NZ lem-coef-infinity-normalized-final-cone --no-push` printed `OK (not pushed) deliver/NZ/lem-coef-infinity-normalized-final-cone at 8c74d183c7: preflight passed`.
