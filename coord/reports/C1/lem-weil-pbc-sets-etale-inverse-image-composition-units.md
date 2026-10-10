# Worker report: lem-weil-pbc-sets-etale-inverse-image-composition-units

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-sets-etale-inverse-image-composition-units.json`: split into five proof steps; no new nodes. The prior LeanSearch, LeanFinder, Loogle and Mathlib source searches rule out an exact sheaf-of-sets Mathlib leaf.
- This report.

## Attachments

None. Read-only `grep -rn 'lem-weil-pbc-sets-etale-inverse-image-composition-units' /home/ubuntu/weil-src-slopmaster2/WeilConjectures/` found no exact tagged declaration. Concept searches found `AlgebraicGeometry.Etale.upperStarComp` at `WeilConjectures/SixFunctors/Etale/UpperLowerStar/Defs.lean:325`, `Etale.upperStarComp_hom_app_unit_app` at `.../Coherence.lean:163`, and `Etale.upperStarComp_assoc` at `.../Coherence.lean:265`. Their shared parameter `A` has `[Abelian A] [IsGrothendieckAbelian A]`, so these do not state a theorem for sheaves of sets. The committed `local/sorry_map_slopmaster2_71d63dcf.jsonl.gz` records each of these three declarations with `s=false, ts=false` (no direct or reachable sorry), but none belongs to this node.

## Sources and route

Read the assigned node, `dag/chapters/sec-proper-base-change.json`, `dag/units/sk-thm-iff.json`, its cited definition and lemma nodes, and the parent `lem-weil-pbc-gabber-h0-etale-criterion`. Read the original source at `/tmp/c1-lead-current/literature/stacks-project/sites.tex`: Lemma Tag 03CB, label `lemma-composition-morphisms-sites`, line 2764, and Definition Tag 03CC, label `definition-composition-morphisms-sites`, line 2786; Topologies Tags 021I (`lemma-morphism-big-small-etale`, line 1176) and 021J (`lemma-composition-etale`, line 1250); Sites Tags 00WB (`theorem-plus`, line 1975) and 00WK (`lemma-sections-sheafification`, line 2156); and `etale-cohomology.tex` Tag 09ZF, third paragraph at line 15021, where the section compatibility is left to the reader. The node serves that omitted compatibility in the parent proof. No WANTED document.

The steps compute the unit as the identity-indexed coprojection followed by sheafification; construct the direct-image comparison from the universal property of iterated fibre products; obtain the inverse-image comparison from the composite adjunction and uniqueness of adjoints; show objectwise uniqueness from local representatives of the two sheafifications; and prove associativity by calculating both composites on those representatives. This retains the `sk-thm-iff` unit route to Tag 09ZF through the parent Gabber criterion.

The proof initially cited `lem-weil-pbc-site-morphism-composition` (`sk-thm-p1`), whose statement is the general site-theoretic Tag 03CB result. It is a generic tool, but the citation was redundant because Step 3 proves the required special case directly from `def-weil-pbc-composite-adjunction` and `lem-weil-pbc-conjugate-iso-unit-equation`; I removed it. The remaining `lem-weil-pbc-site-sheafification-sections-local` (`sk-thm-p1`) states Tag 00WK for *any site and presheaf of sets*, with no PBC hypotheses. Steps 4-5 specialize it to the presheaf defining etale inverse image, so this is a generic tool used as a black box. It supplies exactly the local-representation fact needed for objectwise uniqueness, without replacing a step of the `sk-thm-iff` unit's proof. The lead accepted this cross-unit tool use and instructed me to record only this id in `tool_uses`.

## Checks and findings

- `python3 -m json.tool` passed.
- `python3 tools/review_split.py lem-weil-pbc-sets-etale-inverse-image-composition-units` passes after the lead accepted `lem-weil-pbc-site-sheafification-sections-local` as a generic cross-unit tool.
- `python3 tools/check_dag.py` reports 4514 nodes, 0 cycles and 0 self-loops; its 7 reach and 11 route warnings are on other nodes already present at this base.
- Searched the DAG and blueprint index by composition, inverse image, and Tag 03CB; no blueprint node states this sheaf-of-sets unit/coherence result. No new node was needed.
- The source leaves unit and associativity calculations implicit. The original node's statement is mathematically consistent, including the identity and empty-object cases; no statement change was needed. No Lean files were written or built.

## Unfinished

None in the worker's assigned split. The lead's mathematical review and delivery remain separate.

## Review by C1

I read the assigned node's unchanged clauses against pinned Stacks `sites.tex` Lemma 03CB (`lemma-composition-morphisms-sites`) and Definition 03CC (`definition-composition-morphisms-sites`), and the small-etale base-change compatibility in Topologies 021I/021J. Stacks identifies the composite inverse-image functor via left adjoints but leaves the fixed-sheaf unit and associativity calculations implicit; the five steps make those calculations explicit. The source's site and sheaf hypotheses are met by the cited etale-site and sheaf-of-sets nodes. The slopmaster2 declarations found by the worker have abelian coefficient categories, so none is an exact attachment to this sets statement. There are no new nodes, and the worker's DAG/blueprint search found no duplicate.

In step 1 I opened `lem-weil-pbc-etale-inverse-image-algebraic-structures`: it states inverse image as sheafified presheaf pullback and its adjunction. The identity-indexed coprojection followed by sheafification gives the described unit, while naturality supplies the two equations. Step 2 uses the fibre-product universal property in `def-pc-fibre-product`, pasting in `lem-weil-pbc-cartesian-square-pasting`, and etale base change to give the direct-image comparison; equality on both projections proves its naturality and triple associativity. Step 3 uses the formula for the composite unit in `def-weil-pbc-composite-adjunction` and the unique conjugate isomorphism from `lem-weil-pbc-conjugate-iso-unit-equation`. The cited statements say exactly the needed unit equation; evaluating it on a section gives clause (1).

For step 4 I read Stacks Sites Theorem 00WB and Lemma 00WK in `sites.tex` and the statement of `lem-weil-pbc-site-sheafification-sections-local`. It says every section of a sheafification is locally represented by a presheaf section, and gives local equality and gluing for such representations. Applying it successively to the two inverse images proves the fixed-object uniqueness from the unit equation, rather than merely natural-transformation uniqueness. Step 5 evaluates both parenthesized composites on the same locally generating sections; step 2's unique fibre-product comparison identifies their target sections, and step 4's local uniqueness then gives equality of sheaf maps. This also covers identity arrows and empty objects without extra assumptions.

I accepted `lem-weil-pbc-site-sheafification-sections-local` as a generic cross-unit tool and sent the worker back to record it in `tool_uses`; its statement is for any site and presheaf of sets, so it supplies a local sheafification fact and does not replace this unit's etale route. The worker removed a redundant cross-unit site-composition citation. I checked the final proof and report against delivery-errors A-F, including the five step citations, hypotheses, and absence of a cycle.
