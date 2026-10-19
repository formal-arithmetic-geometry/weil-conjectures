# Worker report

Files written:

- `dag/nodes/sec-six-functors/lem-coef-cartesian-core-right-fibration.json` — retained the item statement, added a four-step split proof, and recorded the existing-node dependencies; no new nodes and no Mathlib leaves.
- `citations.json` — verbatim statement excerpts for every dependency used by every proof step.
- `report.md` — this review.

Attachments: none. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` for the item id, Cartesian-core terminology, right-fibration terminology, and the relevant HTT-style declaration names. No sorry-free project declaration states this item exactly, and no declaration carries the blueprint tag.

WANTED: an archival copy of Lurie, *Higher Topos Theory*, Proposition 2.4.1.5 and Corollary 2.4.2.5 (printed p. 122), for the Cartesian-core right-fibration theorem. The source URL in the item is available online but the PDF is not archived in `literature/`; the proof therefore has `proof_origin.by = agent` and records the source place precisely.

The imported item was unsplit. I read `dag/chapters/sec-six-functors.json`, the historical unit `dag/units/sk-prop-sf-biduality-general.json`, the current `main-20261015` blueprint ancestor `prop-coef-integral-exceptional-adjoint`, and the complete statements of both statement dependencies. Whole-DAG and whole-blueprint searches for “Cartesian core”, “right fibration”, “fiber core”, “Cartesian transport”, and HTT 2.4.2.5 found no duplicate statement. Existing definitions and lemmas are cited rather than copied.

## Review by Q142

I checked the item statement clause by clause against HTT Corollary 2.4.2.5 and Proposition 2.4.1.5: the hypotheses are a Cartesian fibration between quasicategories in a fixed containing universe; the sub-simplicial set consists of simplices whose edges are Cartesian; the conclusion has all three clauses (right-fibration lifting, fiber core, and transport restriction). No coefficient category or extra nonemptiness assumption was introduced.

Step 1 uses `def-coef-infinity-fibrations` for the precise inner, right, and Cartesian horn ranges, and `lem-coef-marked-opposite-relative-calculus` for the cartesian/cocartesian horn duality. I checked that the right horn has `n ≥ 1, 0 < i ≤ n`, that the prescribed final edge is the Cartesian one, and that Cartesian composition/cancellation keeps every edge of the filler Cartesian. This is the standard outer-horn proof of HTT Corollary 2.4.2.5; no arbitrary outer horn is claimed to lift in the original fibration.

Step 2 uses `lem-coef-cocartesian-local-global` together with the opposite-calculus statement. Its degenerate-base clause says that cocartesian edges over identities are exactly fiber equivalences; reversing simplices gives the corresponding Cartesian assertion. Thus a fiber simplex in the Cartesian core is exactly a simplex all of whose edges are equivalences, namely the maximal Kan subcomplex `(E_b)^≃`. I also checked the Kan and empty-fiber clauses against `lem-coef-infinity-right-fibration-fibers`.

Step 3 uses the Cartesian-fibration lifting clause from `def-coef-infinity-fibrations` to choose a lift with prescribed target. The mapping-fiber statement `lem-coef-infinity-cartesian-mapping-fiber` supplies naturality and the homotopy-fiber interpretation, while `lem-coef-infinity-cocartesian-composition-initiality` supplies the equivalence between any two lifts after dualizing. I verified that this identifies right-fibration transport along `f:b→c` with the restriction of Cartesian pullback `f^*:E_c→E_b`, including coherent composition.

Step 4 records the fixed-universe convention from `def-cbc-enhanced-diagrams-cones` and the permitted empty fibers from `lem-coef-infinity-right-fibration-fibers`. The conclusion is exactly the conjunction asserted by the item, with no hidden size or nonemptiness hypothesis.

I tested the statement on `p = id_B`, on `B = Δ⁰`, on the nerve of an ordinary Grothendieck fibration, on an empty total space, on an identity Cartesian lift, and on a base with an empty mapping space. In each case the Cartesian core and transport clauses specialize correctly. No Lean source was written or compiled, as required for stage 1.

## Not duplicates

No new node was created, so there are no new-node duplicate pairs. The existing nodes `def-coef-infinity-fibrations`, `lem-coef-cocartesian-local-global`, and `lem-coef-infinity-cartesian-mapping-fiber` are broader infrastructure statements and do not state the Cartesian-core right-fibration conclusion.

What remains unfinished: nothing in this stage-1 split; delivery is pending the mandated dry run.
