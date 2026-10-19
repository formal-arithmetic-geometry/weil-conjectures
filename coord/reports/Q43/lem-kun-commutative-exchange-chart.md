# Stage-1 report: lem-kun-commutative-exchange-chart

## Files written

- dag/nodes/sec-smooth-purity/lem-kun-commutative-exchange-chart.json: statement, split; no Mathlib match. Audited and retained the six-step argument already present in the unsplit input; refreshed search records and proof-origin description, removed four statement dependencies belonging to the later Lean presentation rather than the natural-language statement.
- citations.json: one verbatim statement excerpt for every node used by every proof step (36 entries).
- No new DAG nodes and no new Mathlib leaves. No unit record changed: the item is a supporting chart lemma, not the unit key statement.

## Attachments

None. Searches for the exact blueprint id and the exchange/chart/cohomology-presheaf concepts in the read-only slopmaster2 project found no project declaration stating all clauses. The upstream master and the metadata's later-stage Lean signature are reference material, not proof of a finished slopmaster2 declaration. The item has lean_audit.slopmaster2.state = none.

## WANTED

None. The relevant Stacks sources are available in literature/stacks-project. I did not download literature, write Lean, or run a compiler, Lake, git, or any local DAG checker.

## Problems and corrections

The input is status unsplit but already contains a six-step resolution proof from the earlier split, plus stage-2 and review metadata. I read the proof rather than treating that metadata as acceptance. Its mathematical statement needs no correction and is unchanged. I removed def-sc-raw-restricted-cohomology-class, def-sbc-raw-affine-restricted-cohomology, lem-sbc-abelian-higher-direct-image-class-compatibility and lem-sbc-abelian-higher-direct-image-natural-comparison from stmt_deps: none is a notion or assertion used in the natural-language statement. I preserved all maintainer-owned metadata, including its unit and tool_uses.

The old proof_origin mentioned a literature mirror and the old split report claimed absent sources; I replaced those historical claims with this reading of the actual repository .tex files. The canonical map is always the degree-q mate in the statement; no invertibility of the underived mate and no cartesianness is inferred.

## Not duplicates

No new nodes were created. Whole-blueprint searches for commutative exchange chart, exchange, and cohomology pullback, and DAG searches by 0736 and the chart/cohomology-presheaf concepts found no same-statement blueprint node. In particular lem-kun-bc-map-on-cohomology and lem-weil-pbc-derived-exchange-termwise assume a cartesian square; they do not replace this lemma for an arbitrary commutative square. same_as remains []. No clause is moved into a fresh node.

## Review by Q43

I read the stage-1 contract, worker role, SETUP requirements and three levels, GOAL, dag-sync and delivery-errors B through E. I read the chapter record sec-smooth-purity and the actual current unit sk-lem-kun-relative-continuity (not the historical ancestor's sk-prop-sf-kunneth-ordinary route). The item realizes the chart-compatibility invocation in current unit steps 2 and 5. I read the master and main-20261015 ancestor lem-kun-0ezt statement/proof: its sole paragraph invokes 0EYM/0EZT. This split expands the comparison maps in that invocation and preserves the assigned route.

For the item's source I read sites-cohomology.tex: lemma-base-change-map-flat-case (0736, lines 2427ff), lemma-adjoint (07A6, 3990ff), remark-base-change (07A7, 4033ff), and lemma-cohomology-of-open (03F3, 608ff); etale-cohomology.tex: lemma-higher-direct-images (03Q8, 7510ff) and section-extension-by-zero (03S2, 11353ff); and sites.tex: lemma-composition-morphisms-sites (03CB, 2764ff). The labels were checked against tags/tags. These sources give commutative-topos exchange, its adjoint description, the restriction calculation and sheafified cohomology presheaf. The additional algebra in the proof is explicitly written out, so proof_origin is agent. There is no SGA route.

Step 1: I opened the statements of lem-weil-pbc-module-sheaves-enough-injectives, lem-weil-pbc-dplus-injective-representative and lem-weil-pbc-kinjective-hom-derived. The first explicitly includes abelian sheaves; the second supplies bounded-below injective representatives and their K-injectivity; the third lifts derived classes to chain maps. Together with prop-weil-pbc-inverse-image-exact and lem-weil-pbc-exact-functor-complex-cohomology, they ensure that j is a quasi-isomorphism and that the pulled coefficient is resolved. def-weil-pbc-direct-image explicitly computes the derived functor on these representatives. All complexes are bounded below. Injectivity of g' inverse image is never assumed.

Step 2: I opened def-kun-commutative-derived-exchange, def-weil-pbc-adjunction-mate, prop-weil-pbc-derived-inverse-image-adjunction, lem-weil-pbc-derived-inverse-image-composition, def-weil-pbc-inverse-image and def-weil-pbc-derived-inverse-image. The first two give exactly the mate/transpose used here. The derived adjunction statement has the termwise counit at I and J, and the composition statement has the termwise derived-square comparison; these are statement clauses, not hidden proofs. The displayed transpose calculation uses counit naturality and the triangle identity. It identifies Q(e) with the specified exchange, not just a morphism with the same endpoints.

Step 3: I opened def-weil-pbc-adjunction-mate, def-weil-pbc-inverse-image, def-weil-pbc-direct-image, lem-weil-pbc-inverse-image-composition, lem-weil-pbc-etale-inverse-image-restriction and def-pc-fibre-product. Composition clause (2) states the unit-compatible equation used to compare the two composites, and clause (1) gives the direct-image comparison d. The four displayed equalities have targets SR'HB and follow in order from this unit formula, naturality of d, naturality of the g' unit, and the f triangle identity. The fibre-product universal property gives T' = X' times_X T even when the original square is not cartesian: both are X' times_Y U. Restriction clause (2), which explicitly identifies the etale adjunction unit, identifies the chart-section formula. No underived exchange isomorphism is needed.

Step 4: I opened lem-weil-pbc-etale-base-change-finite-limits, lem-weil-pbc-etale-inverse-image-restriction and lem-weil-pbc-etale-restriction-injectives. U' is etale over Y' by base change; p and p' are etale by the same statement. Restriction preserves injectives by the cited node for the constant ring Z, giving the abelian case. prop-weil-pbc-inverse-image-exact, lem-weil-pbc-dplus-injective-representative, def-weil-pbc-etale-cohomology and def-weil-pbc-cohomology-pullback give exactly the section-complex computation and chain-map formula w. Only p and p' preserve injectives; t and g' remain arbitrary.

Step 5: I opened sbc-lem-higher-direct-image-presheaf, lem-weil-pbc-exact-functor-complex-cohomology, def-weil-pbc-inverse-image and def-weil-pbc-direct-image. The presheaf lemma states sheafification, not equality of its raw cohomology groups with sheaf sections; the proof uses only the canonical map. The exact-functor statement explicitly preserves cycle inclusions and quotient projections, which is precisely what is needed for the section-unit passage. A raw class has a global cycle in the section complex I(T); no arbitrary cohomology-sheaf section is given a global cycle. e sends this cycle to the w cycle computed above, and chain maps preserve boundaries, proving the quotient equality.

Step 6: I opened def-pc-fibre-product, lem-weil-pbc-kinjective-hom-derived, lem-weil-pbc-cohomology-pullback-functorial, lem-weil-pbc-derived-inverse-image-composition, lem-weil-pbc-exact-functor-complex-cohomology, def-weil-pbc-inverse-image and def-weil-pbc-direct-image. The Hom bijection needs only the target J-tilde to be K-injective; after cancellation of Q(g' inverse image s), it supplies exactly the homotopy between the two comparisons. Evaluation and additive functors preserve the explicit homotopy equation. The morphism clause of direct image computes coefficient maps. Pullback-functorial clauses (1), (3), (4) identify these with the canonical maps and prove both naturalities. Thus no unexplained “compatibility with connecting maps” is hidden.

I checked the B–E failure modes individually: all needed objects and hypotheses occur in the unchanged self-contained statement; TeX remains in the JSON strings correctly; every non-elementary step cites actual statements and every such citation has a verbatim quote in citations.json; proof_deps is exactly the union of uses; no nodes restate the item, no new unsplit node contains a proof, no cartesian theorem is substituted for a merely commutative one, and no added coefficient/torsion/qcqs/finite-type assumption enters. Off-unit generic tools are declared in split_report.tool_uses as already present in the input.

Small cases checked: q=0 reduces to the computed underived section formula; F=0 makes every group/map zero; empty charts have zero section complexes; identity squares reduce the equation to theta followed by the ordinary unit/restriction identifications; noncartesian commutative squares still satisfy T' = X' times_X T by their common maps to Y. No new statement needs an edge-case audit, since there are no new nodes.

The actual msearch log records the executed Mathlib queries, including a second semantic phrasing. I read Mathlib CategoryTheory/Sites/SheafCohomology/Basic.lean at cohomologyPresheafFunctor/cohomologyPresheaf (lines 72 and 81), which defines an Ext presheaf rather than this comparison; the returned pullback adjunctions and scheme pullback diagrams also do not state it. The Loogle response reports an unknown identifier for CategoryTheory.Sheaf.pullbackIso and is recorded as such, not as a match. The leansearch service answered this time; its old unavailable result was replaced by this actual run.

## Unfinished work

None in this stage-1 split. No delivery/push is authorized; the sandbox is for a fresh second reader after successful dry run.

## Earlier second reading (a previous round; superseded)

I reopened the item statement and its source at Stacks Tag 0736, `lemma-base-change-map-flat-case`, together with Tag 07A7, `remark-base-change`, and Tag 03Q8, `lemma-higher-direct-images`; the arbitrary commutative square, abelian coefficient, bounded-below derived functors, chart fibre products, degree-q map, and both naturality clauses agree hypothesis by hypothesis. The flatness assumptions in Tag 0736 concern the ringed topoi with constant integer structure sheaf: the inverse images here are exact, so no flatness of scheme morphisms is required. I tested the zero coefficient, q=0, identity square, and empty chart. For a concrete non-cartesian field example, take X=Y=Y'=Spec(k), f=g=id, X'=Spec(L) for a nontrivial field extension L/k, and f'=g' the structure map; with U=Spec(k), the asserted equality is the cohomology pullback to Spec(L), exactly the unit-defined map on both sides. No clause changes.

Step 1 was checked against the statements of `lem-weil-pbc-module-sheaves-enough-injectives`, `lem-weil-pbc-dplus-injective-representative`, `lem-weil-pbc-kinjective-hom-derived`, `prop-weil-pbc-inverse-image-exact`, `lem-weil-pbc-exact-functor-complex-cohomology`, and `def-weil-pbc-direct-image`; each supplies the claimed resolution fact, and the step does not assume inverse-image preservation of injectives.

Step 2 was checked against `def-kun-commutative-derived-exchange`, `def-weil-pbc-adjunction-mate`, `prop-weil-pbc-derived-inverse-image-adjunction`, `lem-weil-pbc-derived-inverse-image-composition`, `def-weil-pbc-inverse-image`, and `def-weil-pbc-derived-inverse-image`; the transpose calculation identifies the specified mate, including the counit and triangle identity.

Step 3 was checked against `def-weil-pbc-adjunction-mate`, `def-weil-pbc-inverse-image`, `def-weil-pbc-direct-image`, `lem-weil-pbc-inverse-image-composition`, `lem-weil-pbc-etale-inverse-image-restriction`, and `def-pc-fibre-product`; the displayed unit/naturality calculation gives the exact chart section formula, and the fibre-product identifications hold without cartesianness.

Step 4 was checked against `lem-weil-pbc-etale-base-change-finite-limits`, `lem-weil-pbc-etale-inverse-image-restriction`, `lem-weil-pbc-etale-restriction-injectives`, `prop-weil-pbc-inverse-image-exact`, `lem-weil-pbc-dplus-injective-representative`, `def-weil-pbc-etale-cohomology`, and `def-weil-pbc-cohomology-pullback`; only the etale projections are used to preserve injectives, while t and g' remain arbitrary.

Step 5 was checked against `sbc-lem-higher-direct-image-presheaf`, `lem-weil-pbc-exact-functor-complex-cohomology`, `def-weil-pbc-inverse-image`, and `def-weil-pbc-direct-image`; the cycle and boundary quotient argument uses the sheafification map correctly and does not claim arbitrary cohomology-sheaf sections have global cycle representatives.

Step 6 was checked against `def-pc-fibre-product`, `lem-weil-pbc-kinjective-hom-derived`, `lem-weil-pbc-cohomology-pullback-functorial`, `lem-weil-pbc-derived-inverse-image-composition`, `lem-weil-pbc-exact-functor-complex-cohomology`, `def-weil-pbc-inverse-image`, and `def-weil-pbc-direct-image`; the homotopy, coefficient, test-object, and resolution-choice naturalities are explicitly supplied, with no hidden “similarly” step.

There are no new nodes to audit under B1–B7. The item is the only changed DAG node; all 21 proof dependencies already exist, and `citations.json` contains a verbatim statement excerpt for every cited node in every step. Existing-node and blueprint searches found no duplicate or reusable Mathlib declaration for this chart compatibility. I changed no mathematical statements, proof text, or dependencies; the citation excerpts remain valid unchanged.

Changes and reasons:

- Corrected Step 5's source document to `etale-cohomology.tex`: Tag 03Q8 is not in `sites-cohomology.tex`.
- Classified the unknown-identifier Loogle result as inconclusive: a rejected query supplies no absence result.
- Appended my independently run LeanFinder and grep searches with their actual results, and recorded this step-by-step second reading.

 The LeanFinder query about mates and higher sheaf cohomology returned underived pullback/composition and section-restriction identities; the grep returned only cohomology-presheaf maps in Mayer–Vietoris. Neither supplies the item. The earlier delivery authorization is historical; the current repair brief authorizes a dry run and handoff only.


## Returned finding B3 repaired by Q43 (2026-10-17)

I compared the retained sandbox item with the current shared repository snapshot without running git. The shared item still has 20 statement dependencies; the repaired item has 16. The four removed entries are exactly def-sc-raw-restricted-cohomology-class, def-sbc-raw-affine-restricted-cohomology, lem-sbc-abelian-higher-direct-image-class-compatibility, and lem-sbc-abelian-higher-direct-image-natural-comparison. They describe the later Lean presentation and do not occur in the natural-language statement. I retained this already-present repair and made the split-report summary record the returned finding explicitly.

I reread the actual statement of sbc-lem-higher-direct-image-presheaf: it identifies R^q h_*F with the sheaf associated to U ↦ H^q(U ×_X Y,F restricted there). The displayed theta maps are precisely the canonical associated-sheaf maps, so that existing statement is the appropriate dependency. The proof uses its canonical map in Step 5 and never identifies a raw cohomology group with the entire group of sheaf sections. None of the four removed nodes is cited by a proof step.

I reopened Stacks sites-cohomology.tex, lemma-base-change-map-flat-case (0736) and remark-base-change (07A7), and etale-cohomology.tex, lemma-higher-direct-images (03Q8). The first gives the injective-resolution exchange construction; the second gives exactly its counit-adjoint mate; the last supplies the cohomology-presheaf sheafification. The retained explicit transpose and unit calculation fits these sources for a merely commutative square and abelian sheaves (constant integer coefficients); neither cartesianness nor flatness of scheme morphisms is introduced. This confirms the returned review's accepted resolution/mate route.

The statement is byte-for-byte unchanged from the shared snapshot. All six steps retain their mathematical argument. I checked every citation against the current cited node statement: all 36 excerpts are verbatim, cover every step/node pair, and the 21 proof dependencies are exactly the union of the steps' uses. No new node, Mathlib leaf, unit change or Lean change is part of this repair. At q=0 the chart map is the underived unit computation; zero coefficients and empty charts give zero maps, and the fibre-product identity remains valid for noncartesian squares. The B3 repair changes dependency bookkeeping alone. No compiler or Lake command is authorized or run in this stage.

## Second reading by Q43

Step 1 checked against Tags 0736/07A6 and the six cited resolution, exactness, K-injective, and direct-image statements; verdict: bounded-below injective resolutions and the pulled resolution are justified without assuming that inverse image preserves injectives.

Step 2 checked against the derived exchange, mate, adjunction, composition, inverse-image, and derived-inverse-image statements; verdict: the transpose calculation identifies the specified mate, including counit and triangle identities.

Step 3 checked against the mate, inverse/direct-image, inverse-image-composition, etale restriction, fibre-product statements and Tags 0736/03CB/03S2; verdict: the displayed unit/naturality calculation gives the section map, and the fibre-product identification does not require cartesianness.

Step 4 checked against etale finite-limit base change, restriction, restriction-injectives, exactness, injective representatives, etale cohomology, and pullback definitions; verdict: only the etale chart projections are used to preserve injectives, while the arbitrary maps remain unrestricted.

Step 5 checked against Tag 03Q8 and the exact-functor, inverse-image, and direct-image statements; verdict: the argument uses the canonical sheafification map and a genuine cycle representative in the section complex, with no claim about arbitrary cohomology-sheaf sections.

Step 6 checked against fibre products, K-injective Hom, pullback functoriality, inverse-image composition, exact cohomology comparison, inverse image, and direct image; verdict: the homotopy and coefficient/test-object naturality calculations are explicit and the cited clauses identify the canonical maps.

There are no new nodes in this split. The item statement was checked against the current Stacks sources at Tags 0736, 07A6, 07A7, 03F3, 03Q8, 03S2, and 03CB; hypotheses, the non-cartesian square, degree-q map, and both naturality clauses agree. Edge cases checked were zero coefficients, q=0, empty charts, identity squares, and a non-cartesian field-extension square. The 36 citation excerpts were rechecked verbatim against the cited node statements, and proof_deps equals the union of all step uses. No mathematical or statement change was needed; the only retained repair is the removal of four later Lean-presentation dependencies already documented under the returned-finding section.
