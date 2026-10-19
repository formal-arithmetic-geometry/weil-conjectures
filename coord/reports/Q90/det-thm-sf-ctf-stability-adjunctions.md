# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors-basics/det-thm-sf-ctf-stability-adjunctions.json`: split item; zero new nodes and zero Mathlib leaves. Added the missing ambient-adjunction dependencies and completed the restriction argument.
- `citations.json`: exact quotations for every cited node used by step 1.
- `searches.jsonl`: the required LeanFinder, Loogle, grep and LeanSearch records for the item.

No Lean file was written and no compiler, Lake, build, or git command was run.

## Attachments

None. I searched both `/home/ubuntu/weil-newtargets-master/WeilConjectures` and `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its blueprint tag, `Dctf`/`constructibleFiniteTor`, restricted-adjunction terminology, and the relevant adjunction names. There is no sorry-free project declaration stating all three clauses. Nearby declarations such as `AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction` concern ambient derived categories and do not state this restricted `Dctf` theorem; declarations with a different bounded-constructible predicate are not attachments.

## WANTED:

None. The proof follows the current blueprint and uses existing DAG statements; no external source was needed beyond the blueprint proof file.

## Source and DAG audit

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `roles/worker.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, and delivery-errors sections B–E. I read the current item, its chapter `sec-six-functors-basics`, unit `sk-thm-sf-ctf-stability`, and the main-20261015 statement and proof files for `det-thm-sf-ctf-stability-adjunctions`.

The item has one proof paragraph. Its categorical premise is: an adjunction restricts to full subcategories when both functors preserve the chosen objects, with the same Hom bijections, unit, and counit. The preservation hypotheses come from `det-thm-sf-ctf-stability-direct-images` (which states preservation of (f^*, Rf_*, Rf_!, f^!), and derived tensor) and `det-thm-sf-ctf-stability-internal-hom` (which states preservation of internal Hom). The ambient pullback–pushforward adjunction is supplied by `def-sfb-module-derived-pushpull-adjunction`; its (Lf^*) is the (f^*) notation used by this item. The ambient tensor–Hom adjunction is supplied by `sk-def-sfb-derived-tensor-hom`. The exceptional ambient adjunction on the localizing closures is supplied by `sk-prop-sf-existence`. The proof step cites all five statements, and `proof_deps` is exactly the union of its `uses`.

I searched the whole DAG and blueprint before considering new nodes. Existing nodes `def-sfb-dc-upper-lower-adjunction` and `def-sfb-dc-tensor-hom-adjunction` concern the different bounded-constructible (D_{\mathrm{cons}}) predicate and do not state the finite-Tor `Dctf` result, so they are not duplicates or attachments. No new node is needed: the step is the one-level formal restriction argument, while all geometric preservation and ambient adjunction inputs already exist.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Review by Q90

I checked the item against the exact main-20261015 statement and proof and verified that its hypotheses are unchanged: admissible coefficients, separated finite-type (f:X\to Y), the full `Dctf` subcategories, and the localizing categories in the exceptional clause. I opened each cited node rather than relying on its id. `det-thm-sf-ctf-stability-direct-images` explicitly gives the four direct-image/pullback preservation facts and tensor closure; `det-thm-sf-ctf-stability-internal-hom` explicitly gives internal-Hom closure for `Dctf` objects. `def-sfb-module-derived-pushpull-adjunction` states the total derived (Lf^*\dashv Rf_*) adjunction, and the proof records that the item's (f^*) is this derived pullback notation. `sk-def-sfb-derived-tensor-hom` states the derived tensor–internal-Hom adjunction in the closed derived category. `sk-prop-sf-existence` states the exact (Rf_!\dashv f^!) adjunction on `Loc(Dctf)` with its Hom bijection. Every quotation in `citations.json` is an exact substring of the corresponding current statement.

For the sole step, I checked that the full-subcategory argument only transports the ambient Hom bijections after the cited preservation facts have put both outputs back in `Dctf`; fullness then identifies ambient and restricted Hom sets, and the same unit/counit satisfy the triangle identities. I checked the three applications separately: pullback/pushforward on the pro-étale derived categories, tensor/internal Hom with (K\in Dctf(X,\Lambda)), and exceptional lower-shriek/upper-shriek on the localizing closures. I also checked the coefficient-category and source/target scheme hypotheses against the cited statements. The original imported proof omitted the ambient-adjunction citation and had only the two preservation nodes in `proof_deps`; I corrected both the proof text and dependencies. The item's `blueprint` ancestry remains the imported blueprint node with `same_as: []`, and the split report records the three generic tool uses.

## What remains

No mathematical gap remains in this one-level split. A fresh second worker must read the sandbox, run the required no-push dry run, and deliver it; this worker does not push.

## Second reading by Q90

- Item statement: checked every clause and hypothesis against `sk-thm-sf-ctf-stability-adjunctions.md`; the admissible coefficient, separated finite-type morphism, three restricted adjunctions, and the localizing exceptional category all agree.
- Step 1: checked the full-subcategory restriction argument against the five cited statements; direct-images supplies pullback, tensor, both direct images, and exceptional pullback, internal-hom supplies internal-Hom closure, the derived push-pull node supplies `Lf^* \dashv Rf_*`, the tensor-Hom node supplies the ambient tensor adjunction, and `sk-prop-sf-existence` supplies the localizing `Rf_! \dashv f^!` adjunction. Fullness identifies the ambient Hom sets, and the same unit/counit satisfy the triangles.
- New nodes: none; therefore B1–B7, source-tag checks, duplicate checks, and Mathlib-leaf checks have no new-node cases. The existing-node search found only the bounded-constructible restriction statements, whose coefficient range and exceptional adjunction differ from this finite-Tor statement.
- Edge cases: the restriction argument remains valid for the zero objects, the identity morphism, a field coefficient, the empty scheme (zero categories), and tensoring with the zero object.
- Changes: none. The worker's ambient-adjunction dependencies, proof text, exact citation quotations, and search records are correct and no source or DAG repair is needed.
