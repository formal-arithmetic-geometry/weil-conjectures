# Stage-1 report: det-proper-unbounded-window-bounded-below

## Files written

- `dag/nodes/sec-six-functors-basics/det-proper-unbounded-window-bounded-below.json` — item split into five proof steps; no new nodes.
- `citations.json` — verbatim statement quotes for every cited node in every step.

## Attachments

None. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` states this item exactly.

## WANTED

None.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Review by Q20

I read the item source and proof in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-proper-unbounded-window/sk-lem-proper-unbounded-window-bounded-below.proof.md`, the unit route in `dag/units/sk-lem-proper-unbounded-window.json`, and the chapter record. I checked the Lean source tree for the item tag and for declarations about the proper bounded-below window; no exact finished declaration exists.

Step 1 uses `thm-sp-truncation-e2`. Its statement supplies exactly the truncation hypercohomology E2 page, convergence, and finite abutment filtration used here. Step 2 uses `sk-lem-proper-heart-bound`; I verified its statement gives both vanishing above `2d+1` and ind-constructibility of every nonnegative direct-image cohomology sheaf for an ind-constructible input. Step 3 uses the spectral-sequence page structure from `thm-sp-truncation-e2` and the kernel/cokernel closure stated by `det-ind-heart-kernels-cokernels`; the page recursion is written explicitly as kernels and quotients, with images expressed through cokernels. Step 4 uses the finite filtration supplied by `thm-sp-truncation-e2` and the exact-extension closure in `det-ind-heart-extensions`, whose hypotheses match the ambient pro-étale module category. Step 5 reuses the spectral-sequence convergence and the `2d+1` column bound to spell out both amplitude deductions.

The imported proof had an unclassified amplitude step and referred to the aggregate proposition `sk-prop-ind-heart`, which has no node file. I replaced that reference with the existing kernel/cokernel and extension nodes, declared them (and the generic spectral-sequence node) as tool uses for this unit, and added source locations to every step. I ran the required Mathlib searches for the item (LeanFinder, Loogle, grep, and LeanSearch); they found only generic truncation/proper-map declarations and no matching theorem. Every citation quote in `citations.json` was copied verbatim from the cited node statement.

## Source error

None found.

## Could not finish

Nothing remains for this split; the dry run is the remaining mechanical check.

## Second reading by Q20

I compared the item's statement verbatim with the main-20261015 bounded-below `.md` and read its separate `.proof.md`, the proper-unbounded-window unit and the six-functors-basics chapter. The coefficient choices, properness, fibre-dimension bound, bounded-below hypothesis, all-degree ind-constructibility, and both amplitude conclusions agree. No statement change or new node is needed.

- Step 1: checked `thm-sp-truncation-e2`, especially its Grothendieck-category and K-injective hypotheses and clauses (2), (3), (5), (6); repaired the previously uncited ambient hypotheses using `lem-pur-ringed-site-grothendieck-abelian`, `def-sfb-module-lower-star`, and `sk-def-sfb-module-derived-pushpull`. Read the latter two main-20261015 source files and Stacks `sites-cohomology.tex`, Tag 07A5, label `section-unbounded`, together with `sites-modules.tex`, Tags 03DA/03DB, labels `lemma-abelian`/`lemma-limits-colimits`. The tensor-action/sheaf-module identification and replacement by canonical truncation are elementary; the finite filtration and graded identifications are conclusions of the cited theorem. Verdict: valid, including a negative lower bound.
- Step 2: checked `sk-lem-proper-heart-bound` against its main-20261015 `_section.md`; its statement gives precisely the required higher direct-image vanishing for u > 2d+1 and ind-constructibility for u >= 0, with the same coefficients, proper morphism and fibre bound. The input cohomology condition is the definition of Dic. Verdict: retain.
- Step 3: checked the kernel/cokernel closure statement against `sk-prop-ind-heart-kernels-cokernels.md` and the spectral-sequence recursion against `def-sp-exact-couple`; also read Stacks homology Tags 011Q/011R/011S, labels `definition-exact-couple`, `lemma-derived-exact-couple`, `definition-spectral-sequence-associated-exact-couple`. The incoming image is a kernel of a cokernel, the next page is the cokernel of its inclusion into the outgoing kernel, and all these are maps between objects of the full ind-constructible subcategory. Added a finite stabilization argument using the (r,1-r) bidegree from `thm-sp-truncation-e2`, instead of silently passing a finite-page induction to E-infinity. Verdict: repaired.
- Step 4: checked the actual short-exact-sequence assertion in `det-ind-heart-extensions` against `sk-prop-ind-heart-extensions.md` and the finite decreasing filtration in clauses (5), (6) of `thm-sp-truncation-e2`. Wrote the induction from F^N = 0 down to F^0 and each short exact sequence; zero is constructible. Verdict: repaired the previously implicit base and direction of induction.
- Step 5: checked the total-degree inequalities against the source proof's amplitude paragraph and the quadrant/column bounds of the two cited statements. For n < a, v = n-u < a; for n > b+2d+1, every possible u gives v > b. Wrote out preservation of zeros through pages and descent through the finite filtration separately for both cases, and marked this few-line deduction elementary. Verdict: repaired.
- New nodes: none; B1–B7 and the new-node duplicate/leaf checks are vacuous. All added dependencies are existing nodes, not restatements of this item. Traversing their statement/proof dependencies found no path back to the item.

Small-case checks: K = 0 gives zero on every page and on the abutment; X empty has the same result (and the stabilization proof permits an empty column interval). For the identity of Spec(k), d = 0, the only actual direct-image column is u = 0, so K concentrated in degree 0 or 1 remains in that degree, within the asserted bounds. A complex concentrated in degree -1 checks that the lower-bound argument cannot assume v >= 0. At n = 0 and n = 1 the support inequalities and finite-filtration induction have no exceptional boundary case. Both E and Qlbar coefficients meet the hypotheses of each heart-closure node.

Changes: made the spectral-sequence ambient hypotheses explicit with existing citations; replaced the inaccurate unshifted “first-quadrant” description by u >= 0, v >= a0; supplied the finite E-infinity stabilization and both finite-filtration inductions; retained the correct statement and Step 2; regenerated citations.json with one verbatim excerpt per citation covering the clauses used. The first worker's review and sections above remain intact.

I independently ran msearch.py with a more general right-derived-functor/amplitude query (LeanFinder: eight generic derived/truncation hits), with the valid Loogle query `"rightDerived"` (twelve generic localization-derived-functor hits), and with `cohomologicalDimension|hypercohomology|SpectralSequence` in Mathlib/CategoryTheory (zero hits). These are actual appended search-log records; none supplies this proper ind-constructible theorem. Source-tree searches by item id, IndCons/indConstructible and proper-window terminology found no exact finished declaration to attach. No Lean file was written and no compiler was run.

The proposed cross-unit tools are the generic spectral-sequence theorem, the ringed-site Grothendieck theorem, and the two heart-closure lemmas. The local unit does not duplicate these interfaces; its own proper-heart-bound route remains in force. The existing split_report.tool_uses proposals are supported by the delivery checker's explicit worker-proposal rule; no maintainer-owned top-level tool_uses field was written. Approval of these tools remains with the maintainer.

Validation: the required `deliver.py Q20 det-proper-unbounded-window-bounded-below --no-push` printed OK with preflight passed (dry-run commit 29ebcfdd30). The mathematical review, citation checks and dependency-cycle check are complete; delivery is authorized by the brief.
