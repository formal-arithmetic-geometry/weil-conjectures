# Stage-1 report: lem-trf-smooth-at-point-fibre-criterion

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-smooth-at-point-fibre-criterion.json`: the existing statement split into five proof steps; statement, statement dependencies, chapter, unit, source and blueprint ancestry retained. Fresh Mathlib searches appended to the inherited searches.
- `citations.json`: 25 verbatim statement quotations, one for each step-node citation.
- `report.md`: this report. `searches.jsonl` was produced by the authorized search command.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None for this item. I searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the exact item id and by smooth-at-point/fibre notions. The existing `AlgebraicGeometry.Scheme.Hom.fiberι_mem_smoothLocus` in `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/SmoothFiber.lean:130` assumes `[Flat f]` globally and gives one direction using the formally smooth stalk locus. It does not give the item's iff with merely a flat stalk map. The project global criterion, `AlgebraicGeometry.smooth_iff_flat_locallyOfFinitePresentation_smooth_fiberToSpecResidueField`, is already attached to `sbc-lem-smooth-criterion`, which the forward direction cites. No Lean file was written and no compiler was run. Upstream master was used only as read-only reference, not as evidence that a sorry declaration was proved.

## Wanted literature

None. The sources used are available in `literature/stacks-project/`.

## Problems found and repaired

The item was statement-only, with no `lean_audit` field or recorded proof. Its statement is correct: I read `morphisms.tex`, Tag 01V9, `lemma-smooth-at-point`, all six clauses and the full proof. The item is exactly (1) iff (2) after moving flatness into the hypotheses. There is no statement dispute and no hypothesis or conclusion was changed. A potential invalid shortcut would be to apply the global scheme criterion in the converse without global flatness. The split instead follows the source's explicit appeal to the ring-level Tag 00TF.

The blueprint searches `01V9`, `smooth at`, and `smooth fibre`, together with whole-DAG searches by those notions and tag, found the global smooth-fibre criteria and the differential criterion; none states the same pointwise fibre iff. The imported ancestry is preserved. The current main-20261015 ancestor proof and the recorded unit were read: this node supplies the local algebra tool in the inherited semistable/nearby-cycle chain and changes no unit or chapter route. This is not the unit's key statement, so no unit record is edited.

## What could not be finished

Nothing in this one-level split remains unfinished. Its algebra and affine comparison dependencies already exist as nodes and are cited rather than resplit. Independent mathematical review and landing remain the maintainer's work.

## Not duplicates

No new nodes were created. Existing `lem-weil-pbc-flat-smooth-fibre-smooth-at-prime` is reused for the strict ring-level input; `sbc-lem-smooth-criterion` and `lem-pc-smooth-characterization` are global criteria, whereas this item is pointwise with local flatness; `lem-trf-smooth-at-point-differential-criterion` is the different generator-bound equivalence (1) iff (3) in 01V9. Creating a new node for any of these facts would duplicate available material.

## Mathlib searches

I read all six actual results now logged in `searches.jsonl`; no service was unavailable. LeanSearch and the first LeanFinder query returned global smoothness and standard-smooth affine APIs. The second LeanFinder phrasing returned local algebra definitions and spreading lemmas, including `Algebra.IsSmoothAt.exists_notMem_smooth`. Loogle `Algebra.IsSmoothAt, RingHom.Flat` had no hits. The two authorized grep queries located `Mathlib/AlgebraicGeometry/Morphisms/SmoothFiber.lean` and `Mathlib/RingTheory/Smooth/Fiber.lean`. I read their declarations: the former has the global-flat, all-fibres criterion, and the latter's `IsSmoothAt.of_formallySmooth_fiber` sits under a global flatness hypothesis and assumes formal smoothness of the whole fibre. Neither is the item's pointwise scheme iff or a one-line specialization. All new records have the exact tool and query actually run, and the inherited records are retained.

## Tool uses

The two declarations in `split_report.tool_uses` are generic comparisons, not new geometric routes: the ring-level flat/smooth-fibre criterion `lem-weil-pbc-flat-smooth-fibre-smooth-at-prime` (Stacks 00TF), and the smooth ring-map/affine-scheme comparison `lem-weil-pbc-smooth-ring-map-iff-smooth-affine` (02H6). The unit `sk-i-curve-zero` supplies neither commutative-algebra fact. The global forward criterion is already Lean-closed; the remaining generic affine geometry statements used are existing Mathlib leaves or definitions.

## Review by NW

I reviewed the finished node against delivery-errors B through E with the cited node statements open. My source for the item is Stacks `morphisms.tex`, Tag 01V9, `lemma-smooth-at-point`; for its main algebra input I also read `algebra.tex`, Tag 00TF, `lemma-flat-fibre-smooth`, including its hypotheses and proof. There are no new-node sources to check. The source explicitly says base change gives (1) implies (2), and 00TF gives the converse; those are precisely the two directions realized here. No SGA source is used.

Step 1 takes the smoothness of every fibre from the actual statement of `sbc-lem-smooth-criterion`, applied to the smooth neighbourhood U, not to f in the converse. `lem-weil-pbc-open-fibre-product` identifies U_s as the open above U and preserves the projections. `def-pc-scheme-fibre` identifies the point above x. These statements give the smooth fibre neighbourhood required, without asserting the whole original fibre is smooth.

Step 2 takes the finite-presentation affine chart from `def-sbc-locally-finite-presentation`, the equality of morphisms from `lem-weil-pbc-affine-opens-induced-ring-map-spec-square`, the open-chart stalk isomorphisms from `lem-weil-pbc-affine-open-stalk-localization` (b)-(c), and the explicit localized stalk map from `lem-weil-pbc-spec-map-stalk-localization`. I checked that p is the contraction of q, the map is R_p to A_q, and its flatness is exactly the given hypothesis, not flatness of R to A.

Step 3 uses the same stalk isomorphism and `lem-weil-pbc-spec-residue-field-identification` to identify the base residue field together with its map. The affine fibre-product statement specifies both tensor product projections, and the open fibre-product statement identifies its image in X_s. Thus Q is exactly the kernel prime required by 00TF. The fibre definition gives uniqueness of the point over x. Smoothness at that point initially supplies a possibly non-affine open N. I wrote the short Zariski argument selecting D(h) inside its intersection with Spec F: the closed complement is V(I), so choose h in I outside Q. This is a direct consequence of the definition of the Zariski topology, not a new lemma. The principal-localization node identifies D(h) with Spec F_h. The open-immersion/smooth-composition node applies to its inclusion in N; the affine smoothness comparison then gives a smooth ring map k to F_h. Finally `def-weil-pbc-singular-ideal` defines exactly the pointwise ring smoothness being asserted. I checked each of these statements rather than borrowing any construction from their proofs.

Step 4 applies the existing 00TF node with A in its S slot and with the finite-presentation witness 1. Since q is prime, 1 is outside q. Step 2 supplies the local flatness; step 3 supplies precisely its fibre ring A tensor_R k and kernel prime Q, with no mistaken identification of A/pA as the fibre. Its conclusion and the definition of smoothness at a prime give g outside q and the smooth algebra A_g. This is a genuine strictly smaller existing algebra input, not a new node restating the item.

Step 5 uses the principal-localization node for the open containing x and the affine comparison for smoothness to V. The last passage is proved in the step: the same affine charts prove local finite presentation over S; a square-zero thickening has identical underlying points by the explicit assertion in `def-sbc-first-order-thickening`; its base map therefore factors through V, using the open-subscheme interpretation in `def-weil-open-immersion`. The formal smoothness definition supplies the lift over V and hence over S. The smoothness definition then supplies the conclusion. Thus no uncited open-target smoothness theorem is being silently used.

I tested the hypotheses on an empty source (no chosen point, so vacuous), the identity morphism, a smooth affine-space projection (including a nonclosed x), the flat singular fibre k[u,v]/(uv) at its node (both sides false), the nonflat closed immersion Spec k to Spec k[t] at t=0 (excluded despite its smooth fibre), and the purely inseparable extension F_p(t) to F_p(t^(1/p)) (flat and finitely presented but both smoothness assertions false). These checks preserve the need for pointwise flatness and for smoothness rather than reducedness of the fibre. No noetherianity, perfect-field, separatedness, or global-flatness hypothesis enters the argument.

All five steps are below 2000 characters. The only inline comparisons are the stated affine/fibre identifications and the short Zariski-open argument or the explicit lifting square, each with all non-elementary inputs cited. I checked statement dependencies, union of proof uses, lack of self-reference, verbatim quotations in `citations.json`, and retained metadata. No new elementary node, clause-restatement node, or unsplit-node proof was introduced.
