# Stage-1 worker report

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-intersection-sections-flat-base-change.json`: item, split into four proof steps; statement and hypotheses retained.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-sections-intersection-structure-colimit.json`: new statement-only node, unsplit; no Mathlib match for the intersection section-colimit formula.
- `citations.json`: six verbatim statement quotes for the cited nodes.

## Attachments

None. No sorry-free declaration under `WeilConjectures/` states this item. The exact item tag and the relevant section/intersection and flat-base-change terms were searched in the read-only source checkouts.

## WANTED:

None. The needed sources are in the local Stacks checkout.

## Not duplicates

- `lem-a1-sections-intersection-structure-colimit` vs `lem-a1-intersection-sections-flat-base-change`: the new node states only the underlying Stacks equation identifying sections on an intersection with a filtered colimit; the item adds flat affine base change, its canonical T-algebra map, naturality, and iterated compatibility.
- `lem-a1-sections-intersection-structure-colimit` vs `lem-sc-topological-abelian-sections-filtered-colimit`: the existing node treats arbitrary abelian sheaves on compact open subsets of a topological space; the new node treats the structure sheaf on a possibly nonschematic intersection of quasi-compact opens and gives the geometric restriction colimit.
- `lem-a1-sections-intersection-structure-colimit` vs `lem-weil-pbc-sheaves-directed-colimit-sections`: the existing node concerns colimits of sheaves on a finite-cover site; it does not identify sections on an intersection of opens with a filtered colimit of stage sections.
- `lem-a1-intersection-sections-flat-base-change` vs `lem-weil-pbc-flat-base-change-global-sections-qcqs`: the existing Mathlib leaf is for global sections of a quasi-compact quasi-separated scheme. Here (E) may be neither open nor a scheme and carries the inverse-image sheaf, so the intersection-colimit passage is additional content.
- `lem-a1-intersection-sections-flat-base-change` vs `lem-weil-pbc-sections-over-quasi-compact-open`: the existing node is the ideal-power/Hom description for the complement of a finite-type ideal on a quasi-compact scheme; it does not assert flat affine base change on arbitrary intersections.

## What was wrong or corrected

The imported item was statement-only and had no completed proof. I kept its Tag 0APJ statement, including the naturality and iterated-base-change clauses. The proof now makes the source's omitted details explicit: finite-intersection refinement of the family, the two applications of the intersection-section formula, stagewise application of the existing qcqs flat-base-change leaf, tensoring a filtered colimit, and the pure-tensor identification of the canonical algebra map. I added the existing filtered-colimit algebra leaf so the underlying-module colimit used by the tensor-colimit leaf is cited. The imported `created` metadata identifies the earlier NZ worker; it is retained as history, while this split records NS as the worker in `split_report` and the new node's `created` field.

## What could not be finished, and why

The new section-colimit node is intentionally statement-only, as required by a one-level stage-1 split. It joins the later queue for its own split. No Lean was written and no compiler, Lake, or build tool was run.

## Review by NS

I read the item source in `literature/stacks-project/more-groupoids.tex`: the paragraph defining (E=\bigcap U_i) and equation `equation-sections-of-intersection` at line 2977, and `lemma-affine-base-change` at line 3064 with its proof through line 3089. I also read `literature/stacks-project/coherent.tex`, Tag 02KH (`lemma-flat-base-change-cohomology`, line 948), and the full statements of `lem-weil-pbc-flat-base-change-global-sections-qcqs`, `lem-weil-pbc-filtered-colimit-algebras-elementwise`, `lem-weil-pbc-tensor-commutes-with-colimits`, and `lem-weil-pbc-algebra-tensor-pushout-universal-property`.

Step 1 is the elementary finite-intersection refinement: the family remains nonempty, has the same intersection, and inverse image commutes with intersections; affine base change preserves quasi-compact opens. Step 2 cites the new node exactly for both (Y) and (Y_T); the latter is quasi-separated because it is affine over the quasi-separated (Y). Step 3 applies the existing qcqs global-sections leaf to each (U_i\to\operatorname{Spec}R), with (U_i) quasi-compact and quasi-separated and (T) flat. The algebra-colimit leaf supplies the underlying module colimit, and the tensor-colimit Mathlib leaf supplies ((\varinjlim M_i)\otimes_RT\cong\varinjlim(M_i\otimes_RT)). The algebra pushout leaf identifies the resulting map with (c\otimes t\mapsto g^\sharp(c)t). Step 4 checks naturality and iterated compatibility on pure tensors; both paths send (c\otimes t\otimes s) to the same pulled-back section times scalars, with tensor associativity and pullback functoriality.

I checked the hypotheses at every use: (R,T) are commutative, the affine base map is flat, (Y) is quasi-separated, each stage open is quasi-compact and quasi-separated, and the inverse-image sheaves are exactly the ones in the item. Edge cases include (E=\varnothing), a singleton family, (T=R), and a second identity base change; all give the expected zero/identity or iterated tensor maps. The server-side `check_dag` preflight passed with `check_dag OK`.
