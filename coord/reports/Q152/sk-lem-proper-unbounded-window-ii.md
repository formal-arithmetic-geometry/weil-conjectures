# Stage-1 report: sk-lem-proper-unbounded-window-ii

## Files written

- `dag/nodes/sec-six-functors-basics/sk-lem-proper-unbounded-window-ii.json`: item split into six proof steps; no new nodes and no Mathlib leaves.
- `dag/units/sk-lem-proper-unbounded-window-ii.json`: realized statement and the two unit proof paragraphs.
- `citations.json`: 9 step/node citation entries with verbatim statements.
- `report.md`: this report.

## Attachments

No finished sorry-free Lean declaration was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; the item remains a natural-language split.

## WANTED

None.

## STATEMENT-DISPUTED

The imported statement omitted the global integer `d` bounding the dimensions of all geometric fibres, although its only cited window theorem `sk-lem-proper-unbounded-window` requires exactly that hypothesis and the proof's truncation window is `q-2d-1`. Properness alone does not supply such a bound: the disjoint union map `coprod_{n>=0} P^n_k -> coprod_{n>=0} Spec(k)` is proper, while its geometric fibre dimensions are unbounded. I corrected the item statement by introducing `d` and making the coefficient, site, derived-category, size, and canonical comparison data explicit. This is an explicit hypothesis correction to the source's intended finite-window setting; the unrestricted corestriction is not claimed here. The current window source says “p and d as in [sk-lem-proper-heart-bound]”, and its general-detail statement also assumes this bound. The counterexample refutes the missing inference that properness supplies d; it does not assert that the unrestricted ambient coproduct comparison is false.

## Review by Q152

I reread the current item, the unit record, and the blueprint proof files `sk-lem-proper-unbounded-window-ii/_section.md`, `sk-lem-proper-unbounded-window-ii-general.proof.md`, and `sk-lem-proper-unbounded-window-ii-bounded.proof.md`, together with the full statements of every cited DAG node. I also searched the complete source tree for the item tag and for proper/direct-sum declarations; no exact finished declaration exists in the read-only slopmaster2 checkout, and the item is not a Mathlib theorem.

Step 1 uses `det-ambient-ind-derived-sums` for closure of `Dic` under ambient coproducts and `sk-lem-proper-unbounded-window` for membership of each derived pushforward. I verified that the latter states the same proper morphism, coefficient choices, and global geometric-fibre bound now present in the corrected item. Step 2 uses the cohomology-of-sums and truncation clauses of `det-ambient-ind-derived-sums`, plus `lem-weil-pbc-unbounded-derived-iso-cohomology`; it explicitly checks that sums commute with both canonical truncations and that the induced maps are cohomology isomorphisms. Step 3 applies `det-proper-unbounded-window-ii-bounded` with the common interval `[q-2d-1,q]`; its statement has the same proper `p`, coefficient `Lambda`, `Dic` family, and canonical comparison. Step 4 uses the window-isomorphism clause of `sk-lem-proper-unbounded-window` for the two truncation zigzags, and writes out naturality of the comparison maps on each coprojection. Step 5 uses `det-ambient-ind-derived-sums` to identify the left cohomology sum with the cohomology of the coproduct and `lem-weil-pbc-unbounded-derived-iso-cohomology` to conclude the ambient comparison is an isomorphism after checking every `q`. Step 6 uses only the closure and full-subcategory coproduct conclusion from `det-ambient-ind-derived-sums`; it verifies that the ambient inverse is a morphism in `Dic`.

I replaced the prior imported eight-step local restriction argument: it proved an ambient comparison by affine-local bounds but did not establish that the source and target belonged to `Dic(Y)` without the global bound required by the cited window lemma. The corrected split follows the unit's finite-window route, keeps the bounded-family theorem as the existing node, introduces no duplicate or clause-restating nodes, and records all Mathlib searches actually run in the item and `searches.jsonl`. No Lean files were written and no compiler, Lake, or build command was run.

## Source error

The bounded detail blueprint proof uses the wrong shift sign: it writes `H^n(C[-a])=H^{n+a}(C)` instead of `H^{n-a}(C)`. Taking `a=1` and `C` in degree zero gives an immediate check: `C[-1]` is in degree one. The corrected item invokes the bounded detail statement only; this typo belongs to that separate source and is not reproduced.

## Not duplicates

No new nodes are created. The bounded-family theorem is reused as `det-proper-unbounded-window-ii-bounded`, and the general detail node was read rather than restated as a new node. Searching the whole blueprint for “direct sums” found those two details and this item; they have overlapping content, but the item states preservation by the restricted functor, including its `Dic` membership and canonical internal coproduct, whereas the existing general detail concludes only an ambient comparison isomorphism.

## Remaining work

No mathematical substep is left without a cited statement or explicit elementary argument. The delivery still requires the server dry run and push. The corrected global bound is visible for the maintainer's independent statement review; no target statement is changed.
