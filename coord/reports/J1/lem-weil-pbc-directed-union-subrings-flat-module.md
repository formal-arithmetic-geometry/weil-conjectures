# lem-weil-pbc-directed-union-subrings-flat-module

## Files

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-directed-union-subrings-flat-module.json`: split into five proof steps following Stacks Algebra Tag 05UU(2).
- No new nodes or unit edits.

## Source and statement

Read `literature/stacks-project/algebra.tex`, Lemma Tag 05UU (`lemma-colimit-rings-flat`), proof of part (2), and checked the tag in `stacks-project/tags/tags`. Its directed ring and module colimits specialize to the stated directed subrings and the elementwise colimit conditions (i) and (ii). The statement and `stmt_deps` are unchanged. The existing `lem-weil-pbc-colimit-rings-flat` states only part (1), so it cannot replace this item.

## Split

The proof applies the finitely generated ideal criterion (Tag 00HD), descends the ideal generators to a common stage, identifies the ideal and the target module as abelian-group colimits, applies the existing varying-ring tensor-colimit theorem, and uses flatness at each stage plus exactness of filtered colimits (Tag 00DB). The elementwise equality test from condition (ii) is written out; it also proves that restricting to the cofinal upper set does not change the module colimit.

Every non-elementary external fact is an existing cited node: `lem-weil-pbc-flat-fg-ideal-criterion`, `def-weil-pbc-category-colimit`, `lem-weil-pbc-filtered-colimit-tensor-varying-rings`, `def-weil-pbc-flat-ring-map`, and `lem-weil-pbc-filtered-colimit-abelian-groups-exact`. The varying-ring tensor node belongs to another unit and is used as a general tool; the lead should record this tool use if required by `review_split.py`.

## Audit

- No Lean declaration, proof, or `sorry` was changed; stage 1 writes DAG data only.
- No imports or DAG nodes become unnecessary.
- No discrepancy in the brief, source, or earlier statement was found.
- The node already contained LeanSearch, LeanFinder, Loogle, and grep searches with no Mathlib match. I checked the current Mathlib source path supplied by the lead while reviewing those records.
- No WANTED source.
- `tools/review_split.py` reports only the off-route use of `lem-weil-pbc-filtered-colimit-tensor-varying-rings` (twice for the same cited node). The lead must add `tool_uses`, as for the sibling `lem-weil-pbc-colimit-rings-flat`, before delivery.
- `tools/check_dag.py` currently raises `KeyError: lem-weil-pbc-essentially-finite-presentation-over-intermediate` during concurrent edits to another item; no item-specific DAG error was reported.

## Review by J1

I read Algebra Lemma 05UU(2) and its proof in `algebra.tex`. The item specializes its directed ring colimit to inclusions of subrings; its conditions (i) and (ii) give exactly the elementwise surjectivity and eventual equality needed for the module colimit. In step 1, the finitely generated ideal criterion is precisely the cited 00HD node, and finite generation puts all coefficients in one common stage. Steps 2 and 3 prove the two colimit identifications from the universal property in `def-weil-pbc-category-colimit`; the eventual-zero hypothesis handles equality of representatives, including when two indices first need a common upper bound. Step 4 uses the statement, not the proof, of `lem-weil-pbc-filtered-colimit-tensor-varying-rings`: the ideal inclusions and the module transition maps are semilinear as required. In step 5, each stage multiplication map is injective by the stated flat-module definition, and the exact filtered-colimit node preserves these injections. The resulting map is the ideal-test map on generators. The zero ideal and a singleton index give the expected trivial and ordinary flatness cases.

There are no new nodes; I searched the current DAG for 05UU and the flatness and tensor facts and confirmed the cited nodes state these exact ingredients. The off-unit tensor comparison is a general tool; I recorded it in `tool_uses`. I checked A-F of `coord/delivery-errors.md`: the argument does not cite a tag without a node, use a cited proof rather than its statement, assume an unstated hypothesis, or move the conclusion into a new node. The worker's source and proof needed no mathematical correction; I added only the approved tool-use field.

The server added B9 while I prepared the commit. I traced this created node through its `created.item` chain to step 7 of blueprint node `thm-weil-pbc-finite-etale-lifting` and recorded the chain and the proof place. `blueprint_refs.py search directed union flat` returned no blueprint node stating this sublemma; `same_as` is empty. I added the blueprint trace and the split report's blueprint place before pushing.
