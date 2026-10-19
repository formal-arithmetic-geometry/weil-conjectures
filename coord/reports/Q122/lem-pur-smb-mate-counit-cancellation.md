Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-smb-mate-counit-cancellation.json`: the imported statement is now split into five proof steps; no Mathlib match for the geometric statement.
- `citations.json`: 18 verbatim statement quotations covering every node used by every step.
- `searches.jsonl`: the required msearch records (leansearch, leanfinder, loogle, and grep).

Attachments: none. No Lean declaration under `WeilConjectures/` states this item exactly without `sorry`.

WANTED: none.

No statement correction was needed. I created no new nodes: the compact-support square and exchange are existing definitions, the etale/pro-etale compact-support comparison and exchange transport are existing lemmas, and the class-restricted Hom bijection and site-comparison unit are existing theorems. The item is not a duplicate of `lem-pur-smb-extraordinary`: that node asserts invertibility of the exceptional base-change comparison, while this item records the explicit counit cancellation and the equality of the two transposes. No SGA source is used.

## Not duplicates

No new nodes were created, so there are no new-node duplicate pairs to report.

## Review by Q122

I reread the item statement, its parent blueprint proof `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-cohsm/lem-pur-smb-extraordinary.proof.md`, and the unit/chapter records for `sk-prop-cohsm` and `sec-smooth-purity`. I also opened the current statements of every cited node and copied substantive literal excerpts into `citations.json`. Step 1 checks that the base-changed compactification is the one from `def-cbc-compact-support-square`, that the exchange is the specified mate from `def-cbc-exchange-map`, and that the comparison maps `S_N,T_N` satisfy the exact equation in `lem-pur-co-smooth-exchange-transport`; `lem-sf-class-compact-support-comparison` and `lem-weil-pbc-comparison-pullback` supply the comparison and kappa isomorphisms. Step 2 uses the finite-coefficient exchange isomorphism from `thm-cbc-finite-torsion` and the Step 1 equation to justify invertibility of the transported pro-etale exchange, with no inversion of an unproved map.

Step 3 checks the bounded-below etale-origin hypotheses against `def-weil-exceptional-inverse-image` and `thm-sf-ambient-adjoint-class`, and uses the explicit unit isomorphism in `thm-weil-pbc-site-comparison` plus the compact-support comparison to derive the stated pro-etale counit formula. Step 4 performs the displayed substitution and cancellation in the order imposed by `S_M` and `T_M`, yielding identity (1) with its exact source and target. Step 5 applies the transported Hom bijection, including the stated `eta_{Y'}` and witness `kappa_{u,M}`, then uses naturality and the unit-counit triangle to obtain identity (2); it also checks naturality and the cases `d=0`, zero/empty schemes, and identity base change. Every non-elementary assertion in these steps is cited, every cited quote contains the conclusion used, and every proof step is under 2000 characters. `proof_deps` is exactly the union of the step uses, and the item has no cycle or self-citation.

What could not be finished: nothing.
