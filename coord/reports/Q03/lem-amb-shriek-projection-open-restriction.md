# Worker report: lem-amb-shriek-projection-open-restriction

Files written:

- `dag/nodes/sec-smooth-purity/lem-amb-shriek-projection-open-restriction.json`: item, statement node, split with no new nodes; Mathlib searches found no match.
- `citations.json`: verbatim statement excerpts for every proof-step citation.
- `report.md`: this report.

Attachments:

- None. I searched the source tree for the item id, its title, and the compact-support projection/restriction declarations. No sorry-free project declaration states this exact item.

WANTED:

- None. The Stacks sources named by the imported item are present in `literature/stacks-project/`.

What was wrong or incomplete in the imported item:

- The item had no proof or proof dependencies even though it is a statement node. I supplied a three-step split. Its existing statement is retained verbatim; the derived open-tensor dependency is added to `stmt_deps` because the displayed compactified projection map uses that derived comparison.
- The stronger existing node `lem-asd-compact-projection-exchange` was already present in the DAG. It allows an arbitrary base-change morphism and gives the same projection/exchange equation, so the item is its open-immersion specialization. The item still needs `lem-amb-unbounded-compact-support-comparisons` to identify the chosen compactification maps with the canonical compactification-independent maps and to transport the equality through refinements.
- No source statement was disputed or weakened. No new DAG nodes were created.

## Not duplicates

- `lem-amb-shriek-projection-open-restriction` vs `lem-asd-compact-projection-exchange`: the latter treats an arbitrary morphism of Noetherian bases and compactification-defined maps `b` and `Pi`; this item fixes the base map to an open immersion, names the canonical compactification-independent exchange `C`, and records the open-extension normalization and inverse consequence.

## Review by Q03

I read the item JSON, the unit record `dag/units/sk-prop-an.json`, the chapter record `dag/chapters/sec-smooth-purity.json`, the imported parent `thm-amb-vector-bundle-purity`, and the source files `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-an/thm-amb-vector-bundle-purity.md`, Stacks `more-etale.tex` Tag 0F7L, and `sites-cohomology.tex` Tags 0E48 and 0GL1. I also read the full statements of every node cited below.

Step 1 specializes `lem-asd-compact-projection-exchange` with `v=u`, `M=M`, and `Q=K`; its displayed equation has exactly the same source, target, tensor comparison, and no-boundedness hypotheses as the item. I checked that its `X'`, `v_X`, and `f'` become `X_U`, `v`, and `f_U`, respectively. This is a generic tool from the compact-support base-change unit, declared in `split_report.tool_uses`.

Step 2 checks the normalization and domains. `lem-amb-unbounded-compact-support-comparisons` explicitly gives the unbounded exchange as proper exchange followed by inverse open-extension base change and states compactification independence. `def-amb-etale-compact-support` says the chosen compactified functor is `Rr_*` after derived extension by zero. `def-weil-pbc-etale-shriek-base-change-map` supplies the direction of the open extension comparison. `lem-pur-etale-open-derived-tensor` supplies the derived open tensor isomorphism for arbitrary unbounded inputs, and `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` supplies the canonical monoidal pullback identifications. The proper square is the Tag 0E48 projection/exchange square; the open square is Tag 0GL1. I verified that no boundedness, finite Tor-amplitude, flatness, or properness of `u` is introduced.

Step 3 is categorical cancellation: after the equality and exchange/projection isomorphisms are in place, composing with inverses gives the inverse equation. I tested the identity-map case, the empty open, `M=0`, `K=0`, and the case where `f` is proper; all reduce to the corresponding identity or zero square. The statement's finite-ring and ordinary-etale hypotheses remain unchanged.

The Mathlib searches were rerun with `msearch.py` for LeanFinder, Loogle, grep, and LeanSearch and recorded in `searches.jsonl`; all returned no relevant Mathlib declaration (Loogle reported an unknown identifier for the broad pattern). Blueprint search found no alternate blueprint node. The proof dependencies are exactly the union of the `uses` lists, and the only off-unit citations are declared as generic tools.

What I could not finish:

- No Lean code was written and no compiler or Lake command was run, as required for this stage-1 delivery.
