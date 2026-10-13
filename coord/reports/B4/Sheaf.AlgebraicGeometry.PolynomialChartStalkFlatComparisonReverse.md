## What changed
Added `PolynomialChartStalkFlatComparisonReverseAux` as the local criterion step and used it in the target module. The target theorem now has a complete proof from the auxiliary declaration and `Flat.stalkMap`.

## Proved and sorry left
The target `polynomial_chart_stalk_flat_comparison_reverse` is proved. The auxiliary theorem `polynomial_chart_stalk_flat_comparison_reverse_aux` remains `sorry` (node `lem-sbc-polynomial-chart-stalk-flat-comparison-reverse-aux`).

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The planned local criterion argument is not available as a single Mathlib theorem; it was split into the auxiliary local criterion statement.

## New nodes
`lem-sbc-polynomial-chart-stalk-flat-comparison-reverse-aux` records the remaining local algebra argument.

## Earlier second reading (a previous round; superseded)
The target proof preserves the exact statement and uses `Flat.stalkMap`; the auxiliary node is a strict local criterion substep with the remaining algebraic content.

## Second reading by B4

1. **Interface and accidental changes.** Compared the delivered target module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; the only interface addition is the separately declared auxiliary theorem and its node.

2. **Proof and axioms.** Compiled both sandbox modules with `lcompile.py --all`. The target proof is complete and uses `Flat.stalkMap`; the auxiliary theorem is the sole remaining named `sorry`, with no `sorry` in any definition and no forbidden declarations. The target's transitive `sorryAx` comes only from that explicitly documented auxiliary theorem.

3. **Split statement.** The auxiliary statement adds the independently needed base-stalk flatness hypothesis and isolates the local criterion implication. It is strictly more general as a reusable local criterion (the base flatness is supplied separately), has the same mathematical strength required by the target, and is documented with its Stacks Project source and node. No duplicate declaration was found in the library.

4. **Pruning and route.** The plain import of the auxiliary module is proof-only; the target's public imports remain required by its signature. The proof follows the planned local criterion route and retains the unit `sk-prop-normal-form`; no old proof dependency is unused, so nothing is pruned.

5. **DAG agreement.** The target node records the auxiliary criterion as its proof dependency, and the auxiliary node records the exact Lean declaration, source, proof route, and split status. The unit and chapter metadata are preserved.

Changed during this second reading: no mathematical statements or definitions; added this audit section only.
