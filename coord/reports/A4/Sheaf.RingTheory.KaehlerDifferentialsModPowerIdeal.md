## What changed
Added `KaehlerDifferentialsModPowerIdealCore`, whose intermediate theorem states bijectivity of the canonical differential map, and proved the original theorem by constructing `LinearEquiv.ofBijective` from it. The original module imports this proof module.

## Proved and sorry left
The target theorem `kahlerDifferential_mod_power_ideal` is proved. The intermediate theorem `kahlerDifferential_mod_power_ideal_bijective` remains `sorry`, with node `lem-weil-pbc-kahler-differentials-mod-power-ideal-bijective`.

## No longer needed
None; all original proof dependencies remain the stated source of the intermediate theorem.

## Where the brief, the DAG or earlier work was wrong
The full exactness and Leibniz argument is substantial, so it was split into the strictly simpler bijectivity statement and the packaging into a linear equivalence.

## New nodes
`lem-weil-pbc-kahler-differentials-mod-power-ideal-bijective` in `dag/nodes/sec-proper-base-change/`.

## Earlier second reading (a previous round; superseded)
The target proof compiles and preserves the original signature. The new intermediate statement is a strict decomposition: it supplies bijectivity of the generator map, while the target separately packages that map as a linear equivalence.

## Second reading by A4

1. **Visible changes.** Compared with the repository module, the target signature and all existing declarations are byte-for-byte unchanged. The only proof change imports the new core module and applies `LinearEquiv.ofBijective`. The target DAG node records this route, and the added core declaration has its own node.
2. **Compilation and proof status.** Both sandbox modules compile with `lcompile.py --all`. The target theorem has no `sorry`; the only remaining hole is the named theorem `kahlerDifferential_mod_power_ideal_bijective`, exactly the split-off node. No axioms, unsafe declarations, or hollow definitions were added.
3. **Statement review.** The split-off theorem is strictly simpler than the target: it asks for a bijective linear map with the same generator formula, while the target additionally packages that map as a linear equivalence. Its hypotheses and conclusion agree with the canonical map in the Stacks Tag 02HQ statement, and the node records the source and proof dependencies.
4. **Route and pruning.** The target proof uses the split-off bijectivity theorem and Mathlib's `LinearEquiv.ofBijective`; the unit's existing route remains represented by the split theorem's proof dependencies. No import or dependency was removed from the original module's public interface.
5. **Search and consistency.** A fresh `msearch.py` query finds `LinearEquiv.ofBijective` as the applicable Mathlib packaging lemma and no competing theorem for the general power-ideal bijectivity result. The new node's Lean statement matches the declaration exactly.

Changed after reading: added the target node's updated proof route and this review record; no mathematical statement or definition was changed.
