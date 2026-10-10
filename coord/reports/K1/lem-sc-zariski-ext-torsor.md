1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-zariski-ext-torsor.json`: statement node, split with two proof steps.
- `dag/nodes/sec-curve-estimates/lem-sc-zariski-contracted-power-extension.json`: statement-only node, no Mathlib match.
- `citations.json`: verbatim citations for both proof steps.

2. Attachments:

No exact Lean declaration attaches to this item. The generic declaration `CategoryTheory.Sheaf.nonempty_equiv_ext_torsor` is recorded on the separate etale node `lem-sc-ext-torsor`; its statement is not the Zariski-specific item here.

3. WANTED:

WANTED: the local Stacks source file `literature/stacks-project/cohomology.tex` is not present in this checkout; the split follows the cited Lemma 02FQ place already recorded by the existing boundary-class node.

## Review by K1

I read the target node and its ancestor blueprint reference, the existing `lem-sc-ext-torsor` node, and the source declaration `CategoryTheory.Sheaf.nonempty_equiv_ext_torsor` in `WeilConjectures/CategoryTheory/Sites/Torsor.lean`. That declaration is generic but its blueprint tag is the etale item, so it does not state this Zariski item exactly. I also read `lem-sc-torsor-h1-zariski-boundary-class`: its statement explicitly says that the fibre over 1 of a short exact sequence on the Zariski site is a G-torsor, and identifies the torsor class with the boundary class. Step 1 uses the new construction node, whose statement explicitly supplies the contracted-power abelian sheaf, short exact exponent sequence, and fibre over 1. Step 2 uses the existing boundary-class statement for the converse fibre torsor; the addition maps identify every fibre over n with the corresponding contracted power, giving the inverse equivalence. I checked the small cases mentally: the trivial torsor gives the split sequence G plus Z_X, and the fibre over 1 is G; for n=0 the contracted power is G, while n=1 is T. I recorded three Mathlib searches for the new node and found no matching declaration. No unrelated files were changed.
