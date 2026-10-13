## What changed

Added two intermediate theorem modules and imported them in the target module. The target theorem is now proved by obtaining a stalkwise pairing and then extending it to the coordinate maps, combining the resulting witnesses with `⟨b, t, ht, hb⟩`.

## Proved and sorry left

Proved `moduleCup_godement_tensor_coordinates_exists` by decomposition. The two strictly smaller intermediate theorems remain `sorry`: `moduleCup_godement_tensor_stalk_pairing_exists` (node `new-module-cup-godement-tensor-stalk-pairing-exists`) and `moduleCup_godement_tensor_map_of_pairing_exists` (node `new-module-cup-godement-tensor-map-of-pairing-exists`).

## No longer needed

No imports or proof dependencies were removed; the coordinate definition remains required.

## Where the brief, the DAG or earlier work was wrong

The direct construction is substantial, so the target was reduced to the two independent stalk-pairing and coordinate-extension steps described by its own proof plan.

## New nodes

`new-module-cup-godement-tensor-stalk-pairing-exists` in `dag/nodes/sec-abelian-varieties/new-module-cup-godement-tensor-stalk-pairing-exists.json`.

`new-module-cup-godement-tensor-map-of-pairing-exists` in `dag/nodes/sec-abelian-varieties/new-module-cup-godement-tensor-map-of-pairing-exists.json`.

## Earlier second reading (a previous round; superseded)

The target proof combines the two intermediate statements with the exact conjunction shape of `ModuleCupGodementTensorCoordinates`; both new statements are strictly smaller parts of the planned construction and compile.

## Second reading by H4

1. **Visible changes and statements.** Compared all three delivered Lean modules with the repository versions. The existing target declaration has the identical signature and unchanged statement; only proof imports and proof text were added. The two new declarations are the split-off statements recorded by their DAG nodes.
2. **Compilation and proof audit.** Compiled all sandbox modules with `lcompile.py --all`; compilation succeeds. The target proof contains no `sorry`, axiom, unsafe, opaque, extern, implemented_by, or hollow definition. The two intentionally split intermediate theorems each contain the single named `sorry` listed in the report and have matching nodes.
3. **Truth and strength of split statements.** Checked the stalk-pairing theorem against the represented-germ construction and the map-extension theorem against the coordinate formula. Each is a strict substatement of the target, with no added hypotheses or weakened conclusions, and neither duplicates an existing library declaration.
4. **Shortest route and pruning.** The target proof directly destructs the two intermediate existence statements and assembles their witnesses with `⟨b, t, ht, hb⟩`. The target's proof-only imports are plain imports. No unused import or old proof dependency can be removed without dropping a declaration used by this proof.
5. **DAG and unit route.** Verified both new node records agree with the Lean declarations, proof dependencies, sources, and `sk-prop-av-cube` unit. The target node remains the unit's realized construction node and its statement is unchanged.

Changed only this report: added this second-reading audit. No Lean declarations or DAG records required repair.
