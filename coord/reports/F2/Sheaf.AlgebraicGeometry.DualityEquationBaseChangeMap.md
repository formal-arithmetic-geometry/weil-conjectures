## What changed

Verified the repaired inverse-mate construction of
`AlgebraicGeometry.dualityEquationBaseChangeMap`. The definition uses only the supplied
right-adjoint adjunctions and the inverse canonical base-change natural transformation;
it does not choose auxiliary pullback adjunctions or arbitrary counits. Updated the module
docstring to record that this data is determined by the displayed inputs. No Lean
signatures or target statements changed.

## Proved and sorry left

`AlgebraicGeometry.dualityEquationBaseChangeMap` contains no textual `sorry`; no local
holes were closed or added. The module compiles with `lcompile.py`. Any `sorryAx` reported
by an axiom check is inherited from still-open imported declarations.

## No longer needed

None. All three public imports are used by the declaration signature or construction, and
no DAG nodes or modules were removed.

## Where the brief, the DAG or earlier work was wrong

The repair queue described this item as hollow because of the former construction using
fresh chosen pullback adjunctions and counits. The current definition is already the
concrete inverse mate of the canonical base-change map, so that arbitrary-data issue is
resolved. The queue entry was stale; this delivery preserves the repaired definition.

## Second reading by F2

1. **Comparison.** Compared the delivered module with the repository version. The declaration
   signature and definition body are byte-for-byte unchanged; only the explanatory module
   docstring adds that the displayed inputs determine the construction.
2. **Compilation and axioms.** Compiled the module with `lcompile.py`; it is error- and
   warning-free. There are no `sorry`, forbidden declarations, or hollow definitions. The
   axiom probe reports only the permitted axioms plus inherited `sorryAx` from open imports.
3. **Statements and nodes.** The definition statement is unchanged and matches
   `def-sc-duality-equation-base-change-map`. Its proof uses the supplied adjunctions,
   lifted base-change map, and `mateEquiv`; the two obsolete proof dependencies for the
   removed auxiliary mate/conjugate construction were pruned from the node.
4. **Pruning.** All three public imports occur in the public signature or construction;
   the Mathlib mates import is proof-only. No module import can be removed. The node's
   `proof_deps` now records only declarations used by the current route.
5. **Unit route.** The construction remains the unit's canonical inverse-base-change mate
   and does not bypass the unit route. No target or public signature changed.

Changed: clarified the docstring and synchronized the node proof text and dependencies with
 the direct `mateEquiv` proof route. No holes were closed or added.
