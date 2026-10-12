## What changed
Added finite and top endpoint intermediate comparison modules and imported them into `Sheaf.Algebra.Homology.DoubleComplexVerticalTowerComparison`. The target theorem now performs case analysis on `j` and combines the two endpoint lemmas; the endpoint proofs remain named split statements.

## Proved and sorry left
The target theorem `HomologicalComplex₂.verticalTower_interval_homology_iso` is proved by reduction to the finite and top endpoint declarations. The declarations `verticalTower_interval_homology_iso_finite` and `verticalTower_interval_homology_iso_top` remain `sorry`, each with a new DAG node.

## No longer needed
None; the original tower maps and vertical window imports are used by the endpoint statements.

## Where the brief, the DAG or earlier work was wrong
The DAG proof requires a substantial bounded-below totalization argument not available in the current library. It was split into the finite and top endpoint statements, which are strictly smaller cases and preserve the stated target.

## New nodes
`lem-sp-double-complex-vertical-tower-comparison-finite` and `lem-sp-double-complex-vertical-tower-comparison-top` record the two endpoint intermediate declarations.

## Earlier second reading (a previous round; superseded)
The finite and top endpoint statements are strictly smaller than the original mixed-endpoint statement; the target proof preserves the unit route by using the tower maps and window definitions.

## Second reading by T2
1. **Statements unchanged.** Compared the delivered target module with the repository version; the existing declaration signature is byte-for-byte unchanged. The target proof only performs the `EInt` endpoint case split and applies the two new endpoint declarations. Verdict: pass.
2. **Proof and axioms.** Compiled all five sandbox modules with `lcompile.py --all`; there are no compiler errors, unsafe declarations, or hollow definitions. The only remaining `sorry`s are the two explicitly named endpoint theorems, each recorded in a DAG node. Verdict: pass subject to those split holes.
3. **Split statements.** Checked both endpoint declarations against the original mixed-endpoint target and the source route. They are true endpoint restrictions with the same homology conclusion, and are strictly simpler than the target. Their docstrings state the bounded-below totalization argument and their DAG nodes match their Lean statements. Verdict: pass.
4. **Pruning and imports.** The target still imports the tower maps publicly; the endpoint modules import the same map and mapping-cone APIs needed by their statements and proofs. No imported module was removable from the delivered proof. Verdict: pass.
5. **Unit route and DAG agreement.** The target continues through `verticalTower`, `verticalWindow`, and the endpoint comparisons, preserving the unit's realized route. The node proof/dependency records agree with the declarations and the target's actual proof. Verdict: pass.

Changed only the target proof and added the two endpoint modules and their DAG nodes; no existing statement or definition was altered. The endpoint theorems remain the two documented split holes.
