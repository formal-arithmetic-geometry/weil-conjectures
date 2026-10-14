## What changed
Added a complete composition proof of `affine_torsor_equivariant_descent_algebra`. The proof factors through two strictly simpler orbit-model statements in separate modules, then composes the resulting `AlgEquiv`s. The geometric descent theorem remains as supplied and now imports the new helpers.

## Proved and sorry left
`affine_torsor_equivariant_descent_algebra` is proved. The new intermediate declarations `equivariant_orbit_model` and `fixed_orbit_product_equiv` remain sorry and isolate the orbit construction and finite-index comparison respectively. `affine_torsor_equivariant_descent` remains sorry.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The prior attempt stopped at the geometric step. The algebraic target can be reduced to two strictly smaller algebraic statements and a real composition proof, without addressing geometric descent.

## New nodes
`lem-sbc-equivariant-orbit-model` and `lem-sbc-fixed-orbit-product-equiv`.

## Earlier second reading (a previous round; superseded)
Pending independent reading.

## Second reading by K4

1. Compared the delivered target module with the repository version. The existing
declaration signatures are unchanged; only imports and the proof body of
`affine_torsor_equivariant_descent_algebra` differ. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. There are no
errors, forbidden declarations, or `sorry` in definitions. The two split-off
theorems are the only remaining proof holes in the new helper modules, and the
geometric theorem remains the pre-existing hole. Verdict: pass.
3. Checked the two split-off statements against their Lean declarations and
their edge cases (`m = 0` and `d = 0` are permitted by the quantifiers). They
are strictly smaller than the target and provide exactly the two composition
steps; their docstrings describe the orbit-evaluation proof. Verdict: pass.
4. The target proof uses both helper declarations and composes their
`AlgEquiv`s, preserving the unit route through fixed-orbit data. No old import
or proof dependency is unused. Verdict: pass.
5. The DAG nodes, module names, declarations, and proof route agree with the
Lean files; the helper nodes are marked `split` and include their sources and
blueprint links. Verdict: pass.

Changed the duplicate helper docstring wording and recorded this review. No
mathematical statement or target definition was changed.
