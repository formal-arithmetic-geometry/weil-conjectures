## What changed

Proved `AlgebraicGeometry.Scheme.exists_open_stalk_retract_hom_eq` in
`Sheaf.AlgebraicGeometry.PerfectOpenStalkRetractHomEquality` without changing its
signature or visibility. Added a proof-only `import all
Sheaf.AlgebraicGeometry.FiniteFreeStalkMapEquality` to reuse three proved private
helpers. Adapted the existing proof of `exists_open_stalk_retract_map_eq` to a
single restriction and an arbitrary target. Updated the item's DAG proof and
proof dependencies to match this implementation.

The proof transports the finite-free splitting to the open subscheme, evaluates
stalk equality on the finitely many basis germs, shrinks their equalities, cancels
the splitting, and transports the resulting neighborhood back into X. The same
finite coproduct proof handles rank zero; no finiteness of the target is used.
Local compilation passed without errors or warnings.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_open_stalk_retract_hom_eq`
(node `lem-sc-perfect-open-stalk-retract-hom-equality`), the sole original hole.
No `sorry` remains in the delivered module. No new holes, modules, definitions,
statements, or axioms were added. This is a proof, not a decomposition.

## No longer needed

The planned dependency `lem-weil-pbc-finite-free-local-hom-zero`, module
`Sheaf.AlgebraicGeometry.FiniteFreeLocalHomZero`, is no longer needed by this
item: the proved finite-germ equality helper provides the shrinking directly.
It was not imported originally, so no existing import was removed. Both original
public imports are needed by the unchanged statement. All remaining declared
proof dependencies are retained, and the finite-germ helper's node
`lem-pc-finite-free-stalk-map-eq-shrink` is added. No claim is made that the
pruned dependency is unused by other targets or modules. The unit's realized
route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The DAG's zero-map route is valid but unnecessary: an existing proved helper
already gives equality of free-source maps from equality of basis germs. The
neighboring retract-endomorphism proof also works for arbitrary target sheaves,
so no extra intermediate theory is required. No statement error or tool fault
was encountered.

## Second reading by C3

1. Compared the delivered Lean module against the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only a proof-only import, local proof options, and the theorem proof differ. Verdict: pass.
2. Compiled the module with `lcompile.py` and checked `#print axioms`; it compiles cleanly and uses only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, axiom, unsafe, opaque, extern, or implemented_by occurs. Verdict: pass.
3. Checked the proof route and dependencies against the imported finite-free stalk equality helper and the neighboring retract proof. The proof uses the arbitrary-target finite-generator argument, handles rank zero through the finite coproduct helper, and introduces no new statements or holes. Verdict: pass.
4. Checked pruning and imports. The added `import all Sheaf.AlgebraicGeometry.FiniteFreeStalkMapEquality` is proof-only and is required for the private helpers; both public imports remain required by the theorem statement. The old zero-map dependency is not used, and the DAG proof and `proof_deps` record this route. Verdict: pass.
5. Checked the DAG node and unit route. The node statement matches the unchanged Lean declaration, the proof steps and dependencies match the implementation, and the unit's realized route is preserved. Verdict: pass.

Changed during second reading: no Lean proof or DAG changes were necessary; appended this review section and retained the worker's compiling proof and dependency pruning.
