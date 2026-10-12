## What changed

Added `exists_affine_free_etale_zero_cokernel` in a new module, with its proof left as a named DAG obligation. The target theorem is proved by applying it and the standard abelian-category zero-cokernel criterion for epimorphisms.

## Proved and sorry left

`exists_affine_free_etale_epimorphism` is proved. The only remaining sorry is `exists_affine_free_etale_zero_cokernel`, in node `lem-weil-pbc-constructible-module-finite-zero-cokernel`.

## No longer needed

The target module no longer directly uses the long constructibility, stalk, support, and spectral-topology dependency list; these are encapsulated by the intermediate theorem. No existing modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan was reduced to a strict zero-cokernel intermediate statement, preserving its intended Stacks argument while leaving that construction as a separately named obligation.

## New nodes

`lem-weil-pbc-constructible-module-finite-zero-cokernel` is stated in `lean/Sheaf/AlgebraicGeometry/ConstructibleModuleFiniteZeroCokernel.lean`.

## Earlier second reading (a previous round; superseded)

The target proof is unchanged in statement and derives its epimorphism from the strictly stronger zero-cokernel intermediate theorem. The remaining theorem is named and has a matching node; the unit route is preserved through this intermediate obligation.

## Second reading by U1

1. **Interface comparison:** The delivered target module has the same theorem signature as the repository version; the only interface addition is a proof-only import. Verdict: unchanged statement.
2. **Proof checks:** Both delivered modules compile with `lcompile.py --all`; the target has no `sorry`, while the sole remaining `sorry` is the named theorem `exists_affine_free_etale_zero_cokernel`. No forbidden declarations or hollow definitions occur. Verdict: pass.
3. **Split statement review:** The zero-cokernel statement is strictly stronger than the target conclusion, has a source docstring and matching DAG node, and is not duplicated in the library. Its truth is exactly the zero-cokernel form of the Stacks finite-cover argument. Verdict: true and appropriately scoped.
4. **Pruning and route:** The target proof uses the standard `Preadditive.epi_of_isZero_cokernel` criterion; the long construction is isolated in the named intermediate obligation. No additional old imports were removable without affecting the public statement. Verdict: shortest available completed route, with the unresolved construction clearly split off.
5. **DAG and unit consistency:** The node proof and `proof_deps` include the zero-cokernel node used by the Lean proof, and the unit remains realized through the finite-cover intermediate. Verdict: consistent.

Changed only the proof import and proof body, plus this second-reading record; no theorem statements or definitions were altered.
