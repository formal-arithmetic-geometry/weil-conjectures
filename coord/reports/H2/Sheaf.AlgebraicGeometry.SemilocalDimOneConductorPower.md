## What changed
Proved `semilocal_dim_one_conductor_power` from two strictly smaller auxiliary statements. Added imports for the auxiliary finite-adjoin/Jacobson theorem and the ideal-power conductor multiplication theorem.

## Proved and sorry left
The target theorem `semilocal_dim_one_conductor_power` is proved. Two auxiliary declarations remain `sorry`: `exists_finite_adjoin_with_jacobson_power` (node `semilocal-dim-one-conductor-power-aux`) and `Subalgebra.exists_base_mul_mem_of_mem_map_jacobson_pow` (node `semilocal-dim-one-conductor-power-mul`).

## No longer needed
The target proof does not directly use `integral_overring_jacobson_power` or the lying-over declaration; they are needed by the auxiliary node's stated proof route. No stated dependency node is pruned.

## Where the brief, the DAG or earlier work was wrong
The existing conductor theorem is pointwise for base elements in `J(B)^r`; the target requires arbitrary elements of `(J(B)A)^r`. The ideal-power multiplication lemma makes this missing finite-sum step explicit.

## New nodes
`semilocal-dim-one-conductor-power-aux` and `semilocal-dim-one-conductor-power-mul` are added in the sandbox DAG copies.

## Second reading by H2

1. Compared the delivered target module with the repository version and checked every
   existing declaration signature byte for byte. The target statement is unchanged;
   the two auxiliary modules and their declarations are new.
   **Verdict: pass.**
2. Compiled all three delivered modules with `lcompile.py --all`. The target has no
   `sorry`; the only remaining holes are the two named auxiliary theorems listed above,
   each with a docstring source and proof plan. No forbidden declarations or hollow
   definitions occur. **Verdict: pass.**
3. Searched the library and ran the required Mathlib search with alternate wording;
   neither auxiliary statement duplicates an existing declaration. Both are strictly
   smaller than the target and are needed by its proof. **Verdict: pass.**
4. Checked the proof from the target downward. It uses the finite-adjoin/Jacobson
   auxiliary result and the ideal-power conductor result, and retains the unit's route;
   no unused proof-only imports were found. **Verdict: pass.**
5. Updated the target node's `proof`, `proof_deps`, and `proof_origin` to match the
   actual Lean route, and checked both new nodes agree with their declarations and
   sources. **Verdict: pass.**

Changed the target proof to use local typeclass instances via `haveI`; added the two
   auxiliary modules and DAG nodes; and synchronized the target node metadata.
