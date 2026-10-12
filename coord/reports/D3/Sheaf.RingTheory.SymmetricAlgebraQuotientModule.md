## What changed

Added the first-isomorphism-theorem proof of `symmetricAlgebra_quotient_module`. The graded surjectivity and kernel identification are isolated in the new intermediate theorem `symmetricAlgebra_quotient_module_kernel`; the quotient algebra equivalence is constructed using Mathlib's `Ideal.quotientKerAlgEquivOfSurjective` and transported across the kernel equality.

## Proved and sorry left

The target theorem `symmetricAlgebra_quotient_module` is proved. The new intermediate declaration `symmetricAlgebra_quotient_module_kernel` remains `sorry`, covering the graded summation argument from `symmetric_degree_exact`.

## No longer needed

No imports or DAG dependencies were removed. The main theorem does not directly use `Sheaf.LinearAlgebra.SymmetricAlgebra.DegreeExact`; it is retained because the intermediate theorem's statement and proof source depend on it.

## Where the brief, the DAG or earlier work was wrong

The original plan omitted the readily available Mathlib first-isomorphism theorem for surjective algebra homomorphisms. The quotient-equivalence step is therefore discharged directly by `Ideal.quotientKerAlgEquivOfSurjective`, after transporting along the proved kernel equality.

## New nodes

Added `lem-weil-pbc-symmetric-algebra-quotient-module-kernel` for the strict lower-level conjunction of surjectivity and kernel equality.

## Earlier second reading (a previous round; superseded)

Pending the independent second reading.

## Second reading by D3

1. **Statements and visibility.** Compared both delivered modules against the repository. The existing target declaration is byte-for-byte unchanged; the new kernel theorem is a strict lower-level conjunction and is documented with its source and blueprint node. The proof-only `DegreeExact` import remains private, while the quotient theorem imports the new kernel module.

2. **Compilation and axioms.** Compiled both modules with `lcompile.py --all`; both compile cleanly. The kernel theorem is the sole intentional `sorry`, and it has a matching DAG node. The quotient theorem contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; its proof uses Mathlib's quotient first-isomorphism equivalence.

3. **New statement.** Checked the kernel statement on the zero map and identity-map edge cases: it has the expected surjectivity and generated-kernel behavior. It is strictly simpler than the target because it stops before constructing the quotient equivalence, and is needed by the target proof. No duplicate declaration was found in the library or Mathlib.

4. **Pruning and route.** The proof follows the planned unit route through the kernel/degree-exactness result and then uses `Ideal.quotientKerAlgEquivOfSurjective`; no unnecessary imports or DAG dependencies were identified. The retained `DegreeExact` import is needed by the split theorem.

5. **DAG agreement.** The target proof and `proof_deps` agree with the Lean proof, and the new kernel node records its source, proof origin, statement, and Lean declaration. The unit realization is preserved.

Changed only the target proof, added the kernel module and node, and recorded the intentional split-off `symmetricAlgebra_quotient_module_kernel`.
