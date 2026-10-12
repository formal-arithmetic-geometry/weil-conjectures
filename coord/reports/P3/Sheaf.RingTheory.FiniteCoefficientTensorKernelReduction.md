## What changed

Proved `RingHom.finite_coefficient_tensor_kernel_reduction_quotient` by combining the
closed-fibre calculation with Mathlib's proved
`LinearMap.ker_inf_smul_top_eq_smul_of_flat` from `Mathlib.RingTheory.Smooth.Quotient`.
Added the proved theorem `RingHom.finite_coefficient_tensor_kernel_closed_fiber` in its
own module `Sheaf.RingTheory.FiniteCoefficientTensorKernelClosedFiber`. Both added imports
in the item are plain proof imports. Existing signatures, definitions, docstrings and
public imports are unchanged. Updated the two existing DAG proof plans and added the
closed-fibre node. No change record or forced adaptation is needed.

## Proved and sorry left

Closed the one existing hole:
`RingHom.finite_coefficient_tensor_kernel_reduction_quotient`
(node `lem-weil-pbc-finite-coefficient-tensor-kernel-reduction-quotient`).
The already proved `RingHom.finite_coefficient_tensor_kernel_reduction` is unchanged and
now has no sorry in its dependency closure. The new theorem
`RingHom.finite_coefficient_tensor_kernel_closed_fiber`
(node `lem-weil-pbc-finite-coefficient-tensor-kernel-closed-fiber`) is also proved.
Holes added: none. Sorries left in delivered modules: none. This is one existing hole
closed, zero holes added, rather than a decomposition. All three declarations were checked
with `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.

## No longer needed

The planned proof dependency `lem-weil-pbc-flat-quotient-tensor-injective` is replaced by
the direct, proved Mathlib ideal-intersection theorem. It is removed from the two old
proof plans. `def-weil-pbc-flat-ring-map` and `def-weil-module-base-change` remain statement
dependencies of the upper node, but its proof now just uses its quotient theorem.
No baseline import or library module was removed. The proposed factorization module/node
was never part of the repository; it was removed from this sandbox, not pruned from the
library. No unit realization is changed.

## Where the brief, the DAG or earlier work was wrong

The first worker's factorization helper was equivalent to the original inclusion:
the identity endomorphism witnesses it whenever the inclusion holds, and its fixing and
landing properties imply the inclusion. It was a restatement, not a strictly smaller
intermediate, and its docstring lacked the complete promised proof. It is removed.
The earlier report overstated progress by counting the unchanged upper theorem as a new
proof. The original quotient proof plan's final balancing sentence must be read together
with flatness: balancing alone puts a tensor in m_A D, not m_A ker F. The repaired proof
separates these two steps explicitly.

## New nodes

`lem-weil-pbc-finite-coefficient-tensor-kernel-closed-fiber`, at
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-coefficient-tensor-kernel-closed-fiber.json`,
records the proved elementary tensor and residue-field calculation. Its hypotheses do not
require flatness, surjectivity of F, locality of γ/φ/ψ, or locality of B/C; its conclusion is
only ker F⊆m_A D. The full natural-language proof is in the theorem docstring and DAG steps.
LeanSearch returned Internal Server Error; Loogle and grep found no specialized theorem.
The successful flatness search found Mathlib's ideal-intersection theorem, which is used.

## Second reading by P3

1. Compared the item with the repository by diff. Both existing theorem signatures are
   byte for byte unchanged, including every ring/algebra/locality instance, map, compatibility
   equation, residue bijectivity, tensor formula, flatness, surjectivity, kernel equality and
   conclusion. There are no definitions or changes to target statements. The upper proof
   is unchanged. The only item edits are proof imports and the quotient proof.
2. Compiled both files with lcompile.py, without errors or warnings. No sorry or forbidden
   declaration is present. Scratch `#print axioms` checked the closed-fibre helper and both
   original declarations: only the three permitted axioms. No data is chosen from an
   unproved existence theorem; residue representatives are chosen inside a proved proposition.
3. Rejected the equivalent factorization statement and removed it. The replacement helper
   is proved, with a complete docstring proof. Checked field case m_A=0 (the normal form is
   exact and hker forces zero), zero tensor x=0, the identity base map, and potentially zero
   B/C (the generator and tensor induction arguments still apply; no nontriviality of B/C
   is assumed). Searched Mathlib by quotient-flat intersection, residue-map tensor products,
   and closed/special fibre terminology; searched both library roots and DAG records.
   No split-off sorry remains.
4. Used the shorter Mathlib ideal-intersection identity instead of rebuilding tensor
   exactness. Each public import supplies types in signatures; the new item imports are
   needed only by its proof and are plain imports. No baseline module import can be removed.
   Read `dag/units/sk-thm-p1.json`: neither the item nor its closed-fibre intermediate realizes
   a unit step, and the unit's statement, steps, and realized route stay intact.
5. Updated the quotient node to cite the proved closed-fibre node and describe the exact
   Mathlib identity and scalar restriction rewrites. Updated the upper node to cite its
   actual quotient dependency. The new node has its precise Lean signature, self-contained
   statement, source, elementary proof steps, searches, creation data and blueprint ancestry.
   Read Stacks tags 07NS (4) and 07NQ online because the local TeX file is absent: these supply
   the closed-fibre comparison and flat kernel argument; the proof uses no completeness,
   finiteness or Nakayama hypothesis from their broader setting.

Second reading changed: removed the restatement and its sorry; proved the closed-fibre
calculation and quotient theorem; repaired proof-dependency metadata and progress reporting.
