## What changed

Replaced the whole proof of
`AlgebraicGeometry.coherentFormalModule_kernel_stalk_presentation` by a compiling reduction
through the new affine exact-filtration model. Its statement and visibility are unchanged.

The new module `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelAffineStalkFiltration`
asserts an exact affine model, without an Artin--Rees bound: a finite completed source module
N, a submodule L, and stalk presentations whose kernels are the localized intersections
L intersect K^(m+1)N. An order homomorphism describes localization of the submodules of L,
and its ideal-power equation identifies the localized extended ideal with the specified
stalk ideal. No construction or definition contains a hole.

The assigned module proves `intersection_filtration_bound` privately from Mathlib's
`Ideal.exists_pow_inf_eq_pow_smul`. It transports the intersection containment through the
injective subtype of L, applies monotonicity of the exact model's order homomorphism, then
chooses a finite affine subcover and takes the supremum of its bounds. This is a real
algebraic containment and compactness argument, rather than an application of a renamed
version of the original theorem. The new statement has no boundedness conclusion, no global
uniformization, and no maximum involving c. Those parts are proved here.

Updated the existing node's proof, proof_deps and proof_origin to match this reduction.
Both modules compile together with lcompile.py.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.coherentFormalModule_kernel_stalk_presentation`
(node `lem-weil-pbc-formal-kernel-stalk-presentation`). No sorry remains in the assigned module.
The private algebraic helper `AlgebraicGeometry.intersection_filtration_bound` is proved.

Added one hole:
`AlgebraicGeometry.coherentFormalModule_kernel_affine_stalk_filtration`
(node `lem-weil-pbc-formal-kernel-affine-stalk-filtration`). Its proof is exactly `by sorry`;
its docstring gives the source and complete affine quotient/localization argument.

This is a decomposition: one upper hole closed and one strictly intermediate hole added,
so the delivery has zero net hole reduction. The affine sheaf/localization identification
remains; the Artin--Rees containment and finite-cover uniformization are completed.

Edge cases checked against the construction and the Lean proof: empty affine opens have no
stalk conditions; an empty scheme requires no presentation and its finite supremum is zero;
zero modules give zero intersections and maps; the zero ideal gives zero positive-power
intersections; for the unit ideal all level targets vanish and the kernel and ideal-power
submodule are both the whole presentation module. The order-homomorphism equation includes
r = 0, so its top-submodule case has not been omitted. No finiteness over O_(X,x) is asserted:
scalar restriction of a finite completed module need not be finite over the coordinate ring.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`
- `Sheaf.RingTheory.AdicKernelImageBound`
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`

The old immediate proof dependencies no longer used directly are
`lem-weil-pbc-coherent-formal-modules-affine`, `new-adic-kernel-image-bound`,
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`, and
`lem-weil-pbc-ideal-module-product-stalk`. All four remain needed for the new affine
model's proof plan. They are
not claimed as globally unnecessary modules. The new bridge's statement needs only its
public imports; its unproved proof plan is recorded in its node for the next worker.

Retained `Sheaf.RingTheory.AdicCompletionNoetherian` and `Mathlib.RingTheory.Filtration`
because the completed-ring Noetherian instance and the Artin--Rees lemma are used in the
actual proof. Added the proof-only import of the new affine model. No public import changed.
No module or node is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error established. The original plan is valid, but the stated affine
formal-module equivalence and reduced-kernel image bound do not themselves expose the exact
localized intersection-filtration model used in its last step. This interface is isolated
as the new intermediate theorem. The source's level m is level m+1 in this library; the
algebraic helper uses n+d+1 and obtains the desired power n+1 without strengthening the
original statement. The finite-cover route of the original plan and the unit are kept.

LeanSearch was unavailable (HTTP Internal Server Error), recorded as unavailable rather
than a negative result. LeanFinder, Loogle and grep ran. The local Stacks TeX is not present
on this machine; the source was read at the official 087X and 087W pages.

## New nodes

`lem-weil-pbc-formal-kernel-affine-stalk-filtration` is stated in
`Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelAffineStalkFiltration`. It isolates the
affine quotient/localization step of Stacks 087X, using 087W, the reduced-kernel image bound,
Noetherianity of completion, localization exactness, and the ideal-module product dictionary.
It supplies exact kernels and ideal-power compatibility but no bound. Its data, proof plan,
source, searches, blueprint ancestry and Lean record are included. No change record is
needed: existing signatures, definitions and visibility are unchanged.

## Second reading by Y2

1. Interfaces: PASS. Diffed both delivered modules against the repository (the affine
   model is new). Compared the existing theorem signature byte for byte, including all
   hypotheses and its full conclusion: identical. The original public import, namespace,
   visibility, definitions and docstring are unchanged. No change record is required.
2. Proof and axioms: PASS as a decomposition. Independently compiled both files in import
   order through lcompile.py (5.9 s and 7.5 s). Scratch copies with `#print axioms` show
   only propext, Classical.choice and Quot.sound for intersection_filtration_bound;
   the main theorem and affine model also depend on sorryAx, as expected for the listed
   remaining hole and open dependencies. Inspected every delivered declaration: exactly
   one sorry, the entire proof of the named public affine model theorem; no hollow
   definition, unsafe declaration, axiom or alternate implementation. Existential module
   witnesses are eliminated only within a theorem proof; no definition selects arbitrary
   data from the unproved existence statement.
3. Split statement: PASS. Read Stacks 087W and 087X at their official pages and checked
   the affine equivalence, reduced-kernel image bound and localization-exactness node.
   L is the actual completed kernel and M its localization after scalar restriction.
   Exact localization gives the displayed intersection kernels. Ideal extension gives
   K^r L = I(U)^r L after restriction of scalars, including r=0, so localization gives
   the ideal-power equation. Naturality of j and its monic components force compatibility
   for all transitions. Checked empty opens and schemes, zero modules, zero and unit
   ideals, and m=n=d=0 where admissible. This lemma supplies an exact local filtration;
   the main file separately proves its bound and global uniformization, so it is a
   strictly intermediate statement, not a renamed restatement. The sourced docstring
   and matching complete node are present. Independent LeanFinder search for coherent
   adic kernel-image localization returned only ideal-sheaf kernel results; Loogle
   confirmed Ideal.exists_pow_inf_eq_pow_smul; grep with ker/comap and localization/quotient
   queries and rg on both library roots found no replacement. The existing affine
   kernel-image comparison gives equality comparisons, not exact compatible stalk
   presentations. Closing the new affine bridge requires that additional construction
   and cannot be done by a short application of an existing theorem.
4. Route and pruning: PASS. Checked the Artin--Rees exponent n+d+1, injective subtype
   transport, monotonicity of the order homomorphism, and the finite-cover supremum.
   Mathlib directly supplies Artin--Rees; no custom holed bound was introduced. All
   existing proof-only imports retained are used; the new public imports provide types
   occurring in its signature. The four removed immediate dependency nodes are now
   explicitly named above; none is claimed globally pruned. Read sk-thm-p1.realized:
   none of the removed immediate dependencies realizes a unit statement or step, and
   the affine calculation and finite-cover route are preserved.
5. DAG: PASS. Parsed both JSON files, checked proof_deps equals the union of step uses,
   and compared each lean.statement with the corresponding Lean signature. Only proof,
   proof_deps and proof_origin differ on the existing node. The new node has its source,
   searches, ancestry, chapter/unit, creation and Lean records. Its proof plan records
   the remaining affine construction rather than falsely claiming it is proved.

Second-reading changes: clarified the exact four old immediate dependency IDs under
No longer needed and added this independent review. No Lean proof or statement needed
repair. One original hole is closed and one lower hole remains added: zero net holes
closed, a decomposition rather than a completed proof of the import closure.
