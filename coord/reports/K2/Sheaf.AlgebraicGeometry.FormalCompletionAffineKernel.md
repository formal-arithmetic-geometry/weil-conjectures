## What changed

Proved the unchanged declaration `AlgebraicGeometry.formalCompletion_affine_kernel`
in `Sheaf.AlgebraicGeometry.FormalCompletionAffineKernel` from one new affine comparison
statement and Mathlib's `AdicCompletion.map_injective` and `AdicCompletion.map_exact`.
Added three proof-only imports: `Sheaf.AlgebraicGeometry.FormalCompletionAffineComparison`,
`Mathlib.RingTheory.AdicCompletion.Exactness`, and
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`. All original public imports remain.
The comparison publicly imports `ShortComplex.ShortExact`, not the proof-only
`ShortComplex.ModuleCat` results, and has no separate kernel-preservation import.
No existing statement, definition, visibility, universe or target was changed.

The new comparison isolates steps 1–3 of the original plan: the original finite module
short exact sequence, the functor reflecting parallel-pair limits, and linear equivalences
intertwining the restricted completed arrows with the module completion maps. Its
conclusion asserts neither injectivity nor exactness of the completed maps. The main
proof performs that algebraic argument in Lean, including transfer of injectivity,
construction of preimages of killed elements, formation of the limiting kernel fork,
and reflection of its universal property. Updated the original DAG proof and dependencies.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.formalCompletion_affine_kernel`
(node `lem-weil-pbc-formal-completion-affine-kernel`). No sorry remains in the item's module.

Added one hole: `AlgebraicGeometry.formalCompletion_affine_comparison`, in new module
`Sheaf.AlgebraicGeometry.FormalCompletionAffineComparison`, node
`lem-weil-pbc-formal-completion-affine-comparison`. Its entire proof is `:= by sorry`;
its docstring and node describe the geometric comparison completely.

This is a decomposition: one hole closed, one added, net zero; it is not a sorry-free
proof of formal completion. The assembly from the comparison to the original theorem
is complete and compiles. No definition, private helper, or arbitrary data choice was
introduced. Existential witnesses are used solely inside the proof of the theorem.

## No longer needed

No original import was removed: each original public import supports the signature.
The original direct proof dependencies are replaced by the comparison, module-completion
exactness, and exact-sequence interfaces; their geometric prerequisites remain in the
comparison node and have not been claimed as globally pruned.

The route no longer needs `lem-weil-pbc-finite-modules-noetherian-abelian`, or its
`Mathlib.Algebra.Category.FGModuleCat.Abelian` route: exactness is established directly
in `ModuleCat A`, then its kernel limit is reflected. It also no longer needs
`lem-weil-pbc-equivalence-injective-resolutions`; no injective resolutions are used.
No proof dependency imports of those nodes were present in the original module.

The original step-4 invocation of `lem-weil-pbc-adic-completion-noetherian` and
`Sheaf.RingTheory.AdicCompletionNoetherian` is unnecessary for the kernel transfer.
However, the existing affine-equivalence proof still reaches that result, so it is
not claimed as pruned from the transitive closure.

Complete list removed from the original node's direct `proof_deps` (these are not
claims of removal from the targets' import closure):

- `def-weil-affine-spectrum`
- `def-weil-pbc-coherent-formal-module`
- `def-weil-sheaf-of-modules-category`
- `lem-weil-pbc-abelian-full-subcategory-exact`
- `lem-weil-pbc-adic-completion-noetherian`
- `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `lem-weil-pbc-coherent-formal-modules-affine`
- `lem-weil-pbc-coherent-modules-kernel-cokernel-sum`
- `lem-weil-pbc-equivalence-injective-resolutions`
- `lem-weil-pbc-finite-modules-noetherian-abelian`
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`
- `lem-weil-pbc-module-restriction-open-immersion-colimits`
- `lem-weil-pbc-quasi-coherent-finite-type-affine`
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`
- `lem-weil-pbc-ringed-space-module-exactness-local-lifting`
- `pqf-lem-coherent-ft-locnoeth`

The comparison retains the geometric dependencies listed in its own node.
The three discarded routes named above are not needed for the algebraic assembly.
No module is claimed as globally pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the delivered statements. The original plan's intermediate abelian category
of finite completed modules is unnecessary: scalar restriction reflects kernel limits,
so ordinary A-linear module exactness suffices. The affine equivalence itself is
available for literal spectra, while this item's arbitrary affine open and specified
restriction require an additional geometric comparison interface. This is the new
remaining statement, rather than an assumption of completed exactness under a new name.

Read the original node and its dependencies' Lean signatures, the `sk-thm-p1` unit and
its realized nodes, and searched the existing Lean roots and Mathlib. This item is not
one of the unit's realized statements or steps; the unit route is preserved. Existing
Mathlib completion exactness supplied the algebraic part. Lean Finder returned related
module exactness and affine limit results; Loogle found `AdicCompletion.map_injective`;
scoped grep located `map_injective` and `map_exact` at lines 92 and 184. LeanSearch
returned Internal Server Error, recorded as unavailable in the new node.

The cited local Stacks tex sources are absent on this machine. Read the source's
public pages directly: https://stacks.math.columbia.edu/tag/0881 and
https://stacks.math.columbia.edu/tag/087W. The comparison follows their affine
identification, supplemented by the explicit quotient, arrow and limit-cone interfaces
of the existing project nodes. No literature file was written outside the sandbox.

Checked the comparison on zero modules, the empty affine open (zero ring), J = 0,
and J = A. Its hypotheses impose no injectivity of individual quotient maps. An
A-linear comparison is enough; completed-ring linearity need not enter the assembly.
Compiled both modules in import order with `lcompile.py`; the main proof is clean.

The second reader also found an inherited DAG bookkeeping cycle below the already
existing affine equivalence: `lem-weil-pbc-tower-limit-exact-surjective-kernels` uses
`new-tower-limit-induced-maps`, which uses the former node again. The path goes through
`lem-weil-pbc-coherent-formal-modules-affine-limit`,
`lem-weil-pbc-adic-tower-finite-limit`, and
`lem-weil-pbc-adic-tower-completed-free-surjection`. The original kernel node already
reached this same cycle via `lem-weil-pbc-coherent-formal-modules-affine`; this delivery
adds no edge to it. This is reported here for the maintainer rather than modifying
unowned nodes. It does not create a Lean import cycle or change the mathematical
comparison argument.

## New nodes

`lem-weil-pbc-formal-completion-affine-comparison` is the geometric part of the affine
argument, stated in `Sheaf.AlgebraicGeometry.FormalCompletionAffineComparison`. Its
strictly smaller remaining task is the original finite-module sequence and the
natural comparison of quotient-system limits and their arrows. Its source is the
affine identification of Stacks 0881 and equivalence 087W. Searches are recorded in
`searches.jsonl`; the new node records the actual unavailable LeanSearch response.
The blueprint search for completion found only distinct derived/coefficient completion
nodes, with no duplicate of this comparison. No change record is required because
all existing interfaces are unchanged. No forced adaptations were made.

## Second reading by K2

1. PASS. Independently diffed the existing module against the repository and compared
   the whole theorem signature through `:= by` byte for byte. It is identical:
   X and both Noetherian instances, I, h, U, hU, rho, hz, its exact equality h-rho,
   S and hS, both mapped-complex lets, and the Nonempty kernel-limit conclusion.
   No existing definition or visibility changed; the comparison is the only new
   declaration. There are no adaptations or change records.
2. PASS, with one explicitly reported dependency hole. Both delivered modules compile
   in import order with lcompile.py, without errors or warnings. Scratch copies with
   `#print axioms` show only propext, Classical.choice, Quot.sound and sorryAx for
   both declarations. The main theorem has no sorry; the comparison has exactly its
   named whole-proof sorry. Read both complete bodies: no forbidden declaration,
   no hollow definition, no new data definition and no arbitrary witness choice in
   a definition. Existential elimination occurs only in the proof of the main theorem.
3. PASS as a decomposition, not a complete proof. Read Stacks
   [0881](https://stacks.math.columbia.edu/tag/0881) and
   [087W](https://stacks.math.columbia.edu/tag/087W) and the existing
   coherentFormalModules_affine signature with its natural limit projections.
   The comparison contains the geometric identifications only. It does not assume
   completed injectivity, exactness or a limiting kernel fork. These are proved by
   the main module using AdicCompletion.map_injective and map_exact. Its hypotheses
   are exactly those of the original problem. Tested the mathematical construction
   on zero modules, the empty affine open, J = 0 and J = A: the zero quotient at
   power zero contributes no coordinate restriction; the other coordinates give
   respectively the original modules or zero. No injectivity of quotient-level
   first arrows is required. The comparison's docstring describes A, J, M and F,
   its reflection of limits, the linear equivalences and their natural arrow equations;
   its new node records those same claims, the source and all required fields.
   Independent searches with “inverse limit of global sections” and
   “restrictScalars” through Lean Finder, Loogle and scoped Mathlib grep found the
   scalar-restriction reflection/preservation interfaces, but no existing theorem
   giving this geometric comparison. Also searched lean/Sheaf and lean/WeilConjectures
   for completed affine comparisons and kernel statements. Existing torsion-controlled
   and thickening-system comparisons have different hypotheses and conclusions.
   Closing the remaining hole needs the affine transport and quotient-system
   identifications; it is not a short missing algebraic tactic.
4. PASS after import and report repair. Read the proof from the original conclusion
   downwards: compare the arrows, apply finite-module completion exactness, transfer
   injectivity and the two directions of Function.Exact, form fIsKernel, and reflect
   its mapped cone. Scalar restriction preserves limits and reflects isomorphisms;
   with limits in its source, Mathlib's reflectsLimitsOfShape_of_reflectsIsomorphisms
   justifies the prose construction of F. The affine equivalence and full inclusion
   reflect limits by full faithfulness, so no abelian finite-module detour is needed.
   All original public imports support the existing signature and remain unchanged.
   Moved ModuleCat's categorical exactness lemmas out of the comparison's public
   imports into a plain proof import in the main module; an omission scratch check
   fails at moduleCat_injective_f, confirming that import is needed there. Removed
   the comparison's separate public kernel-preservation import; it is unnecessary
   for its statement. A scratch compile of the main module confirms no separate
   kernel-preservation import is needed there either. The complete list of removed
   direct proof dependencies is now in No longer needed. No global module pruning
   is claimed. Read dag/units/sk-thm-p1.json: neither delivered node is a realized
   unit statement or step; its realized fields and chapter route are unchanged.
5. PASS. The existing node changes only proof, proof_deps and proof_origin. Its
   four steps follow the Lean assembly, and proof_deps is the union of their uses.
   The completion exactness node's Mathlib match supplies the completion theorems;
   the exact-sequence interfaces supply the categorical kernel. The new node's
   Lean statement is the comparison's signature verbatim. Checked its dependency
   statements: coherent kernels/cokernels and full inclusion for the original
   sequence; open restriction and affine cokernel sections for its exactness;
   Noetherian coherence and finite-type affine sections for finiteness; the tilde
   adjunction and natural affine formal equivalence for F and its limits;
   ideal-product, power and quotient formulas for the system identification.
   The comparison does not depend on the kernel item, and no unit record is changed.
   A recursive audit found an inherited cycle below the existing affine equivalence,
   recorded under Where the brief, the DAG or earlier work was wrong; the original
   kernel plan already reached it, and the delivery adds no edge to that cycle.

Second reading changed only imports and reporting: replaced the comparison's public
ModuleCat import with ShortExact, removed its unused public kernel-preservation import,
added a plain ModuleCat proof import to the main module, completed the direct-dependency
pruning inventory, and wrote this independent review. Existing signatures and both
proof bodies are unchanged by the second reading. Hole accounting remains one original
hole closed and one strictly smaller comparison hole added (net zero decomposition).
