## What changed

Completed `AlgebraicGeometry.coherentKernel_idealProduct_completion_zero` in
`Sheaf.AlgebraicGeometry.CoherentKernelIdealProductCompletionZero`, preserving its
statement. Coherence follows from the existing coherent kernel/submodule closure.
For each affine open, kernel sections map into the kernel of the completed map.
The assumed ideal-power annihilation, extended by submodule scalar-product induction,
kills the image of every product section in the completion of F. Injectivity of the
completed product inclusion then kills its canonical completion image. Projecting to
each quotient and using the affine quotient isomorphism proves zero sections; the
existing affine-basis vanishing lemma proves global vanishing.

Added proof-only imports of
`Sheaf.AlgebraicGeometry.IdealDataRecursivePowerComparison` (with `import all`) for
its proved `idealData_quasicoherent`, `powers_qc`, `product_qc`,
`multiplication_range` and `powers_range` helpers, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` for
`Scheme.Modules.isZero_of_forall_affineOpens`. Use `import all` for
`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` to access the existing
`finite_sections_of_finiteType` helper in the published build; the source now
exports that same theorem publicly upstream. No statements, definitions,
visibility or public imports changed. The node records the completed argument.

The recursive-power comparison node is used only as a generic tool for affine
multiplication ranges and quasi-coherence; its proof has already been completed.
This does not change any unit statement or step. If a recorded tool approval is
needed, the maintainer may record this existing-node use; no `tool_uses` field was
added by the worker.

Validation: single-file `lcompile.py` succeeds, with no warnings and no textual
`sorry`; the explicit power-zero branch handles t = 0. No nonempty scheme,
nonzero ring, properness or faithful-completion hypothesis is used. The source
calculation was checked in Stacks `coherent.tex`, Lemma `lemma-existence-tricky`
(Tag 088A), and `algebra.tex`, Lemmas `lemma-completion-tensor` and
`lemma-completion-flat` (Tags 00MA and 00MB).

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.coherentKernel_idealProduct_completion_zero`
(node `lem-weil-pbc-coherent-kernel-ideal-product-completion-zero`).
Added 0 holes; 0 holes remain in this delivery. No split-offs.
This is a proof from existing declarations, including
`AlgebraicGeometry.formalCompletion_affine_sections`, whose independent obligation
is outside this delivery.

## No longer needed

Removed the direct proof imports
`Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum` and
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`.
Removed their nodes `lem-weil-pbc-coherent-modules-kernel-cokernel-sum` and
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections` from the item's direct
`proof_deps`. Kernel coherence is supplied by
`lem-weil-pbc-coherent-kernel-cokernel-locnoeth`; the removed coherence module
remains a transitive dependency. The product calculation uses the already proved
helpers of `lem-pc-ideal-data-recursive-power-comparison` instead. Both removed
modules remain transitively imported by retained dependencies, so no additional
module becomes unreachable solely through these direct-import removals.

Removed the redundant `import all` of
`Sheaf.AlgebraicGeometry.CoherentFormalModule`, retaining its unchanged public
import. Changed the proof-only `import all` of
`Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian` to a regular
import: no private restriction helper is needed. No completed-kernel equality,
completion tensor-product isomorphism, formal affine equivalence or local
faithfulness result is imported for this proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The existing DAG already describes the shorter
injectivity argument actually implemented; it avoids the stronger completed-kernel
and tensor-product assertions mentioned in the declaration's original docstring.
The current source has retired the original private-helper modules into upstream
re-export wrappers, while the published build still has their original versions.
An isolated module-system check confirmed that `import all` on a re-export wrapper
does not expose the upstream module's private names. The final imports therefore
use the identical proved generic helpers from the existing, unretired recursive-power
comparison module. This resolves that compatibility issue without copying helpers
or editing any dependency.

## Second reading by S4

1. Compared the delivered Lean file and node with the shared repository using
   `diff -u`. Verdict: pass. The sole existing theorem's signature is byte for
   byte unchanged (also checked programmatically); all existing private helper
   signatures and bodies, definitions, docstrings, visibility, and the public
   import are unchanged. The only Lean changes are proof-only imports and the
   replacement of the original theorem's `sorry`. There are no change records,
   new statements, or adapted modules.
2. Read the whole module and compiled it through `lcompile.py`: no errors or
   warnings. Scanned the delivered Lean for forbidden declarations and holes:
   none. Compiled a scratch copy with `#print axioms` for
   `coherentKernel_idealProduct_completion_zero`, `completionSectionsUnit`,
   `completionSections_dictionary`, and `completionSections_map_injective`:
   each uses exactly `propext`, `Classical.choice`, and `Quot.sound`, with no
   `sorryAx` in the compiled environment. Verdict: pass. The canonical section
   map is constructed by `limit.lift`; the quotient and completion isomorphisms
   are obtained from the existing theorem whose projection equations determine
   them. No arbitrary data are chosen from an undetermined existence theorem.
3. Verdict: pass; no split-off statements or new holes exist. Checked the affine
   multiplication and power helpers against their source proofs, and completion
   injectivity against Mathlib's `AdicCompletion.map_injective` (only the target
   section module must be finite). The zero-power branch explicitly identifies
   the unit ideal. The proof also covers a zero ring, empty scheme, zero module,
   and either zero or unit completion ideal; it never uses faithful completion.
4. Verdict: pass. Searched the existing Lean library for the completion/product
   conclusion and reviewed the existing search results; the direct Mathlib
   completion-injectivity route already used by the proof is appropriate.
   Every retained proof import supplies a referenced declaration or a needed
   private helper; `import all` is required for the published private helpers.
   All removed old direct dependencies are listed under `No longer needed`.
   Read `dag/units/sk-thm-p1.json`: this node is below its realized unit steps,
   and no unit statement, step, or realization is bypassed. The recursive-power
   comparison helpers are generic affine product tools.
5. Compared the node's four proof steps, dependency union, and proof origin
   with the actual Lean proof and the declarations of its dependencies.
   Verdict: pass. Coherence, the evaluated completion comparison, annihilation
   by scalar-product induction, completion injectivity, and affine quotient
   vanishing are all reflected in the node. The unchanged statement agrees with
   the Lean. No new nodes need validation.

Changed in this second reading: this report only. The proof and DAG passed
unchanged. The scratch axiom audit also strengthens the original validation:
although the shared source currently lists `formalCompletion_affine_sections`
as open, the published compiled dependency used for this check contributes no
`sorryAx` to this theorem. The original hole count remains 1 closed of 1,
0 added, 0 split off; no whole-module pruning is claimed.
