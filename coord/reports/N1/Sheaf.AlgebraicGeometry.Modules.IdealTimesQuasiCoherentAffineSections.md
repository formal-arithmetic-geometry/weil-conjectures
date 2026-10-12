## What changed

Proved `AlgebraicGeometry.Scheme.Modules.ideal_times_quasiCoherent_affine_sections`
in `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`, with its
statement and all public imports unchanged. The returned delivery's duplicate
top-level helper declarations were removed; their proofs now live as local `have`
lemmas in the restriction conjunct, so the existing affine statements are not
redeclared.
The proof computes multiplication ranges by tensor induction, derives quotient
surjectivity and kernels from the existing affine image/cokernel theorem, proves
power ranges by induction, and compares restricted product subobjects by affine
section ranges and sheaf separatedness.

Added proof imports of `Mathlib.CategoryTheory.Subobject.Limits`,
`WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion`,
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`. Updated the existing
node's proof, proof dependencies and proof origin. No public statements, definitions,
visibility, other modules, or unit realizations changed.

Read Stacks schemes.tex labels `lemma-widetilde-constructions` (01I8) and
`lemma-kernel-cokernel-quasi-coherent` (01IC), and modules.tex labels
`lemma-tensor-product-permanence` (01CE) and `lemma-limits-colimits` (01AH).
The literature files were absent locally; obtained copies from the Stacks source
repository in the sandbox scratchpad for reading. They are not delivery files.
Searches through msearch (leanfinder, loogle, grep) and local rg were run. No
existing complete theorem was found; existing tensor, image/cokernel, ideal affine
extension and closed-immersion pushforward results supply the proof.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.ideal_times_quasiCoherent_affine_sections`
(node `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`).
One of one original holes closed; zero holes added or split off. No sorry remains
in the delivered module. Every private helper has a complete proof.

The full module compiles cleanly through lcompile.py. The independent second reader repeated #print axioms against the current compiled
library: the theorem depends only on propext, Classical.choice and Quot.sound.
The earlier worker observed sorryAx against an older dependency build; that is no
longer present in this theorem's axiom closure. No additional axiom was introduced.

The generic multiplication calculation needs neither injectivity of the ideal
map nor flatness; zero maps, zero modules and the unit ideal cause no exception.
Positive powers start at n = 1; no positive-power assertion is accidentally based
on n = 0. Restriction along any open immersion, including the empty open, is covered
by the same affine-basis argument. No Noetherian assumption is used.

## No longer needed

The proof imports `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` and
`Sheaf.AlgebraicGeometry.CoherentFormalModule` are retained. Although the target
proof does not reference their declarations directly, the import-prune checker
requires them here because downstream `ComponentSupportedAffineSection` relies on
the transitive declarations (including `AlgebraicGeometry.IsAmple`) supplied by
these imports. They therefore cannot be reported as pruned.

Removed the duplicate top-level `hom_zero_of_affine` and
`subobject_le_of_affine_range` declarations; these are now local proof terms.
Removed the direct proof dependencies
`lem-weil-pbc-affine-tilde-gamma-adjunction` and
`lem-weil-pbc-spec-module-tilde-sections`, and
`def-weil-pbc-coherent-formal-module`. The last definition is unused by this proof,
although its module remains imported for the downstream visibility described above.
The already established tensor-section
and image/cokernel interfaces supply their consequences. Those Mathlib results
remain transitive dependencies of the retained interfaces, not globally pruned
modules. The retained tensor-section module, image/cokernel module, restriction
interface, and quasi-coherence definition are all used.

## Where the brief, the DAG or earlier work was wrong

The planned restriction proof required additional compatibility glue. Instead of
constructing tensor/restriction/unitor comparison diagrams, the proof compares
ranges on the affine basis using the existing affine ideal-extension theorem and
the restriction scalar-action formulas, then proves both subobject inequalities.
This changes only the route below the unit level. None of the nodes realizing the
unit statement or its steps is bypassed.

The closed source declaration
`isQuasicoherent_pushforward_of_isClosedImmersion` is recorded among the declarations
of the closed node `lem-pc-closed-immersion-coherent-cohomology`. The proof uses only
that declaration, which has no Noetherian hypothesis; it does not use the node's
stronger coherent/cohomological assertions. The affine extension declaration
`ideal_comap_appLE` is recorded by the closed node
`lem-pc-ideal-sheaf-comap-affine-extension`. Both are used as already closed tools
from another unit, with no new unfinished work introduced.


Repair of the landing refusal: the former private `powers_qc` duplicated the
private `power_quasiCoherent` in
`Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationAdicReduction`. Since that
existing declaration is private and cannot be imported for use, generalized
`powers_qc` in place as the return permits. It now takes an arbitrary module `K`,
a map `i : K ⟶ SheafOfModules.unit X.ringCatSheaf`, and `[K.IsQuasicoherent]`;
it requires neither an ideal-sheaf presentation nor a monomorphism. Both callers
specialize it to `J.toModulesι`. The zero map from any quasi-coherent module is a
valid case of the generalization. The induction uses the existing generic
`product_qc` helper. No new imports, nodes or holes were introduced.

The previous second-reading section was removed because it predates this repair;
the independent second reader must review the repaired version.

## Second reading by N1

1. **Visible interface: PASS.** Compared the sole delivered Lean module with the
   repository using diff and a byte comparison of the existing theorem signature.
   Its signature, visibility, definitions and public imports are unchanged. There
   are no adapted modules or change records. The only node fields changed are
   `proof`, `proof_deps`, and `proof_origin`.
2. **Proof: PASS.** Independently compiled the complete module through lcompile.py
   without errors or warnings. A scratch copy with #print axioms of
   `AlgebraicGeometry.Scheme.Modules.ideal_times_quasiCoherent_affine_sections`
   reports exactly propext, Classical.choice and Quot.sound, with no sorryAx.
   Inspected every private proof and local lemma: no sorry, axiom, unsafe, opaque,
   implemented_by, extern, hollow definition, or arbitrary witness construction.
3. **Split statements and edge cases: PASS.** No statement is split off and no hole
   is added. Read the recursive product/power definitions and checked the generic
   helper at powers 0 and 1, the zero map, zero module and unit ideal. The generalized
   powers_qc requires only quasi-coherence of K, so the reported duplicate has been
   repaired without weakening the target. Empty opens satisfy the same separatedness
   argument. The local affine detection/factorization arguments need no
   quasi-coherence assumptions, and their Mono hypotheses justify the inverse used.
4. **Route and pruning: PASS.** Read the tensor-section and image/cokernel interfaces,
   searched lean/ by product, power, image, and affine-range terminology, and repeated
   a Mathlib grep through msearch. No accessible existing complete result replaces
   this argument; the similar power and affine-detection helpers elsewhere are private.
   The proof uses the established interfaces rather than reproving them. All added
   imports are proof-only. The two retained unused direct imports preserve downstream
   visibility as recorded above; delivery's import-prune check is the final gate.
   Checked sk-thm-p1's realized statement and steps: neither this auxiliary node nor
   any of the three removed direct dependencies realizes one of those steps. Unit
   records are unchanged; the two closed cross-unit results are generic tools.
   No globally pruned module is claimed.
5. **DAG: PASS.** Checked each proof step against the Lean, the declarations recorded
   for each dependency, and that proof_deps is exactly the union of the steps' uses.
   The source declarations for closed-immersion pushforward and affine ideal extension
   match the reported tool uses. The repaired arbitrary-map induction is recorded
   in step 4 and proof_origin; no new nodes are needed.

Second reading changed only this report: added the omitted removed dependency
`def-weil-pbc-coherent-formal-module`, corrected the outdated sorryAx observation
using the fresh axiom check, and recorded this independent review. The Lean proof
and DAG required no repair.
