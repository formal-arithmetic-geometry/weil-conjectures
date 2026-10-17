## What changed

Repaired the duplicate-theorem refusal at returned head `cc2bc1994c`.
Removed the private theorem
`AlgebraicGeometry.Scheme.Modules.tensor_hom_ext_restriction_scalar` entirely.
The proof now applies the existing `AlgebraicGeometry.Scheme.Modules.tensor_hom_ext`
from `WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison`.
A direct `import all` makes that existing private theorem available in the proof.
The former `Sheaf` comparison module only re-exports the upstream module;
importing all of the re-export does not expose the upstream private theorem.
No source-library module is modified, and no replacement helper is declared.

The original proof of
`AlgebraicGeometry.Scheme.Modules.tensorHom_restriction_of_local_scalar`
is retained: cancel the inverse restriction tensor comparison, apply the imported
extensionality theorem, then compute both sides on every local pure tensor using
hbeta, halpha, the left unitor, and linearity of the local Hom section.
The existing public theorem's complete signature and docstring are unchanged.
The node's first proof step now names the imported theorem instead of the removed
helper. The bilinear-universal dependency remains as the justification for the
imported extensionality result; the monoidal formulas remain explicitly recorded.

The public-import cleanup is recorded in
`coord/changes/TensorHomRestrictionScalarImports.md`.
No other production module is changed. Removed the previous second-reading text
because it certified the returned proof; the next reader must review this repair.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.Modules.tensorHom_restriction_of_local_scalar`
(node `lem-pc-tensor-hom-restriction-scalar`).
Added 0 holes; 0 split off; 0 remaining holes in the item or other delivered modules.
Relative to the retained returned proof, the hole count stays zero and the actual
repair is removal of the duplicate theorem and reuse of the existing one.

The repaired item compiled cleanly in 28.0 seconds. A separate verification set
then compiled the repaired item (24.9 seconds), its unchanged direct consumer
`Sheaf.AlgebraicGeometry.CoherentOpenMapTensorExtension` (18.5 seconds), and an
axiom probe (1.6 seconds). The probe reports only `propext`, `Classical.choice`,
and `Quot.sound`. No assumptions, data constructions, or new statements are added.
The argument tests sections on every open and includes empty opens and zero modules.

## No longer needed

Removed the unused public import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.HomModule` from the original module.
The internal-Hom section action is already exported by the tensor product imports.

Removed the returned proof's direct import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal` along with the
local extensionality helper. Its universal property is used by the existing upstream
helper, whose proof is reused; its DAG dependency is therefore retained.

Replaced the direct comparison re-export import
`Sheaf.AlgebraicGeometry.Modules.RestrictionTensorComparison` with
`import all WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison`.
The re-export adds no needed declaration. No original proof-dependency node is
withdrawn, no new dependency on `QCohTensorResolutionRestrictionTensor` is added,
and no whole module is claimed unreachable from all targets.

## Where the brief, the DAG or earlier work was wrong

The returned helper was exactly the same statement as existing tensor extensionality
lemmas, as the landing checker reported. It is now deleted, and the original theorem
is imported and used. This directly addresses the sole return point, without renaming
or restating the duplicate.

The prior second reading correctly noticed that `import all` of the Sheaf re-export
could not expose its upstream private helper, but missed direct `import all` of the
upstream module. That direct import compiles and avoids both duplication and the much
larger public QCoh tensor-resolution module.

The existing node proof and proof dependencies describe tensor-bilinear uniqueness
and the monoidal section formulas. Only the first step's reference to the local helper
was replaced; its statement, source, unit, and Lean attachment are unchanged.
The unit's realization is untouched. Prior msearch records remain in `searches.jsonl`;
this repair additionally checked the two exact duplicates identified by the return
against the current source and selected the existing upstream helper.

## Second reading by M3

1. **Interfaces: pass.** Compared the delivered module with the current repository
   using `diff` and independently compared the theorem signature as text. The sole
   public theorem's complete signature is byte for byte unchanged and equals its
   node's `lean.statement`; its docstring is unchanged. There are no new declarations
   or definitions. The two import changes are declared in
   `coord/changes/TensorHomRestrictionScalarImports.md`. The unchanged direct consumer
   imports this module only for its proof, so the removed public import is not an
   exported dependency of that consumer.
2. **Proof and axioms: pass.** Independently compiled the delivered module cleanly
   (15.6 seconds). Compiled a scratch copy with `#print axioms` appended: exactly
   `propext`, `Classical.choice`, and `Quot.sound` (16.7 seconds). The same verification
   set compiled the unchanged direct consumer
   `Sheaf.AlgebraicGeometry.CoherentOpenMapTensorExtension` against this scratch copy.
   Inspected the complete proof and the imported extensionality and comparison proofs.
   There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`
   occurrences in the delivered Lean file. The comparison witness is eliminated
   locally in a proof; no data definition selects an arbitrary existence witness.
3. **Split statements: pass, vacuous.** Zero split-off statements and zero new nodes.
   The removed duplicate helper stays absent. The reused private `tensor_hom_ext`
   really states equality from equality on pure tensors on every open; its proof uses
   the already established sheaf tensor bilinear universal property. The local scalar
   calculation works on the empty open and for zero modules: no nonempty-open,
   nonzero-module, or global-generation assumption enters the argument.
4. **Route, pruning, and imports: pass.** Followed the proof from cancellation of the
   inverse restriction tensor comparison, through the existing tensor extensionality
   theorem, to evaluation of both maps on an arbitrary local pure tensor. The final
   equality is linearity of the component of `s` and the structure presheaf's identity
   law. A fresh LeanFinder query about local decomposable tensors returned module-level
   tensor extensionality and ordinary sheaf extensionality, neither a shorter
   replacement for the existing sheaf tensor result. Local source searches confirmed
   the reused result and found no replacement for the whole scalar-restriction theorem.
   The two public imports supply the signature's tensor/internal-Hom and scheme-module
   structures; the proof-only comparison import is correctly non-public and direct.
   `No longer needed` lists the removed imports; neither original proof-dependency node
   is dropped. The unit `sk-thm-picard-coherence` and its `realized` record are unchanged;
   this local tensor calculation replaces no step of its route.
5. **DAG: pass.** Only `proof` and `proof_deps` differ from the repository node.
   Their descriptions agree with the proof, and `proof_deps` is exactly the union of
   the proof steps' `uses`: restriction tensor comparison, internal Hom, bilinear
   uniqueness underlying the imported extensionality theorem, and monoidal formulas.
   Statement, source, proof origin, unit, chapter, and Lean attachment are unchanged.

Second-reading changes: appended this independent review and recorded the fresh
search in `searches.jsonl`; no Lean proof or node repair was needed. Closed one
original hole, added zero holes, and split off zero statements. The returned
same-statement helper has been replaced by reuse of the existing theorem, as required.
