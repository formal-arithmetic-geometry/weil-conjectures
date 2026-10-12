## What changed

Proved `AlgebraicGeometry.affine_base_piece_tensor_base_change_instance` without changing its
statement, definitions, or imports. Added three proved private helpers in the same module:
`composite_pullback_square`, `restricted_composite_base_change`, and `tensor_pullback_arrow`.
The first two identify the restricted composite base change with an ordinary pullback arrow;
the third transports that arrow to the spectrum of the tensor map. Updated the existing node's
proof and proof_origin to record this Mathlib-only route.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.affine_base_piece_tensor_base_change_instance`
(node `lem-weil-pbc-affine-base-piece-tensor-base-change-instance`).
No holes added or left. All three private helpers are proved. This is a proof, not a decomposition.
Local single-file compilation succeeds. A declaration-local `linter.unusedVariables` option
suppresses the original signature's unused-variable warning for its explicit algebra binder `aA`;
the signature is preserved, and the option has no effect on downstream files or proof checking.

## No longer needed

None. There were no Sheaf proof imports or proof_deps to remove. The proof does not use
`Sheaf.AlgebraicGeometry.AffineChartBaseChangeIso` or
`Sheaf.AlgebraicGeometry.AffineChartTensorComparison`; these were searched as possible routes,
not imported, and are not claimed to be globally pruned. All three existing Mathlib imports remain
needed for pullbacks, the Over pullback map, and tensor-product maps respectively.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The node's previous single-step plan did not list declarations
for its geometric glue. Mathlib's `Scheme.Hom.isPullback_resLE` supplies that step directly.
The proof covers empty opens and zero rings through unrestricted pullback and spectrum identities.

## Second reading by D2

1. PASS: Compared the sole delivered module with the repository version. The existing
   theorem signature is byte-for-byte identical; its docstring, three public imports,
   namespace, and universes are unchanged. The only additions are proved private helpers
   and declaration-local elaborator/linter options. No definition or statement change
   requires a change record.
2. PASS: Independently compiled the module with lcompile.py without errors or warnings.
   Scanned the delivered Lean for sorry and forbidden declarations/options: none found.
   Compiled a scratch copy with #print axioms for the public theorem and each of the three
   private helpers: all use only propext, Classical.choice, and Quot.sound. The proof
   constructs pullback isomorphisms explicitly; it chooses no arbitrary unproved witness.
3. PASS: No statements were split off and no holes were added. Read the private helpers
   as reductions: pullback associativity, open restriction, then affine tensor comparison.
   Their arguments allow empty opens, empty schemes and zero rings, with no nonemptiness
   or nonzero assumption. Searched upstream, Sheaf and Mathlib using arrow/pullback and
   spectrum/tensor naturality terminology. The affine chart lemmas provide ingredients
   but no shorter complete proof of the composite restricted arrow comparison.
4. PASS: The proof closes the top hole directly from Mathlib universal properties and
   projection identities, without importing open Sheaf statements. Each public import
   provides notions in the unchanged statement (scheme pullbacks, Over.pullback, tensor
   maps). The old proof_deps is empty, so No longer needed is complete. Read
   dag/units/sk-thm-p1.json and its realized routes: this descendant calculation is below
   the unit level, and no realized statement or step is bypassed or removed.
5. PASS: Compared the existing node JSON with the repository version. Only proof and
   proof_origin differ; proof_deps remains empty. The two recorded proof steps describe
   precisely the geometric restriction and algebraic tensor comparison implemented in Lean.
   The Lean declaration record still reproduces the unchanged signature. No new nodes.

Changes by the second reader: appended this review and recorded the independent compilation
and axiom checks. No Lean or node repair was needed.
