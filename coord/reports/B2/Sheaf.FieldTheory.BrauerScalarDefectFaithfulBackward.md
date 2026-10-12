## What changed

Replaced the sole `sorry` in `Sheaf.FieldTheory.BrauerScalarDefectFaithfulBackward`
with a complete Lean proof of `Field.brauerEquivalent_of_brauerScalarDefect_eq`
from two strictly smaller mathematical inputs. Its signature and existing docstring
are unchanged. Added proof-only imports of `Mathlib.RingTheory.MatrixAlgebra`,
`Mathlib.LinearAlgebra.Matrix.ToLin`, `Sheaf.FieldTheory.CentralSimpleTensorEnd`,
and `Sheaf.FieldTheory.BrauerScalarDefectTensorSplit`.

The descent input supplies `A ⊗ Bᵐᵒᵖ ≃ M_n(K)` for positive n. The algebra input
asserts bijectivity of the existing, explicitly constructed `AlgHom.mulLeftRight K B`.
The main proof uses its uniquely determined inverse and `Module.finBasis K B` to
construct `Bᵐᵒᵖ ⊗ B ≃ M_m(K)`, with m = dim_K B > 0. It then composes the actual
Mathlib tensor associator, commutator, congruences, and matrix–tensor equivalences:

`M_m(A) ≃ A ⊗ M_m(K) ≃ A ⊗ (Bᵐᵒᵖ ⊗ B) ≃ (A ⊗ Bᵐᵒᵖ) ⊗ B ≃ M_n(K) ⊗ B ≃ M_n(B)`.

This implements the split-tensor criterion in Lean rather than leaving that criterion
as another hole. No new definitions, arbitrary choices of definition data, existing
interface changes, or adaptations are delivered. The item's DAG proof and
proof dependencies now describe this composition. The unit's route is preserved;
`dag/units/sk-thm-br.json` has no realized node binding that this proof bypasses.

## Proved and sorry left

Closed the direct hole in `Field.brauerEquivalent_of_brauerScalarDefect_eq`
(node `lem-sc-brauer-scalar-defect-faithful-backward`). No `sorry` remains in the
item module. This is a decomposition, not an unconditional proof: one upper hole
closed and two lower holes added, giving net holes closed minus added = -1.

Every remaining delivered hole:

- `Field.tensor_opposite_split_of_brauerScalarDefect_eq`, in
  `Sheaf.FieldTheory.BrauerScalarDefectTensorSplit`, node
  `lem-sc-brauer-scalar-defect-tensor-split`. It is the Galois-descent part only:
  its conclusion is a splitting of the tensor product, not Brauer equivalence.
- `Field.centralSimple_mulLeftRight_bijective`, in
  `Sheaf.FieldTheory.CentralSimpleTensorEnd`, node
  `lem-sc-central-simple-tensor-end`. It involves a single central simple algebra,
  no scalar-defect relation, and no cohomology. It asserts a property of a concrete
  map, so its inverse is uniquely determined.

All three modules compiled together in import order using the prescribed lcompile.py.
The main proof compiles without warnings. Both lower holes are complete public theorem
proofs `:= by sorry` with sources, full proof descriptions, and matching node records.
The delivery dry run also runs the required axiom probes.

## No longer needed

None. No existing import was removed, and no existing node or module was pruned.
The original public import `Sheaf.FieldTheory.BrauerScalarDefect` is needed by the
statement. The four added proof imports are used by the explicit proof. The split-tensor
Brauer criterion is implemented directly with Mathlib rather than introduced as an
additional unproved theorem or imported as another module.

## Where the brief, the DAG or earlier work was wrong

The original node's only proof dependency was the scalar-defect definition. That
contains no descent theorem or canonical enveloping-map bijectivity result, so its
single prose step could not be obtained by applying its sole recorded dependency.
This delivery makes those two missing mathematical inputs explicit and proves all
of the matrix-amplification glue between them and the original conclusion.

Searches of both project roots, Mathlib, and the blueprint found no existing modules
for either new input. LeanFinder returned the Brauer-equivalence definition and scalar
Hilbert 90, not matrix descent; for the enveloping map it returned CSA and centrality
facts, not central-simple-to-Azumaya. Mathlib's Azumaya bijectivity lemma requires the
stronger `IsAzumaya` assumption. LeanSearch returned Internal Server Error and is
recorded as unavailable, not as evidence of absence. The exact executed searches are
in searches.jsonl. Blueprint keyword and Tag 074I searches found no duplicate.

The source pages read were Stacks Tags 03R7 (injectivity), 0DVG (the continuous
coboundary formula), 074G (tensor central simplicity), and 074I (canonical enveloping
map). New proof explanations expand those steps; they do not assume the field Brauer
comparison or its injectivity, which would be circular.

Edge cases checked mathematically: for A=B the descent input splits A⊗Aᵐᵒᵖ; for split
matrix algebras it gives the usual matrix tensor product. For the enveloping input
A=K gives the canonical multiplication action, and A=M_r(K) gives the matrix-unit
isomorphism. Neither result assumes K perfect or algebraically closed. Zero matrix
sizes are excluded by positive splitting sizes and nontriviality of every CSA; the
main proof formally proves positivity of dim_K B. The opposite algebra and inverse
transpose ensure that the second defect is inverted rather than multiplied.

## New nodes

`lem-sc-brauer-scalar-defect-tensor-split` records precisely the descent step from
equal continuous scalar-defect classes to a positive matrix splitting of A⊗Bᵐᵒᵖ.
Its full source-based proof explains opposite lifts, cancellation by a continuous
scalar coboundary, reduction to a finite Galois extension, and matrix descent. Its
module is `lean/Sheaf/FieldTheory/BrauerScalarDefectTensorSplit.lean`.

`lem-sc-central-simple-tensor-end` records bijectivity of the actual canonical
left-right multiplication map of one finite-dimensional central simple algebra.
Its proof uses simplicity of the enveloping algebra to get injectivity and equality
of finite dimensions to get surjectivity, following Stacks Tag 074I. Its module is
`lean/Sheaf/FieldTheory/CentralSimpleTensorEnd.lean`.

There are no change records because no existing statement, definition, signature,
or public import changes.

## Second reading by B2

1. **Interface and accidental changes.** I compared all three delivered Lean modules with the repository versions. The existing target theorem signature and docstring are unchanged; the two additional modules are new declarations with the signatures recorded in their node files. No target, definition, or existing public declaration was altered.

2. **Proof validity.** I compiled the three modules together with the prescribed `lcompile.py --all` command. The target proof has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `debug.skipKernelTC`; the only remaining `sorry`s are the two named split-off theorems, each a public theorem with a source-based proof docstring. The matrix/tensor composition typechecks and uses positive sizes `m` and `n`.

3. **New statements.** `tensor_opposite_split_of_brauerScalarDefect_eq` and `centralSimple_mulLeftRight_bijective` are strictly smaller inputs than the target and are stated for the concrete constructions used by the proof. Their hypotheses and conclusions are unchanged by this reading, and each has a matching DAG node and source explanation. Searches recorded in `searches.jsonl` found no duplicate declaration.

4. **Pruning and dependencies.** The proof uses every added import and every listed proof dependency; no import or node can be removed. The route retains the unit's tensor-splitting and matrix-amplification steps and does not bypass a realized unit node. The target node's proof and `proof_deps` agree with the Lean composition.

5. **Axioms and edge cases.** The modules compile without warnings. The target proof only invokes standard tensor, matrix, and finite-dimensional algebra equivalences plus the two split-off inputs; positivity excludes zero matrix sizes. The edge cases `A = B`, `A = K`, and split matrix algebras are consistent with the statements. No statement or definition is hollow.

I corrected the report by adding this second-reading record; no Lean proof changes were needed.
