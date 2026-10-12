## What changed

Replaced the sole sorry in `Sheaf.FieldTheory.ProjectiveMatrixDescent`,
`Field.exists_CSA_of_matrix_descent_action`, by a complete Lean proof from a strictly
smaller Galois-descent statement. The original signature and public imports are unchanged.
Added proof-only imports of `Sheaf.FieldTheory.MatrixDescentScalarMapBijective` and
`Sheaf.FieldTheory.MatrixFormCentralSimple`.

`Sheaf.FieldTheory.MatrixDescentInvariants` constructs the actual invariant K-subalgebra
of matrices and the explicit scalar-extension multiplication map. All closure obligations
and `Field.matrixDescentScalarMap_one_tmul` are proved; no algebra data is chosen from
an existence statement. The inverse used by `AlgEquiv.ofBijective` is uniquely determined
by this explicit map and its asserted bijectivity.

`Sheaf.FieldTheory.MatrixFormCentralSimple` proves
`Field.centralSimple_of_matrix_form` completely for arbitrary field extensions, in
independent universes. Finiteness descends by faithful flatness. Simplicity follows by
scalar-extending a proper two-sided-ideal quotient, using injectivity of ring maps from
simple rings, and reflecting injectivity by faithful flatness. Centrality follows by
contracting the scalar equality `1 tensor x = l tensor 1` with a K-linear functional
on L taking 1 to 1. The original theorem packages these proved properties as a CSA
with the explicit invariant carrier and obtains the descent equation by unit cancellation.

All four modules compiled together in import order with `lcompile.py --all`, without
warnings, before the records were written. The delivery dry run printed OK: local compilation and preflight pass except for the
second reading, which the second reader writes. Nothing was pushed.

## Proved and sorry left

Closed the original hole in `Field.exists_CSA_of_matrix_descent_action`
(node `lem-sc-projective-matrix-descent`). This is a decomposition, not an unconditional
sorry-free proof: one original hole is closed and one strictly smaller hole is added,
so the net hole change is zero.

Proved `Field.centralSimple_of_matrix_form`
(node `lem-sc-matrix-form-central-simple`) with no sorry and only Mathlib dependencies.
Proved the invariant-subalgebra construction, the scalar map, and
`Field.matrixDescentScalarMap_one_tmul` (node `def-sc-matrix-descent-invariants`).

The only sorry left anywhere in this delivery is
`Field.matrixDescentScalarMap_bijective` in
`Sheaf.FieldTheory.MatrixDescentScalarMapBijective`
(node `lem-sc-matrix-descent-scalar-map-bijective`). Its proof is exactly `by sorry`;
its docstring and node contain the finite Galois reduction, invariant spanning argument,
basis argument, and scalar-extension argument. It asserts bijectivity of a specified map,
not existence of an arbitrary CSA or a replacement for the original conclusion.

Edge cases checked mathematically: n=0 is allowed in the new bijectivity statement
(both algebras are zero and the empty basis applies), but excluded exactly where needed
in the matrix-form central-simplicity theorem. For n=1 and scalar b, invariants are
precisely K inside its separable closure, and the scalar map is the usual unit map.
For arbitrary scalar unnormalized b(1), conjugation by b(1) is identity and the
construction never assumes b(1)=1. The spanning argument uses independence of
field automorphisms, rather than division by the group order, so it works in
positive characteristic. No Galois or algebraicity assumption is needed for the
fully proved matrix-form lemma.

## No longer needed

No existing dependency nodes or modules were pruned. The original node had
no proof dependencies. The second reader removed six redundant direct imports from
new modules, all still provided by retained public import chains:

- `MatrixDescentInvariants`: `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`
  and `Mathlib.RingTheory.TensorProduct.Maps` (provided by `IsSepClosed`).
- `MatrixFormCentralSimple`: `Mathlib.Data.Matrix.Basic`
  and `Mathlib.RingTheory.SimpleRing.Defs` (provided by retained statement imports),
  `Mathlib.Algebra.Central.Basic` (provided by `Central.TensorProduct`), and
  `Mathlib.RingTheory.Ideal.Quotient.Operations` (provided by retained proof imports).

The existing item's public imports remain unchanged. Its full four-step route is retained: concrete invariants,
Galois scalar extension, descent of CSA properties, and the displayed descent equation.
No module has been claimed to leave the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The original node marked finite Galois descent, invariant basis selection, and descent
of central simplicity as elementary without naming dependency declarations. These
are substantial arguments. The delivery makes the invariant algebra concrete,
formalizes all of the central-simple descent and final conjugation calculation,
and isolates only the unformalized Galois scalar-extension step.

The original third-step dimension argument is replaced by a proved quotient/faithful-flatness
argument for simplicity and a proved linear contraction argument for centrality.
No statement or definition of an existing module changes, and no forced adaptations
are needed. The unit `sk-thm-br` and its route are unchanged.

The first dry run encountered a temporary launcher/repository tool mismatch:
`ImportError: cannot import name 'refuse_missing' from 'import_cycles'`.
The repository tool then refreshed externally to include that export; rerunning the
same command printed OK. No tool was edited or bypassed by this worker.

Mathlib searches used LeanFinder, Loogle, and source grep. LeanSearch returned HTTP
500 and is recorded as unavailable, never as evidence of absence. The Stacks source
was read at Tags 03R6 and 03R2; 03R6 only sketches twisting, so the explicit finite
Galois proof is identified as an agent expansion, as in the original node.

## New nodes

`def-sc-matrix-descent-invariants`: explicit invariant subalgebra and multiplication
map, realized by `Sheaf.FieldTheory.MatrixDescentInvariants`. All data and proofs
in this module are constructed without sorry.

`lem-sc-matrix-descent-scalar-map-bijective`: the strictly smaller remaining
finite Galois descent step, realized by
`Sheaf.FieldTheory.MatrixDescentScalarMapBijective`, with one sorry.

`lem-sc-matrix-form-central-simple`: the fully proved generic descent of centrality,
simplicity, and finite dimensionality from a nonempty matrix form, realized by
`Sheaf.FieldTheory.MatrixFormCentralSimple`.

Updated the original node's proof, proof dependencies, and proof origin to match
these modules. There are no interface change records because all existing signatures
and visibility are preserved.


## Second reading by X2

1. **Existing interface unchanged: PASS.** Diffed the only existing delivered module,
   `ProjectiveMatrixDescent`, against the repository. Its sole existing declaration,
   `Field.exists_CSA_of_matrix_descent_action`, has a byte-for-byte identical signature,
   including every hypothesis, universe and clause of the conclusion. Only two plain
   proof imports and the proof body are added. All other delivered modules are new.
   No target, existing definition, visibility or public import was changed; no change
   record or forced adaptation is needed.

2. **Kernel proofs and concrete data: PASS with the reported open step.** Independently
   compiled all four files in import order through `lcompile.py`, both before and after
   removing redundant imports, without errors or warnings. Searched every delivered
   Lean file for forbidden declarations and sorry: the sole hole is exactly `by sorry`
   in `Field.matrixDescentScalarMap_bijective`. Appended `#print axioms` probes through
   `lcompile.py` for all six delivered declarations. The invariant subalgebra, scalar
   map, one-tensor formula and central-simplicity lemma use only `propext`,
   `Classical.choice`, `Quot.sound`. The bijectivity lemma and original theorem also
   use `sorryAx`, exactly as reported. The invariant carrier and multiplication map
   are explicit constructions; `AlgEquiv.ofBijective` chooses only their uniquely
   determined inverse. No arbitrary algebra witness comes from an unproved existence
   theorem. The quotient/faithful-flatness and linear-functional centrality proofs
   were read line by line and establish all three CSA properties.

3. **Split statement true and strictly smaller: PASS.** Read its complete finite
   Galois proof in the docstring and node, and checked compactness/finite quotient,
   preservation of the finite fixed field, invariant averaging, independence of
   automorphisms, and the invariant-basis coefficient argument. This is scalar
   extension of a specified invariant algebra, without the original CSA existence
   conclusion or descent equation. For n=0, compiled a scratch proof of bijectivity
   using subsingleton source and target, with no action hypotheses or sorry. For n=1,
   conjugation is trivial and the statement is the usual fixed-field scalar extension.
   Checked unnormalized scalar b(1), imperfect base fields, and characteristic dividing
   the finite group order: the argument uses no division by that order. Independently
   searched LeanFinder for fixed-vector basis descent, Loogle for locally constant
   bijective maps and tensor centrality, and Mathlib/upstream/Sheaf with alternate
   terms. No reusable complete descent theorem was found. The tensor centrality
   results require centrality over K of the tensor algebra, whereas here it is central
   over L. The remaining finite Galois step cannot be closed in a few minutes.
   This delivery closes one original hole and adds one smaller hole: a decomposition
   with net zero holes, not an unconditional proof of the original theorem.

4. **Route and pruning: PASS after import cleanup.** Read the original top-down proof
   plan and `dag/units/sk-thm-br.json`. The unit's sole Brauer injection/Tsen step and
   all its realized fields are untouched; this construction stays below that unit.
   The implemented reduction retains concrete invariants, Galois scalar extension,
   descent of CSA properties, and the final conjugation equation. Removed the six
   redundant new-module imports listed above; all required APIs remain available
   through retained imports. Both new proof imports of the original item are needed.
   Its old proof_deps was empty, so no old dependency is omitted from the pruning list.
   No module is claimed to leave the targets' import closure.

5. **DAG and provenance: PASS after record cleanup.** Matched each node's statement
   with its Lean declaration and the explicit construction it describes. Verified
   that every proof_deps equals the union of its steps' uses and follows the actual
   proof. The three new nodes have source, origin, searches, creation, blueprint,
   chapter/unit and Lean records. Recorded their declaration signatures verbatim
   from the source using the preflight convention (the definition signature omits
   the `noncomputable` modifier), and added
   the independent search results to the relevant new nodes. Read Stacks Tags
   03R6 and 03R2 directly: the former sketches twisting, while the explicit finite
   Galois descent and the general-field-extension CSA proof are correctly marked
   as agent expansions. No unsupported quotation or claim of a source proof is used.

Changes by this reader: removed six redundant direct imports from the new modules;
made their new-node signature records verbatim; recorded independent search results;
updated the pruning report and added this review. No mathematical statement or proof
body needed repair, and no additional hole was introduced.

The first second-reader dry run rejected the definition signature record because
preflight expects it without `noncomputable`. Corrected that record to the tool's
signature convention; the Lean declaration itself remains noncomputable and unchanged.
