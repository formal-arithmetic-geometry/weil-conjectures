## What changed

Reduced `AlgebraicGeometry.Scheme.singletonTensorDegreeComparisonHom_kernel` to
three strictly smaller statements: the ring of an iterated affine product, affine
coefficient sections for an arbitrary etale morphism, and additive evaluation of
the normalized comparison. All three modules are proof-only imports.

The main module proves the tensor-generator induction, scalar balancing, tensoring
and composing the two equivalences, and kernel cancellation. Its original public
signature and docstring are unchanged. The DAG now records the three intermediate
statements and the real algebraic argument. No definition, instance, visibility,
target statement, or existing interface changes.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.singletonTensorDegreeComparisonHom_kernel` (node
`new-etale-affine-singleton-tensor-degree-kernel`). Its proof has no internal holes
and compiles. This is a decomposition, not a complete geometric proof: one original
hole is closed and three strictly smaller holes are added.

Every remaining delivery hole:

- `AlgebraicGeometry.Scheme.singletonProduct_affine_ring`
  (`new-etale-affine-singleton-product-ring`).
- `AlgebraicGeometry.Scheme.exists_etaleAffineTensorSectionsEquiv`
  (`new-etale-affine-tensor-sections-equiv`).
- `AlgebraicGeometry.Scheme.singletonTensor_normalization_evaluation`
  (`new-etale-singleton-tensor-normalization-evaluation`).

Each is a public named theorem in its own new module, with its source and full
proof in words. The first does not involve a module sheaf or comparison map. The
second does not involve an indexed product or comparison map. The third uses no
affine hypotheses or injectivity conclusion. Existential equivalences and the
additive map are eliminated only inside a theorem proof; no data definition is
chosen from an unproved existence statement.

Edge cases checked mathematically: degree zero has one factor; zero modules, zero
rings, and empty affine schemes cause no exception. Neither covering nor faithful
flatness is needed for fixed-degree injectivity. The unit record has empty realized
statement and step lists; the affine tensor/Amitsur route of Tag 03P2 is retained.

Validation: all four modules compile without warnings, individually in import
order, in approximately 3--7 seconds each. The prescribed delivery dry run is the
final check; nothing is pushed by this worker.

## No longer needed

No original import is removed and no original geometric node is pruned. The binary
affine spectrum formula, pullback adjunction, quasi-coherence, affine sections, and
normalized composition inputs remain needed through the new geometric statements.
The original direct proof dependencies now occur below the appropriate new nodes.
Tensor induction and cancellation are proved directly and need no new sorry nodes.

## Where the brief, the DAG or earlier work was wrong

The saved attempt was blocked by a kernel timeout. Using the chosen product
expression directly in the equivalence assembly, instead of a local abbreviation,
lets the kernel check the reduction in approximately six seconds. The private
generic helper assembles the equivalences and their pure formulas; no proof is
split into additional files to evade the limit. No heartbeat override remains.
Direct evaluation from the normalization predicate still exceeds the local compile
budget, so the earlier evaluation statement remains a separate elementary part of
the reduction, with a complete construction described in its docstring.

The imported node's `created.item` names a module rather than a node, so
`blueprint_refs.py ancestor` computes None. New nodes preserve that mechanically
computed ancestor and record the actual affine clause of
`lem-sc-etale-affine-qcoherent` in `from.place`.

Read the stated proof dependencies and their Lean signatures, including the binary
`pullbackSpecIso`, `isQuasicoherent_pullback`, the tensor-pullback adjunction,
`exists_tensorPullback_affine_sections`, and normalized tensor-section restrictions.
Searches saved in `searches.jsonl` include LeanFinder for affine tensor sections and
indexed affine product rings, Loogle for indexed tensor induction and spectrum
pullbacks, and grep for the corresponding constructions. A further Loogle search
found `TensorProduct.congr_tmul`. Blueprint tensor search found no replacement for
the proposed intermediate statements. Sources checked: Stacks Tags 03P2 (affine
Cech/Amitsur calculation), 01JQ (affine fibre products), 01I9 and 01IA (affine module
pullback and sections), and 03DR (normalized section presheaf).

## New nodes

`new-etale-affine-singleton-product-ring` records affine product functions, including
the indexed pure-tensor projection formula, in
`Sheaf.AlgebraicGeometry.EtaleAffineSingletonProductRing`.

`new-etale-affine-tensor-sections-equiv` records unit-normalized affine coefficient
sections in `Sheaf.AlgebraicGeometry.EtaleAffineTensorSectionsEquiv`.

`new-etale-singleton-tensor-normalization-evaluation` records additive evaluation
at the unique outer index in
`Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizationEvaluation`.

No change record or forced adaptation is needed.

## Second reading by B2

1. Compared the delivered kernel module with the repository using diff. The sole
   existing public theorem's signature and docstring are byte for byte unchanged.
   Only its proof, proof-only imports, and private proved helpers are added. The
   three other modules are new; no definition, instance, or existing visibility
   changes, and no change record is required. Verdict: pass.
2. Compiled all four modules with lcompile.py in import order, without errors or
   warnings. Inspected all three named sorry theorems and all private helper bodies;
   there are no other holes or forbidden declarations. A scratch #print axioms
   check of all four public theorems reports only propext, Classical.choice,
   Quot.sound, and sorryAx. No data is chosen in a definition. Verdict: pass as a
   decomposition with three open geometric/evaluation obligations.
3. Read every split statement and its proof docstring. The product-ring theorem
   is the finite iteration of the affine binary fibre-product formula; the
   coefficient-sections theorem follows from affine pullback sections and the
   unit-normalized composition isomorphism. The evaluation theorem follows from
   the projection already used in the normalization predicate. All handle n=0
   (one factor), the zero ring, empty affine schemes, and the zero module. None
   restates injectivity. Independently searched LeanFinder for affine scalar
   extension of quasi-coherent sections, Loogle for PiTensorProduct.ext, and grep
   for tensor-pullback section/evaluation comparisons; read the upstream affine
   sections theorem and restriction definitions and related chart-coordinate
   proof. No complete replacement was found. Verdict: pass.
4. Read the proof from the kernel cancellation back to the tensor equivalence
   assembly and generator induction. Scalar balancing correctly moves the
   indexed-tensor scalar to the coefficient. All three new imports are used only
   by the proof and are plain imports. The sole original public import supplies
   the signature. The old direct dependencies on
   lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-module-pullback-quasi-coherent,
   lem-pc-module-pullback-adjunction,
   lem-weil-pbc-module-pullback-affine-sections, and
   lem-sc-etale-qcoherent-presheaf-functorial have moved under the new statements;
   none is globally pruned. Checked sk-prop-h2's empty realized lists; the affine
   tensor/Amitsur route remains intact. Verdict: pass; no shorter complete route
   located.
5. Compared the existing node with the repository: only proof, proof_deps and
   proof_origin differ. Checked the new node signatures against Lean, sources,
   natural-language proof steps, dependency unions, creation records and unit.
   Verdict: pass after replacing copied, irrelevant search records on the new
   coefficient and evaluation nodes with second-reader searches.

Changes by this reader: corrected those search records and added this review.
Tried closing normalization evaluation by composing the categorical projection
with AddEquiv.ulift.toAddMonoidHom, then applying hf. Both the ordinary elaboration
and a local transparency variant exceeded lcompile.py's 60-second limit; restored
its original named sorry. No compile-limit workaround or interface change was
introduced. The proof bodies delivered are otherwise unchanged.
