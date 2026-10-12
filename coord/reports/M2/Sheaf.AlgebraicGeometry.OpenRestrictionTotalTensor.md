## What changed

Replaced the first worker's assembly restatement with a real reduction. The existing
`AlgebraicGeometry.openRestriction_totalTensor_iso` keeps its exact signature and local
monoidal instance. Its proof now assembles the module comparisons into a bicomplex
isomorphism with two applications of `HomologicalComplex.Hom.isoOfComponents`, then
composes `HomologicalComplex₂.total.mapIso` with the inverse of the already proved
upstream `HomologicalComplex₂.mapTotalIso`.

Added `Sheaf.AlgebraicGeometry.OpenRestrictionTensorNaturality` with
`AlgebraicGeometry.exists_openRestriction_tensor_natural`: the natural tensor comparison
for module objects, without complexes or totalization. This is the one remaining hole.
The module has a source, a complete proof in words, and a matching node. Its statement
imports are public; `RestrictionTensorComparison` is a plain proof-dependency import.
The item's two added imports are plain proof imports. Existing public imports are unchanged.

Deleted the proposed `OpenRestrictionTotalTensorAssembly.lean` and its node from the delivery.
No existing statement or definition changed, so there is no change record.

## Proved and sorry left

Hole closed in the item's body:
`AlgebraicGeometry.openRestriction_totalTensor_iso`
(node `lem-pc-open-restriction-total-tensor`).

Hole added:
`AlgebraicGeometry.exists_openRestriction_tensor_natural`
(node `lem-pc-open-restriction-tensor-natural`), in the new module
`Sheaf.AlgebraicGeometry.OpenRestrictionTensorNaturality`.

This is a decomposition: one upper hole closed and one strictly lower, module-level hole
added; net holes closed is zero. The original theorem still depends on `sorryAx` through
the new module theorem. No theorem in this delivery is claimed to have closed the entire
import-closure proof. The original module has no remaining `sorry`; the new module has
exactly the named theorem above. No data definition uses a hole or chooses an arbitrary
witness of an unproved existence theorem. The tensor comparisons are unpacked only inside
a proposition proof.

Both delivered modules compile locally without warnings. A scratch-copy `#print axioms`
check reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the item;
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the split theorem; and only `propext`, `Classical.choice`, `Quot.sound`
for the upstream `HomologicalComplex₂.mapTotalIso`.

## No longer needed

The item's direct import of `Sheaf.AlgebraicGeometry.Modules.RestrictionTensorComparison`
is replaced by the new naturality module. It remains a proof dependency of that lower
module, so no library module is pruned by this replacement.

Of the original node's proof dependencies:

- `lem-weil-pbc-module-restriction-tensor-comparison` moves to the new naturality node;
  it remains needed transitively.
- `lem-weil-pbc-module-restriction-open-immersion-colimits` is no longer a direct proof
  dependency. The proof infers colimit preservation directly from Mathlib's left-adjoint
  instance for over-site pushforward and colimit preservation by an equivalence. Its
  Mathlib module remains needed for the canonical restriction in the statement.
- `def-pc-tensor-complex-sheaves` remains used to form the tensor bicomplex and its total.

No unit or chapter route is removed. No library module is claimed pruned. The first
worker's unlanded assembly module and node are discarded, not counted as library pruning.

## Where the brief, the DAG or earlier work was wrong

The first worker's assembly theorem had precisely the original conclusion and the
vacuous hypothesis `forall n, Nonempty (P.X n ≅ P.X n)`. Supplying `Iso.refl` does not
prove any part of the original argument. It was a restatement, not a decomposition.
Its claim that the direct-sum assembly was unavailable overlooked the already proved
upstream `HomologicalComplex₂.mapTotalIso` in
`WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap`. The old helper also had a
line-length warning and an incomplete node. All are removed rather than delivered.

[Stacks Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) explicitly states functoriality
of the tensor/pullback comparison. [Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
uses locality in the derived tensor argument; it does not explicitly provide the Lean
assembly theorem. The new node records the expanded argument and its actual source.

## New nodes

`lem-pc-open-restriction-tensor-natural`: the simultaneous module-level tensor comparison
for the precise overFunctor/overEquiv restriction of the item. It has no complexes or
coproducts and realizes only the first part of the old proof plan. Its proof uses the
existing restriction tensor comparison and Mathlib's `Scheme.Modules.overFunctorEquiv`.
The node records LeanSearch (unavailable), leanfinder, loogle, and grep searches; they found the existing ingredients,
but no duplicate assertion. The existing item's node now records the two-stage assembly
actually implemented. No change records are needed.

## Second reading by M2

1. **Existing interfaces: PASS.** Compared the item with the repository version by `diff`.
   Its existing theorem signature, universe, attributes, visibility, options, and genuine
   local monoidal construction are byte-for-byte unchanged. Only proof imports and the
   theorem body differ. The new theorem has its own module and node. No target statement
   or existing definition changes.
2. **Proof and axioms: PASS for the reported decomposition.** Both delivered files compile
   without warnings through `lcompile.py`; the item contains no `sorry`, the lower theorem
   has exactly `by sorry`. No axiom, unsafe, opaque, implemented_by, extern, or hollow
   definition occurs. The scratch axiom probe confirms the allowed axioms plus the
   explicitly reported `sorryAx`. The upstream totalization comparison is fully proved.
3. **Lower statement: PASS, still open.** The new assertion is the functorial module-level
   tensor comparison of Tag 01CD, transported via the canonical over restriction
   identification. It has exactly the compatibility needed for both differentials and
   imposes no flatness, boundedness or quasi-coherence. Empty U, zero input modules,
   identity maps and zero maps satisfy the formula; no exception is omitted. Read the
   existing restriction comparison and searched Mathlib and both local library roots with
   different keywords. Ring restriction-extension tensor theorems are different statements.
   This is strictly a module-level part, not the original complex isomorphism renamed.
4. **Route and pruning: PASS.** The item itself now proves differential compatibility in
   both bicomplex directions from module naturality; the proved upstream mapTotalIso
   handles coproducts and the integer signs. The imports supplying new proofs are plain.
   All old proof dependencies are accounted for above. Read
   `dag/units/sk-thm-picard-f-representable.json`: its realized statement and step lists
   are empty and no entry or unit route is bypassed or changed. This split stays below
   the unit level.
5. **DAG: PASS.** Updated the existing node's proof, proof_deps and proof_origin to the
   implemented route only. Added the full lower node, with its exact Lean statement,
   source, statement dependencies, proof steps and their union of uses, origin, three
   required search kinds (LeanSearch unavailable, loogle/leanfinder, and grep), creation data, blueprint ancestry, chapter/unit and Lean record.

Second reading changed the vacuous assembly restatement into the actual two-direction
bicomplex assembly followed by the proved upstream totalization comparison, moved the
one remaining hole down to module tensor naturality, and repaired the imports, node
records and progress report. This delivery is a decomposition, not a net proof closure.
