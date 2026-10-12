## What changed

Preserved the signature of `AlgebraicGeometry.rightAdjointTensorLocus_triangles` byte for byte.
Replaced the first worker's conjunction-only proof with a reduction through the existing
`rightAdjointTensorComparison_natural`. The pinned inverse equation makes the projection
isomorphism unique; the proof identifies the existential locus with invertibility of the
underlying natural-comparison component. Shift conjugation and Mathlib's
`Pretriangulated.isIso₃_of_isIso₁₂` now prove the two closure assertions.

Added `Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonDiagrams`, with a single named
obligation for compatible shift squares and morphisms between distinguished image triangles.
This statement concerns diagrams without any component-invertibility assumptions or conclusion.
Removed the undelivered `RightAdjointTensorLocusTrianglesAux` and its two clause-restating nodes.
Updated the existing item's proof, proof_deps and proof_origin to match the reduction.
The new import is proof-only. All original public imports occur in the existing signature.

## Proved and sorry left

Closed the original body hole in `AlgebraicGeometry.rightAdjointTensorLocus_triangles`.
Added one hole: `AlgebraicGeometry.rightAdjointTensorComparison_diagrams`, node
`lem-sc-right-adjoint-tensor-comparison-diagrams`. It has a source and a detailed
natural-language construction in its docstring. The pre-existing imported theorem
`AlgebraicGeometry.rightAdjointTensorComparison_natural` remains open and is used explicitly.

This is a decomposition: one original hole closed and one new hole added; net zero.
The original declaration still depends on sorryAx. Neither the target nor the library is
claimed axiom-free. The first worker's two auxiliary holes and nodes are removed rather than
counted as closed baseline holes.

## No longer needed

Old proof_deps `def-pc-derived-direct-image`, `def-pc-derived-pullback` and
`def-pc-scheme-derived-tensor-structure` are no longer direct proof dependencies of the
item: they belong to the comparison-diagram obligation. Their modules remain public imports
because the unchanged signature uses their definitions, and remain in the targets' closure.
No baseline module or import was pruned.

The first worker's undelivered `RightAdjointTensorLocusTrianglesAux`,
`lem-sc-right-adjoint-tensor-locus-shift-closure` and
`lem-sc-right-adjoint-tensor-locus-triangle-closure` are removed from this delivery.

## Where the brief, the DAG or earlier work was wrong

The first worker supplied only the two conjuncts of the original statement under new names,
then paired them. Its docstrings omitted the natural-language proofs; its new nodes lacked
stmt_deps, blueprint, searches and verbatim Lean signatures. Its report called this a proof
without accounting for the two added holes, and the existing node was not updated.

The repaired reduction proves pinned uniqueness and the invertibility argument, and isolates
the geometric diagram construction. The actual Stacks source was read online at
https://stacks.math.columbia.edu/tag/0A9U and
https://stacks.math.columbia.edu/tag/0A9T, since literature/stacks-project/duality.tex is absent
on this machine. Tag 0A9U assumes perfect proper for the entire localizing argument; the
shift and triangle portion used here requires exactness, without the later coproduct condition.
The new diagram statement adds no perfectness or coproduct hypothesis.

## New nodes

`lem-sc-right-adjoint-tensor-comparison-diagrams`, in its own new module.
No new definitions and no interface adaptations.

## Second reading by T3

1. Compared the delivered item with the repository using diff. All existing hypotheses,
   universes, instances, the pinned inverse equation and both conclusions remain byte for byte
   identical. No definition, public visibility or target changed. Only a proof import and the
   proof body changed. The auxiliary module is entirely new.
2. Compiled both repaired files with lcompile.py in import order; no errors or warnings.
   Inspected every declaration: the new diagram theorem is the only local sorry; no axioms,
   unsafe declarations, opaque declarations, extern or implemented_by, and no definitions
   using a sorry or selecting arbitrary existence witnesses. The natural comparison and
   its pf witnesses are eliminated inside a proposition proof, with pf uniquely pinned.
   Axiom probes are recorded below after the delivery checks.
3. Read the diagram statement and its complete construction against Stacks 0A9U and the
   comparison formula. Checked n=0, negative shifts, the zero object, the zero triangle,
   and triangles whose first two objects are zero: the statement still asks for diagrams,
   with no forbidden assumption of component invertibility. Isomorphisms in all vertex
   positions have the stated directions. Searches used different vocabulary (exact natural
   transformations, shift squares, triangle morphisms): LeanFinder found generic mapTriangle
   and exact-functor lemmas, grep found CommShift and right-adjoint triangulated machinery;
   LeanSearch was unavailable (HTTP 500), recorded as unavailable. Searched Lean sources and
   DAG records for existing geometric comparison-diagram statements; none supplies this
   statement. The auxiliary is strictly a part of the proof, not a locus-closure restatement.
4. The proof uses the existing natural-comparison node and Mathlib directly; no duplicate
   definitions or generic triangle lemma were introduced. All imports support the unchanged
   signatures or proof. The No longer needed section accounts for every removed direct
   proof_dep. The unit sk-thm-picard-duality realized fields were read and remain unchanged
   (currently empty); the reduction retains the same tensor-comparison route.
5. The existing node now names natural comparison, pinned uniqueness and diagram
   two-out-of-three exactly as the Lean proof does. The new node has the full statement,
   verbatim signature, source, complete proof steps, dependency union, proof_origin,
   three actual search kinds, created/blueprint/lean fields, chapter and unit.

Changed: replaced the clause-restating split by the real reduction, reduced new holes from
two to one, repaired documentation and node records, and removed the first worker's long-line
warning together with its obsolete auxiliary file.

Validation: the first dry run printed OK and classified the delivery CODEX because it
adds a node and a public auxiliary theorem. Explicit #print axioms in scratch copies
compiled through lcompile.py reports exactly propext, Classical.choice, Quot.sound,
and sorryAx for both rightAdjointTensorLocus_triangles and
rightAdjointTensorComparison_diagrams. The delivery tool's full declaration probes
also passed. No additional axioms were detected.
