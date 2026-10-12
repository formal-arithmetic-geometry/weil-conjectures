## What changed

Proved the remaining theorem in `Sheaf.AlgebraicGeometry.FiniteEquationsOfClosedAffine`,
`AlgebraicGeometry.Scheme.Hom.exists_finitely_generated_zeroLocus_ideal_degree_sublevel_inter_affine`,
without changing its signature or the signature of the already proved finite-equations theorem.
Added one proof-only import of
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeDegreeQuotientApproximation`.

The proof constructs the ideal as the canonical vanishing ideal of the closed locus pulled
back to the affine spectrum. The quotient-spectrum range formula and the universal degree
criterion make that quotient base change finite locally free of degree r. Quotient-ideal
descent gives a finitely generated subideal. Ideal inclusion proves one direction of the
zero-locus equality; the universal degree criterion proves the other.

The new module proves
`AlgebraicGeometry.Scheme.Hom.exists_fg_subideal_isFiniteLocallyFreeOfDegree` from the existing
`AlgebraicGeometry.descend_finite_locally_free`. It explicitly constructs the directed diagram
of quotient rings and proves that its colimit is A/I. It also proves fixed-degree pullback
stability and the isomorphism comparing over-category pullback with the usual composite base
change. All new definitions contain real data and complete proofs. No witness of an unproved
mere-existence theorem is used to define data.

The route follows Stacks Tag 07RZ, second proof paragraph, and its reference Tag 06AC.
The local literature checkout lacks the TeX files, so these already-listed obtained sources
were read at https://stacks.math.columbia.edu/tag/07RZ and
https://stacks.math.columbia.edu/tag/06AC. The unit record `sk-thm-p1` was read; this item realizes
none of its own statement or numbered steps, and the unit route is unchanged.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Scheme.Hom.exists_finitely_generated_zeroLocus_ideal_degree_sublevel_inter_affine`
(node `lem-weil-pbc-finite-equations-of-isClosed-inter-affine`).

Added zero holes. The new theorem
`AlgebraicGeometry.Scheme.Hom.exists_fg_subideal_isFiniteLocallyFreeOfDegree`
(node `lem-weil-pbc-finite-locally-free-degree-quotient-approximation`) is fully proved.
The pre-existing theorem
`AlgebraicGeometry.Scheme.Hom.exists_finite_equations_of_finitely_generated_zeroLocus`
remains proved and unchanged.

No `sorry` remains in either delivered module. This is a proof from the existing library's
fixed-degree descent theorem, not a decomposition into new unproved statements. Existing
transitive holes below that library theorem are not claimed closed here.

Both modules compile through the prescribed lcompile.py wrapper (17.0 seconds and 8.0 seconds
in the last explicit set compile). The prescribed `deliver3.py --no-push` dry run printed OK:
the delivery compiles and passes preflight except for the second reading, which the next
worker writes. Nothing was pushed. Edge cases are included by
the constructions: I = zero, I = top, the zero ring, empty schemes, an empty affine open, and
r = zero. The index has bottom zero even when I is zero, and its quotient cocone proof never
requires a prime or a nonempty spectrum. The proof uses no cancellation by r.

## No longer needed

None. Both original public imports remain necessary for the original signatures. No original
proof-dependency module or node is pruned. The new module needs only its public FiberDegree
import and the proof-only DescendFiniteLocallyFree import.

## Where the brief, the DAG or earlier work was wrong

The item's original DAG proof compressed ideal representation, quotient-limit construction,
descent, and the comparison of zero loci into one non-elementary step with no named
dependencies. The updated node now records those actual steps and the proved quotient-descent
specialization, which cites the existing general fixed-degree descent node.

There is no disputed statement, interface change, or forced adaptation. The generalized
quotient-descent theorem needs quasi-compactness rather than quasi-finiteness; the original
hypothesis supplies it as `hf.2.1`. Its proof also does not require flatness as an initial
hypothesis: fixed-degree finite local freeness at the limit supplies the property that the
existing descent theorem descends.

## New nodes

`lem-weil-pbc-finite-locally-free-degree-quotient-approximation`, in
`dag/nodes/sec-proper-base-change/`, records the proved quotient-ideal specialization of
fixed-degree finite locally free descent. Its module is
`lean/Sheaf/AlgebraicGeometry/FiniteLocallyFreeDegreeQuotientApproximation.lean`.
It has a complete proof, searches of all three required kinds, and no `sorry`. LeanSearch was
attempted and returned an Internal Server Error; semantic search, type-pattern search, and
source grep found the existing general descent theorem but no one-line quotient specialization.
The node and the parent node retain chapter `sec-proper-base-change` and unit `sk-thm-p1`.
No change record is needed, since every existing signature and visibility is unchanged.

## Second reading by F2

1. **Unchanged interfaces: PASS.** Read the repository diff and compared the raw
   signature slices of both existing theorems: byte-identical. The already proved
   finite-equations theorem's body is unchanged. The only added import in the item
   is proof-only. The new quotient-approximation module has no repository predecessor.
   No definition, existing visibility, target, or statement has changed; no change
   record is required. Read the landed earlier public-import change record as well.
2. **Proof and constructions: PASS.** Independently compiled both modules in import
   order through lcompile.py (4.7 and 2.7 seconds in the first review compile), with
   no errors or warnings. Source scanning finds no sorry or forbidden declaration.
   Scratch-copy #print axioms checks give propext, Classical.choice, Quot.sound for
   exists_finite_equations_of_finitely_generated_zeroLocus; the newly closed theorem
   and exists_fg_subideal_isFiniteLocallyFreeOfDegree additionally use sorryAx.
   A separate check of the existing descend_finite_locally_free confirms its inherited
   sorryAx dependency. These transitive holes remain open and are not claimed proved.
   The finitely generated ideal index, quotient maps, diagram, cocone and colimit
   factorization are explicit constructions with complete proofs; no arbitrary data
   is selected from an unproved existence theorem.
3. **New statements and edge cases: PASS.** There are zero split-off unproved
   statements. Read the new proved quotient-descent theorem and its entire argument:
   bottom and sums give a nonempty directed index; principal ideals kill each relation;
   the bottom-stage map gives the unique quotient factorization. Separatedness and
   quasi-compactness give the qcqs source required by general descent. Degree stability
   and pullback comparison preserve exactly the claimed degree. For I = zero the
   index includes zero; for I = top a zero-ring quotient is allowed; zero rings,
   empty schemes/affine opens and r = zero introduce no nonemptiness or positive-rank
   requirement. Independent LeanFinder, Loogle and source searches with quotient-rank
   and colimit terminology found no existing quotient-ideal degree specialization.
   The similarly named quotient_fibre_limit_transfer concerns inverse-image ideals
   in a different diagram; fgSubDiagram concerns ideal sheaves. Neither replaces this
   specialization. There is no mere renamed restatement of the item.
4. **Route and pruning: PASS.** Read the proof from the top down, the existing general
   descent theorem, Stacks Tags 07RZ and 06AC, and dag/units/sk-thm-p1.json.
   The canonical vanishing ideal, quotient descent and range criterion are the direct
   source route. Every import is needed: original public imports supply signature
   notions; the added proof-only imports supply the descent results. The original
   proof_deps list is empty, so no old dependency is omitted from No longer needed.
   This item realizes none of the unit's statement or numbered steps; its route is
   retained, and no module is pruned.
5. **DAG agreement: PASS.** Compared the original and delivered parent nodes and read
   the new node. The parent records the vanishing-ideal construction, fixed-degree
   quotient descent and both zero-locus inclusions. Its only proof dependency is the
   new quotient-approximation node. That node records the quotient colimit, pullback
   comparison and the existing general descent dependency; proof_deps equals the
   union of step uses. Its source, proof_origin, searches, created/blueprint, chapter,
   unit and verbatim Lean statement agree with the module and the stage-3 contract.

Second reading changed only this report by adding independent verification and
explicit axiom findings. No Lean proof or node repair was necessary. Closed one
existing hole, added zero holes, split off zero holes; existing transitive holes
remain. All scratch probe copies were removed before delivery.
