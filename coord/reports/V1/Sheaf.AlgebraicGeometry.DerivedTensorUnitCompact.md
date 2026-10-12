## What changed

Reduced `AlgebraicGeometry.exists_compact_derivedTensorUnit` without changing its signature.
Constructed its witness as the degree-zero structure sheaf, proved quasi-coherence in each
cohomological degree, and used the definitional tensor-unit identification. The complete
compactness proof maps Hom groups additively to zeroth derived global sections, proves the
canonical direct-sum square on each summand by naturality, and cancels bijections. Ambient
coproduct compatibility uses the existing full-subcategory closure theorem. All three modules
compile cleanly through lcompile.py.

The two new modules isolate separate calculations: identification of Hom with hypercohomology,
and the coproduct comparison for hypercohomology. Their statements do not assert compactness
or existence of a compact representative. No arbitrary witness was chosen from a mere
existence theorem; the object U is constructed explicitly. The chosen equivalences are proof
witnesses used only inside the theorem.

Read Stacks Tags 09M1, 08DZ and 0B6A online because the listed local perfect.tex is absent.
Searches used LeanSearch (unavailable: Internal Server Error), leanfinder, loogle and grep
through msearch.py, and local searches of both roots.
The existing RHom global-sections theorem involves the internal Hom functor and the ringed-site
hypercohomology definition, whereas our comparison uses ordinary module-valued global sections
and the single structure sheaf. It does not directly give either new signature. Blueprint
searches for structure-sheaf compactness, hypercohomology, and global-section direct sums found
no matching blueprint statement. The unit's realized statement and steps are empty; no unit
route has been bypassed.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.exists_compact_derivedTensorUnit`
(node `lem-pc-derived-tensor-unit-compact`), by decomposition into two strictly smaller
statements. This is a decomposition, not a sorry-free proof of the mathematical theorem.

Added exactly two holes:
- `AlgebraicGeometry.derivedStructureSheaf_hom_hypercohomology`, node
  `lem-pc-derived-structure-sheaf-hom-hypercohomology`.
- `AlgebraicGeometry.derivedGlobalSections_cohomology_coproduct`, node
  `lem-pc-derived-global-sections-cohomology-coproduct`.

Each is a public theorem with proof exactly `by sorry`, a full proof in its docstring, and a
matching node. There are no holes in the item's module or in any definition. The private
`qc_single` helper is completely proved. One upper hole closed and two lower holes added:
net -1 before accounting for shared dependency imports and pruning.

Edge cases: the Hom identification imposes no quasi-coherence or boundedness, and reduces to
ordinary evaluation at 1 for a degree-zero module; zero objects and shifts are covered by the
cycle/boundary computation. The coproduct comparison retains qcqs hypotheses and explicitly
allows empty indexing, zero summands, and unbounded complexes. The Lean direct-sum proof uses
no inhabitedness of the index set.

## No longer needed

Removed proof imports from the item:
- `Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums` (the required ambient coproduct instance
  is obtained from `DerivedQCohDirectSumsAux`).
- `Sheaf.AlgebraicGeometry.DerivedAdjoint`.
- `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums`.
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`.
- `Sheaf.AlgebraicGeometry.DerivedCategory` (already a public statement dependency).

The original node `lem-pc-ringed-spaces-derived-adjoint` and its module `DerivedAdjoint` are
not used by this route: Hom is computed directly on K-injective resolutions. The original
nodes `lem-pc-derived-direct-image-preserves-direct-sums` and
`lem-pc-affine-qcoh-derived-equivalence` remain needed in the new hypercohomology coproduct
node's plan, so they are not claimed as globally pruned. Ambient sums remain transitively
needed through the existing quasi-coherent coproduct modules. No whole-library pruning count
is claimed; the ledger must determine reachability after the second reader lands the delivery.

## Where the brief, the DAG or earlier work was wrong

The original imports do not expose the missing bridge from Hom(O_X,-) to derived global
sections or the scalar-valued hypercohomology coproduct map. They supply the main abstract
ingredients but not those signatures. The derived tensor unit itself is definitionally the
single structure-sheaf complex, so an extra unit-representation existence lemma is unnecessary.

The local source path `literature/stacks-project/perfect.tex` is absent; the online Tag 09M1
was read. Its first paragraph invokes H^0 direct-sum preservation via Tag 08DZ. The original
DAG's structure-morphism/affine reduction is a valid expansion of this fact, not the literal
text of that paragraph. The new node proof origins record the expanded arguments as V1's
specialization of that source.

## New nodes

`lem-pc-derived-structure-sheaf-hom-hypercohomology` in
`DerivedStructureSheafHomHypercohomology.lean` states a natural additive Hom/H^0 identification
for all ambient derived objects on any scheme. Its missing work is the cycle/boundary and
K-injective-resolution comparison, independently of coproducts and compactness.

`lem-pc-derived-global-sections-cohomology-coproduct` in
`DerivedGlobalSectionsCohomologyCoproduct.lean` states the canonical additive coproduct
comparison for zeroth derived global sections on qcqs schemes. Its missing work is the
structure-morphism/affine computation and exact module sums, independently of Hom and the
derived tensor unit. No definitions, existing signatures, target signatures, or change
records were changed.

## Second reading by V1

1. **Declarations and accidental changes.** Compared the delivered module with the repository version. The existing target declaration has the same signature byte for byte; only its proof and proof-only imports changed. The two additional declarations are new split-off nodes, and no existing definition or target statement was altered.

2. **Proof and admissibility.** Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds with no errors. The target proof has no `sorry`, and the only remaining `sorry`s are the two named public split-off theorems, each documented and represented by a DAG node. No forbidden declarations or hollow definitions occur. The target's proof uses only the permitted imported results; its unresolved dependencies appear only below the split nodes.

3. **Split-off statements.** Checked both new statements on empty index sets, zero objects, shifts, and unbounded complexes. The Hom/hypercohomology statement has no extra quasi-coherence or finiteness assumptions, and the coproduct statement retains qcqs hypotheses and allows arbitrary indexing. Each is strictly smaller than the compactness target and is not a restatement of it. Searches of the repository and Mathlib-facing search tools found no existing declaration with either signature.

4. **Pruning and route.** The target proof no longer uses the ambient direct-sums, derived-adjoint, derived-direct-image, affine-equivalence, or derived-category proof imports listed in the report; they were removed and recorded. The quasi-coherent coproduct closure and its ambient coproduct construction remain in the route. The unit is explicitly constructed as the degree-zero structure sheaf, so no arbitrary witness is selected from an existence theorem.

5. **DAG and unit agreement.** The target node and both split nodes record the declarations, statements, proof dependencies, and proof origins used by the Lean files. The unit record is not bypassed: this item realizes the structure-sheaf compactness statement directly, while the two new nodes are intermediate calculations beneath that item.

I changed only this report during second reading; no Lean declarations, node statements, or definitions required repair.
