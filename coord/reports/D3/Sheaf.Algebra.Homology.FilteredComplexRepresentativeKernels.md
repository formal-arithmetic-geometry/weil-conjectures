## What changed

Completed the unchanged declaration
`CategoryTheory.DecreasingFiltration.filteredComplex_representative_kernels` in
`Sheaf.Algebra.Homology.FilteredComplexRepresentativeKernels`.
The proof identifies the cokernel kernel with a pullback of the graded boundary
subobject, and identifies the homology kernel with the same pullback using
homology naturality and the mono from homology into opcycles.

Added the proved module `Sheaf.Algebra.Homology.FilteredComplexBoundaryPullback`
and its theorem `CategoryTheory.DecreasingFiltration.filteredComplex_boundary_pullback`.
It performs the substantive quotient-boundary calculation by epimorphic
refinements in an arbitrary abelian category. All its private helpers are proved.
It uses degreewise exactness, incoming-boundary liftings, liftings through images
and sums, and descent of factorization along an epimorphism. There is no arbitrary
choice in a definition and no concrete-category assumption.

The item's only added import is a proof-only import of the new module. The new
module has proof-only imports of the existing source-library subobject APIs.
Updated the item's node proof and proof dependencies to match the Lean argument.

Repair of the landing-tool return: removed the private `exists_image` and
`step_mono` declarations from the new boundary module. The two image calculations
now apply the existing `CategoryTheory.Subobject.exists_obj_top` and
`CategoryTheory.Subobject.exists_obj_comp` theorems directly. The degreewise
monomorphisms are obtained by typeclass inference after expressing each component
as evaluation of the filtration inclusion. This reuses the general library APIs
without stating or proving either duplicate theorem. The flagged declarations in
`FilteredComplexFirstPageCyclesBoundaries` are private, so importing that module
would not make them available. No import of its page-one result is needed.
No existing signatures, definitions, or public imports were changed. No forced
adaptations or change records are needed.

## Proved and sorry left

Closed 1 original hole:
`CategoryTheory.DecreasingFiltration.filteredComplex_representative_kernels`
(node `lem-sp-filtered-complex-representative-kernels`).

Also proved the new theorem
`CategoryTheory.DecreasingFiltration.filteredComplex_boundary_pullback`
(node `lem-sp-filtered-complex-boundary-pullback`); it is not a split-off hole.
Added 0 holes. No `sorry` remains in either delivered module.
This is a proof, not a decomposition with remaining intermediate obligations.

Both modules compile through `lcompile.py --all`. The delivery dry run runs the
axiom probe and checks all declarations against the permitted standard axioms.
The boundary calculation was checked at r=1 (A=P), at a zero differential
(boundaries consist of the next filtration step), and with equal filtration steps
(the relevant quotient is zero). The argument uses only N ≤ P ≤ A and remains
valid in these cases. The representative theorem does not require either supplied
lift to be epic.

## No longer needed

No imports from the repository version of the item were removed, and no existing
DAG proof dependency was pruned: all three definition nodes remain needed.
No additional planned modules are required. Pruned modules: none.

During cleanup of the inherited sandbox attempt, removed the redundant proof-only
`Mathlib.CategoryTheory.Abelian.Exact` import from the new boundary module;
the exactness API is already available through its necessary imports.
This removes no module from the targets' import closure, so it is not counted
as pruning progress.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the private `exists_image` and `step_mono`
statements already present in `FilteredComplexFirstPageCyclesBoundaries`.
The repair removes both declarations and uses existing general APIs directly,
as described above. The previous second-reading section was removed because it
predates this repair; the independent second reader must review the repaired set.

The original inherited attempt had no report or node records. Its new boundary theorem
still contained `sorry`, and its boundary vanishing helper had compiler errors:
association-sensitive rewrites, incorrect subtraction orientation, a nonexistent
`ShortComplex.mk_f` name, and a wrapped subobject-arrow mismatch. These are repaired;
the boundary theorem is now proved as well as the representative theorem.

The original statement and mathematical plan are correct. The proof follows the
cycle/boundary formulas in Stacks Tag 012K, inspected at
https://stacks.math.columbia.edu/tag/012K. The named local homology.tex source is
not present on this machine, so the source was read on the official webpage.
The categorical expansions are explicitly recorded as agent-written.

The inherited unit metadata names `sk-prop-av-pqf-finite`, whose realized statement
and step lists are empty and whose topic is unrelated to this homological lemma.
Its record and the chapter route were not changed or bypassed.
LeanSearch returned an internal-server error; semantic search and source searches
found general APIs, not this filtered-complex comparison.

## New nodes

`lem-sp-filtered-complex-boundary-pullback`, in
`dag/nodes/sec-abelian-varieties/lem-sp-filtered-complex-boundary-pullback.json`,
is a strictly smaller, fully proved boundary pullback calculation. It has no
representative object, cycle lift, comparison morphism, or B≤Z hypothesis, and
is independent of the representative-kernel theorem. Its source, complete proof
steps, three search kinds, and verbatim Lean signature are recorded. It is the
only new node. No change records.

## Second reading by D3

1. **Interface preservation — PASS.** Compared the complete item with the repository
   by `diff -u`: the only changes are the proof-only boundary-module import, three
   proved private helpers, and replacement of the original `sorry` proof. The existing
   theorem signature and docstring are byte-for-byte unchanged. No definition, public
   import, target, or other existing module changes. The boundary module is new.
2. **Proof and trust — PASS.** Read both modules in full and compiled both, in dependency
   order, with `lcompile.py --all`: clean, about four and three seconds respectively.
   Separate scratch copies with `#print axioms` show exactly `propext`, `Classical.choice`
   and `Quot.sound` for both public theorems, without `sorryAx`. Text inspection finds
   no remaining `sorry` or forbidden declaration mechanism. All private helpers have
   complete proofs. No data definition or arbitrary existence witness is introduced.
   In particular, the local existential witnesses are used only inside theorem proofs.
3. **New statement and overlap — PASS.** There are zero split-off holes. The new,
   fully proved `filteredComplex_boundary_pullback` is a proper intermediate result:
   it calculates a subobject of the filtration step, independently of R, z, g, phi,
   and B ≤ Z. Read Stacks Tag 012K's displayed B_r formula (the equation preceding
   Lemma 12.24.2) at https://stacks.math.columbia.edu/tag/012K and matched the degree
   n-1, filtration p-r+1, intersection with F^p, and addition of F^{p+1}. The only
   required inequality is N ≤ P ≤ A. For r=1 the claim becomes the pullback of the
   incoming boundary in P/N; for zero differential both sides pull back to N; for
   N=P both sides are the top subobject of P. The zero complex also satisfies it.
   Checked the forward refinement decomposition x=dy+f, the subtraction proving
   dy lies in P, and the reverse decomposition and cancellation. None uses a
   concrete-category assumption or an epic hypothesis on z or g.
   A fresh LeanFinder query for the epimorphism subobject correspondence and a fresh
   grep query for opcycle pullbacks/quotient boundaries found general APIs but no
   replacement for this filtered-complex theorem. Also searched lean/Sheaf,
   lean/WeilConjectures, and the upstream homology directory. Read the upstream
   `pullback_exists_obj_of_le`: its map is literally a cokernel projection, whereas
   the helper here applies to an arbitrary epi, including the evaluated complex
   projection. The earlier duplicate `exists_image` and `step_mono` helpers are gone;
   the proof now uses `exists_obj_top`, `exists_obj_comp`, and evaluation instances.
4. **Route and pruning — PASS.** The item first reduces its cokernel kernel by the
   mono-cokernel property and pullback functoriality, applies the proved boundary
   calculation, and uses homology naturality and the mono into opcycles to identify
   the second kernel. Read every import: Subquotients supplies the signature's
   filtration data; ShortComplex.HomologicalComplex supplies the signature's cycles,
   homology and opcycles APIs; the two proof-only upstream imports supply the image
   pushforward and abelian subobject/refinement APIs used in the boundary proof.
   No old proof dependency is omitted, so `No longer needed` is complete and pruning
   is none. Read `dag/units/sk-prop-av-pqf-finite.json`: its realized statement and
   step lists are empty and it concerns proper quasi-finite morphisms. This inherited
   unrelated attachment is reported above; no realized node or unit step is bypassed.
5. **DAG agreement — PASS.** Compared the old and delivered item nodes: only proof,
   proof_deps and proof_origin change. The four recorded steps match projection
   naturality, the quotient kernel, boundary pullback, and homology into opcycles.
   The original three definition dependencies remain, with the new boundary node
   added and actually invoked. Read the new node in full: its statement matches
   the Lean signature; its proof describes degreewise exactness, both refinement
   directions, saturation under the graded epi, and the final two subobject
   inclusions. Its source, creation, blueprint ancestry, search records and Lean
   record are present. It introduces no new unproved assumption.

Second-reading changes: appended this independent review and recorded its fresh
searches in the sandbox search log. No Lean or DAG repair was necessary. The delivery
closes the one original hole, adds zero holes, and also proves its new helper theorem.
