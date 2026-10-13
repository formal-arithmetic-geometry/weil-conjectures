## What changed

Replaced the sole sorry in `Sheaf.Algebra.Homology.AffinePerfectColimitDescent` by a complete
Lean assembly proof. The theorem signature, universes, visibility and docstring are unchanged.
The proof obtains bounded graded term models, proves their finite presentation from finite
projectivity, descends differentials on those fixed models, constructs the complex from its
actual terms and maps, and builds the isomorphism with `HomologicalComplex.Hom.isoOfComponents`.

Added `Sheaf.Algebra.Homology.FiniteProjectiveGradedColimitDescent` and
`Sheaf.Algebra.Homology.AffineDifferentialColimitDescent` for the unfinished term-descent and
map/relation-descent steps. The first has no complex or differential data. The second fixes
its term models in its hypotheses and returns only maps, relations and compatible term
isomorphisms; it does not assert bounded finite projectivity of a complex. The original
module constructs that complex and proves its term properties in Lean.

Replaced the original module's direct proof import of `Sheaf.Algebra.FinitePresentationColimit`
with the two new modules and added the proof-only import `Mathlib.RingTheory.TensorProduct.Finite`.
Both lower modules retain the finite-presentation colimit import for their planned proofs.
Updated the item's node to record the actual Lean combination and its dependencies.

## Proved and sorry left

Closed the original hole in
`CochainComplex.exists_finite_projective_model_of_directed_colimit`
(node `lem-pc-affine-perfect-colimit-descent`). No sorry remains in the original module.

Added exactly two holes, each the whole proof of a public theorem in its own module:

- `ModuleCat.exists_finite_projective_graded_model_of_directed_colimit`
  (node `lem-pc-finite-projective-graded-colimit-descent`).
- `CochainComplex.exists_differentials_on_graded_model_of_directed_colimit`
  (node `lem-pc-affine-differential-colimit-descent`).

This is a decomposition: one original hole closed, two lower holes added (net -1).
It does not yet establish an axiom-free proof of affine perfect complex descent. The complete
Lean combination constructs the complex, proves its term models finitely presented,
preserves the bounds and finite projectivity, and assembles its scalar-extension isomorphism.
No definitions or arbitrary data chosen from unproved existence theorems were added.

All three modules compile through lcompile.py; the assembly proof has no warnings.
The new statements were checked mathematically on empty support (including b<a),
single-degree support, zero modules, zero colimit ring and non-antisymmetric preorders.
Empty support uses zero models at any nonempty index; single-degree support has zero adjacent
differentials. No nontriviality of any ring is assumed. When the colimit ring is zero, zero
term models are permitted. Fixed nonzero stage models whose base changes vanish cause no
problem for differential descent: their finite list of composite equations is imposed only
after enlarging the stage. Antisymmetrization gives an equivalent thin indexing category;
comparison in the quotient lifts a later representative j with i≤j.

## No longer needed

No planned mathematical dependency or unit route is discarded. The original module's direct
`Sheaf.Algebra.FinitePresentationColimit` import is removed from its assembly proof; that
module and node `lem-pc-fp-module-map-descent-affine` remain prerequisites of the two lower
items and are retained there. No entire existing module is claimed to be pruned.
All original public imports remain, so no importing module's interface changes.

## Where the brief, the DAG or earlier work was wrong

`ModuleCat.finitePresentation_descent_directedColimit` requires `PartialOrder`, whereas this
item allows `Preorder`. Its application needs a quotient-by-mutual-comparison indexing
equivalence and transport of the colimit ring and module data. Both lower proof plans make
this explicit, while the original theorem signature stays unchanged. The final assembly
also needs finite-presentation inference and explicit ring-map algebra structures for the
Mathlib tensor-product finiteness and projectivity instances.

The referenced Stacks TeX and blueprint section text are absent in this checkout. Read the
supplied node and unit records and verified the source at
https://stacks.math.columbia.edu/tag/0BC7, proof of (1): finite-presentation colimit descent
and finite projectives as finite free summands. The unit `sk-thm-picard-semicon` has empty
realized lists; none of its bindings or route was altered.

LeanSearch returned Internal Server Error, recorded as unavailable, never as no match.
LeanFinder, Loogle, Mathlib grep, searches of both library roots and blueprint searches found
no existing theorem matching the two new steps. The sheaf complex descent statement under
Noetherian hypotheses does not apply to this unrestricted ring-colimit statement.

## New nodes

`lem-pc-finite-projective-graded-colimit-descent`, in
`dag/nodes/sec-picard-framework/lem-pc-finite-projective-graded-colimit-descent.json`, records
the term-descent part of Tag 0BC7. It supplies no differential data, preserves the specified
support bounds, and reduces to finite-presentation module/map/equality descent plus
finite-projective splitting. Its module is
`lean/Sheaf/Algebra/Homology/FiniteProjectiveGradedColimitDescent.lean`.

`lem-pc-affine-differential-colimit-descent`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-differential-colimit-descent.json`, records the
map/relation part of Tag 0BC7 on prescribed term models. It returns differentials, their
shape and square-zero equations, and compatibility with the original differentials. Its
module is `lean/Sheaf/Algebra/Homology/AffineDifferentialColimitDescent.lean`.

Both inherit the item's chapter, unit and blueprint ancestor and carry complete natural-language
proofs, source references, actual search records and Lean signatures. No change record is
required: no existing signature, definition or public import is changed.

## Second reading by H3

1. **Interface: PASS.** Compared every delivered module with the read-only repository.
   The two lower modules are new. The original theorem's signature is byte-identical,
   and its universes, visibility, docstring and public imports are unchanged. The only
   original Lean changes are proof-only imports and its proof. No definition changed,
   so no statement change record or forced adaptation is required.
2. **Kernel and holes: PASS as a decomposition.** Independently compiled all three modules
   with `lcompile.py --all`: no errors or warnings. A scratch copy with explicit
   `#print axioms` commands reports exactly `propext`, `Classical.choice`, `Quot.sound`
   and `sorryAx` for all three declarations. The two new named public theorem bodies are
   the only remaining sorries. There are no definitions containing postponed data, no
   forbidden declarations, and no arbitrary witness selected in a public definition.
   The existential witnesses are eliminated locally inside the original theorem's proof.
   This closes one upper hole and adds two lower holes; it is not an axiom-free proof.
3. **New statements: PASS.** Read both signatures and their complete docstring arguments
   against the finite-presentation object/map/equality theorem and Stacks Tag 0BC7 (1).
   The graded result has no maps, and the differential result has fixed bounded finitely
   presented models, with no projectivity conclusion. They are strictly separate parts
   of the original argument, not restatements. Empty and reversed intervals use zero
   models; one-degree support has zero differentials; zero rings require no nontriviality.
   Outside the interval a zero source or target forces the map to vanish. For a preorder,
   mutual-comparison quotienting is an equivalence of thin categories; transporting the
   diagram and colimit and choosing a representative of a later class preserves i <= j.
   The canonical iterated tensor isomorphisms ensure simultaneous map compatibility,
   and finitely many square-zero equations can be imposed at a common later stage.
   Repeated independent searches with different terms: LeanFinder "finite projective
   modules over filtered union of commutative rings descend to an index" returned
   projectivity and finite-presentation tools, not descent; Loogle
   "Module.Projective, TensorProduct" returned tensor projectivity and duality tools;
   Mathlib grep for descent with projective/differential returned only faithfully flat
   etale descent, whose source was checked and does not apply. Searches in both library
   roots found no matching existing graded or differential descent theorem. Neither
   remaining step can be closed by these tools in a few minutes.
4. **Route and pruning: PASS.** Reviewed the assembly from the top downward: finite
   presentation follows from finite projectivity; scalar extension preserves zero,
   finiteness and projectivity; the returned compatibility equations feed directly into
   `HomologicalComplex.Hom.isoOfComponents`. Proof-only imports remain private to the
   proof. The finite-presentation import in the new holed modules is retained for their
   stated proof plans. Of the original proof dependencies,
   `lem-pc-fp-module-map-descent-affine` is no longer a direct assembly dependency but
   remains used through both lower nodes; `def-weil-pbc-projective-module` remains used.
   Thus no old prerequisite or entire module is pruned. Read the unit record: its
   `realized.statement` and sole `realized.steps` entry are empty and unchanged; the
   established unit route is retained.
5. **DAG: PASS.** Compared the existing node: only stage-3-owned fields changed. Checked
   all three node statements against the Lean signatures (whitespace normalization),
   and checked that each `proof_deps` equals the union of its proof steps' `uses`.
   The new nodes have sources, proof origins, search records, creation metadata,
   blueprint ancestry, chapter/unit and matching Lean records. Their proof plans and
   the original node's assembly describe the actual reduction.

Second reading changed only this report: added the independent checks, axiom results,
search results, and clarified the indirect retention of the old proof dependency.
No repair to the Lean proof or nodes was needed.
