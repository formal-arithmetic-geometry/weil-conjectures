## What changed

Proved `picardExternalCupCochain_right_exact_ladder` from the new short-exact-complex
comparison theorem `picardExternalCup_right_cech_diagram`. Added proof-only imports
of `PicardExternalCupRightCechDiagram`, `TensorKunnethNat`, and Mathlib's
`HomologySequenceLemmas`; all existing signatures and public imports stay identical.
The private proved helper `normalized_homology_unique` uses cycle lifts, the tensor
Kunneth cycle formula, and tensor/direct-sum extensionality to identify specified
normalized maps on all homology classes. The main proof truncates Mathlib's exact
six-term ladder and proves the outside isomorphisms by conjugation, with a separate
zero-homology argument in degree zero. Updated the item's proof route accordingly.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_right_exact_ladder`
(node `lem-sc-picard-external-cup-right-exact-ladder`), 1 of 1 original holes.
Added: `AlgebraicGeometry.Scheme.Modules.picardExternalCup_right_cech_diagram`
(node `lem-sc-picard-external-cup-right-cech-diagram`), one named theorem whose entire
proof is `by sorry`. This is a decomposition with net zero holes, not a complete
geometric proof. No sorry remains in the item or in its private uniqueness helper.
The remaining statement constructs a comparison of short exact complexes and
identifies its three homology maps; it asserts neither exact homology rows nor
invertibility. The latter steps, including the degree-zero boundary case, are proved.
Both modules compile locally without warnings. Delivery dry-run supplies axiom probes.

## No longer needed

No existing import was removed. No geometric dependency is globally pruned: those
needed for the unfinished Cech construction move to its new node. Direct proof
of the item now needs only the new diagram, tensor Kunneth, normalization and scalar
models, and the generic complex homology long exact sequence. The following former
direct proof dependencies are used only below the new diagram:
- `lem-sc-cech-comparison-map-iso-affine`
- `lem-sc-cech-comparison-map-naturality`
- `lem-sc-cech-comparison-natural`
- `lem-sc-picard-affine-diagonal-intersections`
- `lem-sc-picard-cech-cup-pullback-compat`
- `lem-weil-pbc-derived-functor-long-exact`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-module-pullback-affine-sections`
- `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`
- `pqf-lem-affine-vanishing`

## Where the brief, the DAG or earlier work was wrong

The plan's existing declarations do not themselves give a short exact sequence of
scalar Cech tensor complexes or the three comparison isomorphisms. The Cech
pullback/cup compatibility statements apply to specified refinement and cup maps;
constructing the full coefficient diagram and its model identifications is the
remaining geometric glue. It has been isolated without adding any invertibility
hypothesis. The source page https://stacks.math.columbia.edu/tag/0BED was read.
No statement, definition, or unit route was changed. Edge cases checked: no flatness
of F over O_X is assumed (exactness is over the field on product affine sections),
empty schemes and zero coefficients are allowed, and n=0 uses degree -1 homology.

## New nodes

`lem-sc-picard-external-cup-right-cech-diagram`, in
`Sheaf.AlgebraicGeometry.PicardExternalCupRightCechDiagram`, isolates the finite-affine
Cech short exact comparison and scalar-model identifications. Its source and full
construction proof are recorded in its docstring and node. Mathlib searches found
only Mayer-Vietoris constructions and generic homology tools; LeanSearch was
unavailable. No change record is needed: existing interfaces are unchanged, and the
new import of the diagram is proof-only.

## Second reading by N1

1. Compared the complete existing module with the repository using diff. Its
   theorem signature and docstring, public imports, visibility and namespace are
   byte-for-byte unchanged. Only proof-only imports, a private proved helper and
   the theorem proof were added. The other module and its node are new. No existing
   definition was changed, and no change record is required. Verdict: pass.
2. Compiled both modules in import order with lcompile.py --all: no errors or
   warnings. The sole new sorry is the named theorem
   `AlgebraicGeometry.Scheme.Modules.picardExternalCup_right_cech_diagram`.
   There are no forbidden declarations, definition holes, or arbitrary data
   definitions chosen from existence. The private uniqueness proof lifts homology
   classes through homology projections, uses tensor Kunneth's cycle formula, and
   compares normalized values through the injective scalar model equivalence.
   The main proof uses the actual Mathlib six-term sequence and deletes its first
   object; its outside maps are the second and third coefficient maps at n-1 and n.
   At n=0 the former objects are zero, not natural-degree comparisons. Axiom
   probes are checked in the delivery dry run. Verdict: pass, conditional on the
   explicitly reported remaining geometric hole and existing imported holes.
3. Read the new statement and complete construction docstring against official
   Stacks Tag 0BED, equation the project server and its short-exact diagram, including the
   right-variable argument. Compactness supplies finite covers; affine diagonals
   supply affine intersections; quasi-coherence supplies affine section exactness;
   exact tensoring uses the field, and does not assume O_X-flatness of F. On product
   intersections the external coefficients have tensor sections over k. Natural
   Cech comparisons and normalized tensor-cycle formulas give the displayed
   homology equations. Empty schemes, zero F or coefficient terms, and n=0 are
   allowed; negative homology is zero. This is a strictly smaller construction
   statement: it supplies neither exact homology rows nor conditional outside
   invertibility, and the delivered proof proves both. It is not a renamed ladder.
   Fresh LeanFinder search for an external tensor cup morphism of short exact
   coefficient complexes found group cohomology and Mayer-Vietoris results only;
   Loogle verified mapComposableArrows5. Local rg searches of lean/Sheaf found
   related Cech naturality and the downstream RightShortExact theorem, but no
   duplicate comparison or normalized homology uniqueness theorem. Verdict: pass;
   closing this geometric hole is not a few-minute task.
4. The proof takes generic Mathlib homology exactness and naturality directly.
   TensorKunnethNat is needed explicitly because PicardExternalCupCochain imports
   it privately. All three newly added imports are proof-only. The new module's
   public imports occur in its signature; the existing public imports remain needed
   for the unchanged public interface. No shorter matching theorem was found.
   Every removed old direct proof dependency is listed under No longer needed and
   remains a dependency of the geometric diagram, so no globally pruned module is
   claimed. Inspected dag/units/sk-prop-av-cube.json: this item is below the unit
   realization, whose statement and route remain untouched. Verdict: pass.
5. Compared the old and delivered item nodes: only proof, proof_deps and
   proof_origin changed. The steps record diagram construction, proved normalized
   homology uniqueness and Mathlib sequence truncation, exactly as the Lean does.
   The long-exact dependency is a Mathlib leaf. The new node has its source,
   self-contained statement, full construction proof, searches, creation record,
   blueprint ancestry, chapter/unit, and verbatim Lean statement. Its proof_deps
   equal its step's uses. One original hole closed and one strictly smaller hole
   added: net-zero decomposition. Verdict: pass.

Second reading changed only the unused local abbreviation T in
normalized_homology_unique (removed), and appended this review. No statement,
definition, public import, or mathematical proof route was changed.
