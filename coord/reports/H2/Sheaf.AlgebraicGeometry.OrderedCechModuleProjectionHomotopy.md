## What changed

Completed the inherited draft of Sheaf.AlgebraicGeometry.OrderedCechModuleProjectionHomotopy. Its theorem retains its original signature. The proof combines two separately stated sorting boundaries: identity minus stable sorting, and stable sorting minus P. A proved private helper establishes full-coordinate injectivity using the evaluated categorical product, e, and extendXIso. The proof cancels the intermediate stable-sorting terms, treats negative degrees using the zero extension, and adds the canonical null homotopies through Homotopy.equivSubZero. Fixed the draft's application of that equivalence and localized classical decidability in the two new theorem statements.

All three modules compile without warnings through lcompile.py --all. The parent node records the actual reduction. No existing definition, statement, or public import changes.

## Proved and sorry left

Closed the one original hole: AlgebraicGeometry.Scheme.Modules.orderedCech_module_projection_homotopy (lem-pc-ordered-cech-module-projection-homotopy). Its module now contains no sorry. The private fullCoordinate_ext helper is also proved.

Added two holes, each in its own module:

- AlgebraicGeometry.Scheme.Modules.orderedCech_module_firstSorting_boundary (lem-pc-ordered-cech-module-first-sorting-boundary).
- AlgebraicGeometry.Scheme.Modules.orderedCech_module_secondSorting_boundary (lem-pc-ordered-cech-module-second-sorting-boundary).

This is a decomposition: one hole closed, two added, net -1. Each new theorem is strictly a separate boundary computation and module-sheaf assembly step; neither asserts the parent's final homotopy. The first does not assume or mention P. The second asserts only stable sorting minus P. No arbitrary object is chosen for a definition from an unproved existence statement.

## No longer needed

Removed the parent's direct proof imports Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingIdentity and Sheaf.AlgebraicGeometry.AlternatingCechSecondSortingIdentity, replacing them by the two respective module-sheaf sorting boundaries. The additive identities remain imported in those new modules for their planned proofs. Consequently no existing node or module is pruned from the target import closure. The parent's public projection-lift and Homotopy imports remain necessary.

## Where the brief, the DAG or earlier work was wrong

The previous missing OrderedCechModuleProjectionLift.olean is now present in the shared compiled baseline. The inherited draft had an invalid tactic application of Homotopy.equivSubZero.symm, corrected to explicit application using refine. Its global open scoped Classical commands triggered lint warnings; decidability is now scoped to each new statement.

Read Stacks Tag 01FM, equations cohomology-equation-first-homotopy and cohomology-equation-second-homotopy, and both existing additive sorting identities. The parent plan omitted the Lean bridge assembling these additive formulas into locally linear module-sheaf components; those two assembly/boundary steps are the remaining items. The two formulas work on inverse-image opens regardless of covering: only tuple restrictions, their functoriality, hd, and hlinear are used.

Checked empty families (r=0 gives empty positive-length tuple products), degree zero (stable sorting and projection are identity, and the incoming boundary is zero), repeated tuples (stable sorting remains, while strict sorting contributes zero), and degrees above r (strict sorting is zero, without forcing full cochains to vanish). Joint injectivity also covers the empty product. Negative degrees are closed by isZero_extend_X, rather than an added hypothesis.

The inherited searches recorded LeanSearch unavailable, LeanFinder normalization results, and source grep with no module-sheaf assembly bridge. Current source grep confirms no existing first/second module-sheaf sorting boundary. The unit record's realized lists are empty; this reduction retains its route and both sorting computations. No adaptation or change record is needed.

## New nodes

lem-pc-ordered-cech-module-first-sorting-boundary: Sheaf.AlgebraicGeometry.OrderedCechModuleFirstSortingBoundary assembles the first junction homotopy into locally linear maps and states its full-coordinate boundary, identity minus stable sorting. It is independent of P and hP.

lem-pc-ordered-cech-module-second-sorting-boundary: Sheaf.AlgebraicGeometry.OrderedCechModuleSecondSortingBoundary assembles the repeated-tuple homotopy into locally linear maps and states its full-coordinate boundary, stable sorting minus P. It is independent of the first boundary. Both nodes carry the source, the complete construction and boundary argument in words, and their verbatim Lean signatures.


## Second reading by H2

1. **Statements and interfaces.** Compared the delivered projection-homotopy module with the repository version. The target theorem signature is byte-for-byte unchanged; the two added boundary theorem signatures match their DAG `lean.statement` fields. No existing definition or target statement changed. Verdict: pass.

2. **Proof and trust basis.** Compiled all three modules with `lcompile.py --all`; the files contain no forbidden declarations and no `sorry` in a definition. The private coordinate-extensionality helper has only `propext`, `Classical.choice`, and `Quot.sound`. The target has no direct hole; its axiom list includes `sorryAx` through the two split boundary theorems. Each boundary theorem has its reported named hole and node. Verdict: pass.

3. **Truth and strength of split statements.** Read the two boundary formulas against Stacks Tag 01FM, equations the project server and the project server, and the existing additive identities. The first states identity minus stable sorting; the second states stable sorting minus the supplied projection, with exactly the differential and local-linearity hypotheses used by the assembly. Edge cases (empty index family, degree zero, repeated tuples, and degrees above the number of chosen opens) are covered by the displayed filters and zero extension. Verdict: pass.

4. **Pruning and route.** The parent imports only the projection-lift interface, homotopy API, and the two new boundary modules. The boundary modules keep the additive sorting identities as proof-only imports. The unit route remains the two sorting identities followed by module-sheaf assembly; its `realized` record is unchanged. Verdict: pass.

5. **DAG agreement.** Checked each node's declaration, proof text, `proof_deps`, source, and module path against the Lean files. Corrected the parent node's explicit projection-lift dependency and clarified the empty-family proof wording. Search found no existing module-sheaf bridge theorem duplicating either split statement. Verdict: pass.

Changed files: the parent proof and imports as delivered, the two split boundary modules and nodes, the parent node dependency metadata, and this report. No statement or definition was changed.
