## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.Modules.externalGlobalSectionsTensor_bijective_of_isAffine_right`
with a complete Lean reduction along the node's finite affine cover argument.
The proof takes the finite subcover of `X.affineCover`, proves that its opens are affine,
uses `isAffineHom_diagonal_iff` for affine pairwise overlaps, applies the affine-by-affine
comparison on each chart and overlap, and applies finite-cover descent in the first factor.
All existing signatures, public imports, and docstrings are unchanged.

Added proof-only imports of `ExternalGlobalSectionsTensorAffine`,
`ExternalGlobalSectionsTensorFiniteCoverLeft`, and `Mathlib.AlgebraicGeometry.Modules.Tilde`.
The last supplies quasi-coherence of the restrictions of F. The first two modules contain
one strictly smaller residual statement each. Their docstrings give full proofs in words,
and their new nodes record the source and dependencies. Updated the item's node proof,
proof_deps and proof_origin to the Lean route. No definitions or other modules were changed.

All three delivered modules compile together, without warnings, through `lcompile.py`.
The residual statements were checked on empty factors, zero coefficients, empty overlaps,
and the empty indexing type. Descent with an empty cover is valid because hcover then
forces X to be empty; its equalizer and section modules are zero. The affine comparison
uses balanced tensor identities that remain valid for zero rings and zero modules.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.externalGlobalSectionsTensor_bijective_of_isAffine_right`
(node `lem-sc-external-global-sections-tensor-affine-right`). Its proof now has no local holes.

Added exactly two holes, each the whole proof `:= by sorry` of a named public theorem:

- `AlgebraicGeometry.Scheme.Modules.externalGlobalSectionsTensor_bijective_of_isAffine`,
  node `lem-sc-external-global-sections-tensor-affine`, in
  `Sheaf.AlgebraicGeometry.ExternalGlobalSectionsTensorAffine`.
  This is the affine chart calculation, with both factors affine; it has no descent step.
- `AlgebraicGeometry.Scheme.Modules.externalGlobalSectionsTensor_bijective_of_finite_cover_left`,
  node `lem-sc-external-global-sections-tensor-finite-cover-left`, in
  `Sheaf.AlgebraicGeometry.ExternalGlobalSectionsTensorFiniteCoverLeft`.
  This is generic descent from supplied chart and overlap bijectivity; it has no affine
  chart calculation and assumes neither quasi-coherence nor affine diagonals.

This is a decomposition, not an axiom-free proof of the original comparison: one upper
hole is closed and two lower holes are added (delivery-local net -1). No other holes are
left in the item's module or added anywhere. Every remaining hole is in its own module.

## No longer needed

None of the original public imports were removed, and no original mathematical dependency
was globally pruned. Former direct proof dependencies no longer named by the item node are
`def-sc-scalar-global-sections-comparison`, `def-weil-field`,
`def-weil-sheaf-of-modules-category`, `lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-module-pullback-affine-sections`, and
`lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`. The three definition nodes
remain in the statements/import closure and the residual proof plans; the three affine
comparison nodes remain in the affine residual proof plan. The affine spectrum, affine pullback-section and affine tensor-section
nodes remain needed by the new affine chart node, rather than directly by the item's node.
The affine-diagonal intersection node remains used directly by the item's proof.

The symmetric second-factor theorem
`Sheaf.AlgebraicGeometry.ExternalGlobalSectionsTensorFiniteCover` is not imported by this
proof. The direct first-factor descent formulation avoids a separate factor-exchange
comparison. That second-factor module remains used elsewhere in the library, so no global
pruning of it is claimed. No higher cohomology, acyclicity or infinite-product comparison
is introduced by this route.

## Where the brief, the DAG or earlier work was wrong

The item's original imports do not include the two substantial intermediate steps of its
DAG plan. The named affine pullback and tensor-section comparisons do not themselves state
the assembled affine external comparison; their ring changes and pure-tensor compatibility
are the residual affine theorem. The finite-cover equalizer step likewise has no existing
first-factor descent statement, so it is now stated explicitly as a second residual.

The library has a symmetric second-factor descent statement. Reusing it would require
factor exchange of both coefficient sections and the canonical external map. I tested
that route, including constructing the linear equivalence by the pullback unit, monoidal
pullback comparison, projection composition comparisons and braiding. Completing its
pure-tensor transport reached the compiler's 60-second limit; the attempt is not delivered.
The recently landed second-factor descent module was also absent from the local compiled
snapshot during these attempts. The final direct-cover route compiles using available
interfaces and does not duplicate that declaration. No script was changed or bypassed.

The source Tag 0BED was read at https://stacks.math.columbia.edu/tag/0BED. Its affine case
and finite-cover calculation support the two residuals; the degree-zero kernel argument
is spelled out in their docstrings and nodes. LeanSearch was attempted and returned an
Internal Server Error; this is recorded as unavailable. LeanFinder, Loogle and Mathlib
source searches found only general tensor, fibre-product and sheaf-descent tools.

## New nodes

`lem-sc-external-global-sections-tensor-affine` carries the affine-by-affine comparison,
with the same canonical map as the original item and stronger local affineness hypotheses.
Its two proof steps assemble the existing affine spectrum/pullback/tensor comparisons and
then the explicit balanced algebraic tensor isomorphism. It inherits the item's chapter,
unit and blueprint ancestor, and has a verbatim Lean signature and three kinds of search.

`lem-sc-external-global-sections-tensor-finite-cover-left` carries descent in the first
factor, given chart and overlap bijectivity. Its proof identifies restrictions of external
coefficients via the cartesian open-immersion square, then tensors the finite sheaf kernel
diagram over the field and restricts the inverse chart map to its kernel. It inherits the
item's chapter, unit and blueprint ancestor and has a verbatim Lean signature and recorded
searches. No unit statement or realized proof step is bypassed, and no change record is
needed because all existing interfaces are unchanged.

## Second reading by M1

1. **Interface unchanged.** I compared the delivered item module against the repository version. The existing theorem signature is byte-for-byte unchanged; only its proof and proof-only imports were added. The two residual theorem signatures are new, and their node records match the Lean declarations.

2. **Compilation and proof audit.** All three sandbox modules compile with `lcompile.py --all` without errors or warnings. A scratch-copy `#print axioms` check of all three public theorems showed only `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx` from the open residuals. The item theorem has no `sorry`; the only remaining `sorry`s are the two named residual theorems, each with a source docstring and matching DAG node. No forbidden declarations or hollow definitions occur.

3. **Statement review.** The affine residual is exactly the affine-by-affine comparison required by the chart step. The finite-cover residual is exactly first-factor descent from chart and overlap bijectivity, with no extra hypotheses. Both statements were checked on empty index types, empty overlaps, zero modules, and zero schemes; no contradiction or weakening was found. Searches and repository inspection found no duplicate declaration.

4. **Route and pruning.** The item's proof follows the unit route: finite affine subcover, affine chart/overlap comparison, then first-factor descent. The affine-diagonal criterion is used for overlaps. The proof-only imports are all used; no existing import can be removed, and the symmetric second-factor route is unnecessary.

5. **DAG agreement.** The item node's proof steps, dependencies, and origin agree with the Lean proof. The two new nodes contain the verbatim declarations, source, proof plans, searches, chapter/unit, and blueprint ancestry required by stage 3. The unit record currently has empty `realized.statement` and `realized.steps[0]` lists: this is a pre-existing upstream omission, not fixed or bypassed by this below-unit decomposition.

I changed the report to enumerate former direct dependencies and note the upstream empty unit realization record after the first delivery check; no Lean code, node, or interface was changed during second reading.

Independent searches in this reading used LeanFinder for exterior-product sections on
affine schemes, Loogle for `ker_rTensor`, and grep for bijective tensor/equalizer maps.
They found general affine-space and flat equalizer tools, not either residual statement.
I also read [Tag 0BED](https://stacks.math.columbia.edu/tag/0BED): its affine case and
finite-cover degree-zero calculation support the reductions. The stronger descent
statement for arbitrary module sheaves follows from the stated sheaf kernel argument.
Neither residual can be closed by a short application of a found theorem.
