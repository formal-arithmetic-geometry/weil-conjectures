## What changed

Wrote a reduction of `AlgebraicGeometry.Scheme.Modules.externalGlobalSectionsTensor_bijective`
without changing its signature, visibility, or docstring. The proof constructs the finite
subcover of Y's canonical affine cover, proves its pairwise overlaps affine using
`isAffineHom_diagonal_iff`, and applies the affine-right comparison on each chart and
overlap before finite-cover descent. Added two proof-only imports and the Mathlib
quasi-compact-cover and Modules.Tilde imports. Added two new statement modules, each with its named residual
theorem, source, complete proof in words, and matching node. Updated the original node's
proof, proof dependencies, and proof origin.

Read Stacks Tag 0BED at https://stacks.math.columbia.edu/tag/0BED because the local
literature tree contains only the citation lists, not varieties.tex. The argument stays
inside the original node's ordinary-section two-equalizer route. The unit record
`sk-prop-av-cube` has no realized node for this item; its route is unchanged.

Verification on this retry (2026-10-13): `lcompile.py --all` compiled all three
modules with exit code 0 and no warnings (3.3 s, 2.6 s, and 4.1 s respectively).
The repository source now contains ScalarGlobalSectionsComparison and the item, so
the previous source-snapshot blocker is resolved. Repeated LeanSearch through
msearch.py; the service returned Internal Server Error. Recorded this unavailability
in both new nodes without inventing a mathematical verdict; the previous LeanFinder,
Loogle, and grep searches remain available.

## Proved and sorry left

The original theorem's proof body contains no sorry and compiles successfully.
This is a decomposition into two residual holes, not a completed mathematical proof.
Hole closed:
`AlgebraicGeometry.Scheme.Modules.externalGlobalSectionsTensor_bijective`.

Two holes added:
- `AlgebraicGeometry.Scheme.Modules.externalGlobalSectionsTensor_bijective_of_isAffine_right`
  (`lem-sc-external-global-sections-tensor-affine-right`): the first finite equalizer,
  with the second factor affine, including affine chart calculations.
- `AlgebraicGeometry.Scheme.Modules.externalGlobalSectionsTensor_bijective_of_finite_cover`
  (`lem-sc-external-global-sections-tensor-finite-cover`): general descent from prescribed
  chart and overlap bijectivities, with no quasi-coherence, affine, compactness, or
  diagonal assumptions. The conclusion is conditional on strictly local comparisons.

Each hole is exactly a public theorem proved by `by sorry` in its own new module.
No definition, existing signature, or target was changed. No hole was added to the
item's proof. Empty schemes, empty covers, empty overlaps, and zero coefficients were
checked in the mathematical proof sketches; only finite products are tensored.

## No longer needed

No imports or modules are pruned. All original public imports supply the unchanged statement.
The following old proof dependencies leave the item's direct proof_deps:
- `def-sc-scalar-global-sections-comparison`;
- `def-weil-sheaf-of-modules-category`;
- `lem-weil-pbc-fibre-product-affine-spectra`;
- `lem-weil-pbc-module-pullback-affine-sections`;
- `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`.
These remain needed transitively: the affine calculations belong to the affine-right
residual, while the scalar comparison and sheaf category belong to both residuals.
Their removal from the direct dependency list therefore prunes no module.

## Where the brief, the DAG or earlier work was wrong

The source plan names affine section comparisons but does not provide a Lean theorem
assembling either finite-cover equalizer. These are the two residual statements now
written explicitly. The affine-diagonal criterion requires `(f := g)` to avoid a stuck
morphism metavariable; this was checked and corrected in the independently compiling
cover construction.

The quasi-coherent restriction instance needs the proof-only import
`Mathlib.AlgebraicGeometry.Modules.Tilde`; it was added and the isolated check passes.

The first worker stopped before the independent-reading gate. This second reading
supplies that review; the earlier process blocker no longer applies.

## New nodes

`lem-sc-external-global-sections-tensor-affine-right`, in
`Sheaf.AlgebraicGeometry.ExternalGlobalSectionsTensorAffineRight`: the original first-cover
argument with an affine second factor. Its proof explains the algebraic affine-chart
comparison and the single equalizer. This is a strict special case of the original theorem.

`lem-sc-external-global-sections-tensor-finite-cover`, in
`Sheaf.AlgebraicGeometry.ExternalGlobalSectionsTensorFiniteCover`: descent from local
bijectivity on a prescribed finite cover and its overlaps. Its proof explains pullback and
restriction compatibility and the equalizer diagram. It does not assume or establish any
of the local bijectivities. Both new nodes record the actual logged LeanFinder, Loogle, and grep searches,
plus the newly attempted, unavailable LeanSearch service; and the blueprint searches for global sections tensor, tensor,
Kunneth, and external found no blueprint node stating either residual. No change record
is needed because no existing interface changed.


## Second reading by H3

1. Interface preservation: PASS. Diffed the sole existing module against the repository.
   Only four proof-only imports and the theorem body changed. The existing declaration's
   signature, visibility, and docstring are byte-for-byte unchanged; there are no new
   definitions, forced adaptations, or statement change records.
2. Proof and trust: PASS as a decomposition. All three modules compile locally without
   warnings. Scratch copies with #print axioms show exactly propext, Classical.choice,
   Quot.sound, and sorryAx for each of the three theorems. The only delivered sorries are
   the two named residual theorems listed above. No forbidden declarations or hollow
   definitions occur. The finite cover is constructed from affineCover.finiteSubcover;
   no arbitrary data witness is selected from an unproved existence theorem.
3. Residual statements: PASS. Read both signatures and complete proof docstrings, and
   checked them against Stacks Tag 0BED and the explicit section map's definition.
   Affine-right performs just the first equalizer, using affine chart algebra; finite-cover
   descent assumes the local comparisons and performs just the second equalizer. Neither
   is a renamed version of the original hypotheses and conclusion. Finite-cover descent
   needs no quasi-coherence: it uses sheaf gluing and exact tensor over the field.
   Empty index sets force Y empty; empty overlaps, X empty, and zero F or G give zero
   section modules. A singleton top cover reduces to its local bijectivity hypothesis.
   The affine-right algebraic inverse on pure tensors is balanced over A tensor_k B.
   New LeanFinder search for tensoring sections with a vector space and finite-cover
   descent found ring-sheaf equalizers and restriction tools, not either residual.
   Loogle found Module.Flat.ker_lTensor_eq; grep found generic equalizer machinery.
   Searched the repository Sheaf and WeilConjectures sources for section/tensor and
   equalizer terminology: affine chart lemmas exist, but neither assembled comparison.
   Closing either residual requires substantial comparison/gluing formalization, not a
   short application of an existing result.
4. Route and pruning: PASS with report repair. The target proof constructs the finite
   affine cover of Y, derives affine overlaps from g's diagonal, preserves quasi-coherence
   under restriction using Mathlib's Tilde instance, and applies the two residuals.
   Each added import is used, and public imports supply the unchanged interface.
   The unit sk-prop-av-cube has empty realized entries for this item; no unit or chapter
   route is bypassed. Corrected No longer needed to name every old dependency removed
   from the direct proof_deps, distinguishing this from actual module pruning.
5. DAG agreement: PASS. The target's three steps and dependency union match the Lean
   proof, including the two Mathlib leaves. The new nodes' statements match their Lean
   signatures, and their source, proof steps, dependency unions, proof_origin, searches,
   status, created, blueprint, chapter/unit, and lean records are present. The original
   node's semantic statement is unchanged. Added the independent searches to both new
   nodes; existing node edits remain confined to stage-3-owned fields.

Second reading changed the dependency-pruning report, removed obsolete process-blocker
text, recorded independent searches in the new nodes, and appended this review.
No Lean repair was necessary. One original hole is closed syntactically, two holes are
added, so this is a decomposition with net -1 holes closed, not a completed proof.
