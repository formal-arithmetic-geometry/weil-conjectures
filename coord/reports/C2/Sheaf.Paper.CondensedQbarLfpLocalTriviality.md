## What changed

Repaired reviewer X-c7b77's E1 and H8/E5 findings. The new matrix theorem
`AlgebraicGeometry.ProEtale.exists_condensedQbar_finiteFree_refinement` now takes
`(hf : WeaklyEtale f)` immediately after `(f : Y ⟶ X)`. The parent theorem supplies
`𝒰.forgetQc.map_prop i`. The matrix node's `statement` and `lean.statement` have the
identical corrected signature. No existing target signature changed.

The matrix theorem docstring and its node now give seven complete natural-language
steps: exact restriction of a presentation, realization in one finite coefficient
field, intrinsic geometric rank on f(|Y|), generalization lifting using hf, clopen
rank levels in that image subspace, maximal-minor elimination, and composition of
covers with all empty and zero-rank cases. The rank argument explicitly proves that
the image is generalization-stable and that its irreducible closed subsets have
generic points. It does not assert finite presentation or a rank function outside
the image. Exactness, coefficient comparison, finite-field directedness, and
geometric evaluation are included in the node's dependency list.

The target module retains the earlier Lean reduction: extract the presentation
cover, refine every member, and compose the refinements. The proof-only imports
remain the two new modules. The original public imports are restored: the earlier
pruning hid monoidality instances required by the downstream importer. The change
record is `coord/changes/condensed-qbar-matrix-weakly-etale.md`.

## Proved and sorry left

The original module's one hole is closed by the compiling Lean proof of
`AlgebraicGeometry.ProEtale.condensedQbar_lfp_locally_free`. This is a decomposition
into two strictly smaller open obligations, not an axiom-free proof: relative to
the original item it closes one hole and adds two (net -1). This repair introduces
no additional holes beyond the returned delivery's two splits.

Every remaining sorry in the delivery:

- `AlgebraicGeometry.ProEtale.exists_condensedQbar_finiteFree_refinement`
  (`lem-weil-pbc-condensed-qbar-lfp-matrix-refinement`): still needs formalization of
  the seven documented coefficient, geometric-rank and matrix-elimination steps.
- `AlgebraicGeometry.ProEtale.exists_condensedQbar_refinement_of_local`
  (`lem-weil-pbc-condensed-qbar-cover-composition`): still needs the sigma-indexed
  cover composition and transport of the local isomorphisms along its composite maps.

All three delivered modules compile with `lcompile.py --all`, including the direct
importer of the repaired matrix theorem. The unchanged downstream module
`Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` also compiles against the
final sandbox overlay after restoring the original public imports (42.5 seconds).

## No longer needed

No public imports are pruned: the parent keeps its original public interface.
The former proof-only imports removed from the parent are:

- `Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.Properties`
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`
- `Mathlib.RingTheory.Ideal.GoingDown`
- `Mathlib.Topology.NoetherianSpace`
- `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`
- `Sheaf.Paper.CondensedPointBasisEvaluation`
- `Sheaf.Paper.GeometricFieldProEtaleEvaluation`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`

These are removed as direct imports of the parent. The matrix argument still needs
the corresponding exactness, coefficient, evaluation, and topological nodes listed
in its `proof_deps`; none is claimed mathematically unnecessary. The fixed-member
proof uses a chosen geometric lift of a point in f(|Y|), so it does not need the
old separate covering-base-change step citing
`lem-galois-fpqc-covering-base-change`. The parent itself now uses precisely the
two split nodes. No additional module or node is withdrawn in this repair.

## Where the brief, the DAG or earlier work was wrong

E1: The returned matrix statement allowed arbitrary f while its proof invoked flat
going-down. WeaklyEtale f now provides flatness and makes Y an object of X_proet;
the parent already has this hypothesis for its presentation-cover maps.

H8/E5: The returned three-line outline and compressed node step omitted essential
arguments. The replacement gives finite-field realization, choice-independent
geometric dimension, the lifting argument, noetherian topology on f(|Y|), and the
explicit Schur-complement calculation. It includes zero rows, zero columns, rank
zero, empty pieces, and the empty scheme.

The previous report's claim that a kernel timeout justified splitting was
unsupported and is withdrawn. Slow elaboration is not a valid reason to split
under this project's rules. The delivery records two genuine open mathematical
obligations; this repair corrects their statement/proof documentation without
claiming to have formalized those obligations. The earlier second-reading text
predates this return and has been removed for a fresh independent reading.

The earlier public-import pruning was also incorrect. Compiling the unchanged
`Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` against that overlay failed
at lines 240, 646 and 709: `failed to synthesize NatTrans.IsMonoidal e.inv`. Restoring
the original public imports avoids changing that downstream module. The obsolete
public-import-pruning change record has been removed.

## New nodes

No further nodes were added during the repair. The returned delivery's nodes remain:

`lem-weil-pbc-condensed-qbar-lfp-matrix-refinement`, in
`lean/Sheaf/Paper/CondensedQbarLfpMatrixRefinement.lean`, is the fixed-member matrix
argument with its corrected weakly-etale hypothesis and complete proof in words.
Its signature repair is recorded in
`coord/changes/condensed-qbar-matrix-weakly-etale.md`.

`lem-weil-pbc-condensed-qbar-cover-composition`, in
`lean/Sheaf/Paper/CondensedQbarLfpCoverComposition.lean`, is the composition of the
presentation cover with its finite-free refinements.

## Second reading by C2

1. **Signatures and definitions.** I compared the delivered target module with the
repository version. The declaration signature of
`AlgebraicGeometry.ProEtale.condensedQbar_lfp_locally_free` is unchanged byte for
byte; only its proof and imports differ. The two new declarations have signatures
matching their DAG `lean.statement` fields. No definition was changed.

2. **Compilation and axioms.** I compiled all three delivered modules with
`lcompile.py --all`; they compile without errors. The target proof contains no
`sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The two split
lemmas intentionally retain their documented `sorry`s and are the only new holes;
the target therefore depends on `sorryAx` through those named obligations.

3. **Split statements and nodes.** The matrix-refinement and cover-composition
statements are strictly smaller than the target, have complete source and proof
documentation, and their DAG nodes match the Lean declarations, dependencies,
status, and proof origins. The matrix hypothesis includes the required
`WeaklyEtale f`; the composition lemma states only the indexed cover-composition
obligation. No duplicate library declaration was found by the recorded search.

4. **Proof route and pruning.** The target proof follows the unit route: obtain the
presentation cover, apply the fixed-member refinement, then compose covers. The
removed direct imports are proof-only dependencies now encapsulated by the matrix
obligation. I checked the unchanged downstream importer against the sandbox overlay;
restoring the original public imports is necessary for its monoidal instances.

5. **Unit and DAG agreement.** The target node uses exactly the two split nodes, and
the matrix node records all seven documented mathematical steps, including the
generalization, rank, minor, and edge-case arguments. The unit’s realized route is
therefore preserved. No statement change beyond the declared matrix-hypothesis
repair is present.

I changed only this second-reading report section after review; no Lean proof or DAG
content required further repair.
