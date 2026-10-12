## What changed

Replaced `AlgebraicGeometry.Scheme.Modules.exists_local_normal_form_of_constantRank_nonempty`
with a complete Lean reduction. Its signature and public imports are unchanged.
The proof extracts a nonvanishing minor using the proved source-library
`le_rank_map_appTop_iff`, obtains an invertible leading block, applies the proved
Mathlib `CategoryTheory.Biprod.gaussian`, kills its complementary block, absorbs
the pivot automorphism into the source basis, and reorders that basis with
`biprod.braiding`. The final factorization follows from `biprod.hom_ext` and
projection identities. The node's proof and dependencies now follow that code.

Added the proof-only imports `Sheaf.AlgebraicGeometry.Modules.LocalInvertibleMinorBlock`,
`Sheaf.AlgebraicGeometry.Modules.ComplementaryBlockVanishes`, and
`Mathlib.CategoryTheory.Preadditive.Biproducts`. The two new modules state the
remaining geometric parts separately; each has one public theorem, a source,
a full proof in words, and its own node. Gaussian elimination itself remains
proved Mathlib code rather than a new hole.

All three files compile together using `lcompile.py --all`, without warnings.
The new statements were checked mathematically on rank zero, maximal rank,
zero-dimensional complements, empty U, and a larger than m or n. In the pivot
lemma the last case is excluded by nonvanishing of the minor at a point; the
complementary-block lemma remains valid even on an empty open.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_local_normal_form_of_constantRank_nonempty`
(node `lem-pc-constant-rank-map-local-normal-form-nonempty`). No `sorry` remains
in the item's module. This is a decomposition, not a complete proof independent
of new holes: one hole closed, two holes added, net minus one hole.

The two holes added and still left are:

- `AlgebraicGeometry.Scheme.Modules.exists_local_invertible_minor_block`, node
  `lem-pc-local-invertible-minor-block`, in
  `Sheaf.AlgebraicGeometry.Modules.LocalInvertibleMinorBlock`.
- `AlgebraicGeometry.Scheme.Modules.complementary_block_eq_zero_of_rank_le`, node
  `lem-pc-complementary-block-vanishes`, in
  `Sheaf.AlgebraicGeometry.Modules.ComplementaryBlockVanishes`.

The first concerns a specified minor on an arbitrary scheme: no reducedness,
no constant-rank hypothesis, no diagonal form, and no zero-block assertion.
The second constructs neither a neighbourhood nor bases: it assumes the
block form and proves that its given residual map is zero. They are separate
parts of the argument, not renamed copies of the original statement.
No data definition or axiom was added.

## No longer needed

No original imports were removed: both public imports serve the unchanged
signature. The direct proof no longer uses `lem-weil-matrix-rank-field-extension`
or its module `Sheaf.LinearAlgebra.MatrixRankFieldExtension`. The proved
rank-minor criterion selects a pivot directly at the image point, and the
vanishing argument only needs injectivity of residue-field maps to detect zero
entries, not a separate rank-invariance theorem. This dependency was planned
in the node but was absent from the original Lean imports.

The old direct dependencies `def-pc-reduced-scheme`, `def-weil-pbc-free-module`,
`lem-weil-pbc-open-immersion-module-pullback-restriction`, and
`lem-weil-pbc-zero-locus-eq-iff-radical-eq` are now needed by the two lower nodes,
not pruned from the overall argument. `def-weil-matrix-rank` is still needed
for pivot selection. No other node or module is claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The named dependencies of the original plan do not themselves state either
local coordinate splitting with an invertible minor or zero detection for the
complementary block. Those are the two newly stated intermediate theorems.
The original plan's categorical Gaussian elimination does already exist:
`CategoryTheory.Biprod.gaussian` in Mathlib's Preadditive/Biproducts.lean.

The blueprint source file is not present in this local literature checkout.
The retained unit record, parent node, and original module docstring contain
the normal-form argument; these were read. New proof details are explicitly
recorded as written by an agent, with the original source and exact step named.
The unit's reduced-base local normal-form route is retained. No statement or
definition was changed, and no forced adaptation was needed.

LeanSearch returned HTTP Internal Server Error for both new statements and is
recorded as unavailable. LeanFinder returned related free-sheaf construction,
rank-condition, and rank-at-stalk results, not either geometric lemma. Loogle
returned matrix determinant/rank results. Targeted source searches found the
categorical Gaussian construction and no geometric pivot/vanishing theorem.
Blueprint searches for “invertible minor” and “complementary block” returned
zero matches; related finite-free residue-localization nodes concern a ring
map's full injectivity/isomorphism and do not state the required sheaf bases.

## New nodes

`lem-pc-local-invertible-minor-block` is the specified-pivot part of the source's
normal-form claim. Its statement requires only nonvanishing of a specified
minor at the chosen point. Its proof describes an affine shrinking, completing
the selected coordinates to bases, constructing the pivot inverse by the
adjugate identity, and transporting the bases through pullback and restriction.
It is in `dag/nodes/sec-picard-framework/lem-pc-local-invertible-minor-block.json`.

`lem-pc-complementary-block-vanishes` is the reducedness part after Gaussian
elimination. Its proof pulls back a given block equality, uses the fibre rank
bound to force the complementary fibre map to zero, descends zero entries
through an injective residue-field extension, applies the intersection-of-primes
criterion on reduced affine opens, and glues by the sheaf axiom.
It is in `dag/nodes/sec-picard-framework/lem-pc-complementary-block-vanishes.json`.
There are no change records because existing interfaces were not changed.

## Second reading by K1

1. **Interface and visibility.** Compared the delivered item module with the repository version. The theorem signature is byte-for-byte unchanged; the former proof-only rank-extension import is replaced by proof-only imports for the two split lemmas and Mathlib Gaussian elimination. Verdict: pass.

2. **Compilation and kernel safety.** Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds. The only remaining `sorry`s are the two named split theorems, with no axioms, unsafe, opaque, extern, or hollow definitions. Verdict: pass.

3. **Split statements.** Read both new declarations and their docstrings and checked their edge cases (rank zero, maximal rank, zero complements, empty open, and impossible oversized pivots). They are strictly simpler than the target and are not duplicate library statements; each has a matching DAG node. Verdict: pass.

4. **Route and pruning.** The proof uses the existing rank-minor criterion, Mathlib `Biprod.gaussian`, and the two genuinely separate geometric split lemmas. The unit's local normal-form route is retained. The old field-extension rank dependency is no longer used and is removed from the node dependencies; no further import can be pruned. Verdict: pass.

5. **DAG agreement.** Updated item-node proof steps, proof dependencies, and proof origin match the Lean proof. The two added nodes carry source, proof plans, searches, Lean declarations, and split status. Verdict: pass.

I changed only this report section; no Lean statements or definitions were changed during second reading.
