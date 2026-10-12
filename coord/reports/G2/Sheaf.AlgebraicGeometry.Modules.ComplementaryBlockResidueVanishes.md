## What changed

The item module now proves `AlgebraicGeometry.Scheme.Modules.complementary_block_residue_eq_zero_of_rank_le` with its signature unchanged. Proof-only imports are `WeilConjectures.Mathlib.AlgebraicGeometry.Scheme`, `WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank`, and the new `Sheaf.AlgebraicGeometry.Modules.LocalBlockResidueRank`.

The proof transfers the given field-valued rank bound to κ_Y(j(x)) using the existing, proved nonvanishing-minor criterion and basic-open evaluation lemmas. It combines the local block-rank equality with the bound by natural-number cancellation, then proves the complementary matrix zero from its zero-dimensional image, entry by entry. The local block-rank equality is split off as a separate item; its proof requires the restriction/pullback and biproduct comparisons.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.Modules.complementary_block_residue_eq_zero_of_rank_le` (node `lem-pc-complementary-block-residue-vanishes`). Added one whole-proof `sorry`: `AlgebraicGeometry.Scheme.Modules.local_block_residue_rank` (new node `lem-pc-local-block-residue-rank`). This is a decomposition, with one hole closed and one added, not a complete mathematical proof or a net hole reduction.

The new statement has no `hrank`, no field-valued test point g, and no vanishing conclusion: it computes the residue rank of an arbitrary displayed local invertible block form. It is a strict part of the original argument. The original theorem's rank transfer, arithmetic cancellation, and zero-matrix deduction are complete Lean proofs. No other holes are added, and no existing signatures, definitions, or visibility are changed.

## No longer needed

No original imports were removed, and no existing node or module is eliminated entirely by this delivery. The original proof's lift of the arbitrary field-valued g through U is unnecessary: nonvanishing minors transfer its bound directly. The restriction/pullback, biproduct, free-module, and field-extension machinery remains needed for the new local rank-calculation item; it is not claimed as pruned. An explored import of `WeilConjectures.AlgebraicGeometry.Modules.FreeComplex` was omitted in favor of the narrower Scheme and Matrix.Rank modules. The unit's normal-form route is retained.

The old parent `proof_deps` entries no longer used directly by the parent proof are
`def-pc-module-pullback`, `def-weil-additive-category`, `def-weil-open-immersion`,
`def-weil-pbc-free-module`, `def-weil-sheaf-of-modules-category`, and
`lem-weil-pbc-open-immersion-module-pullback-restriction`. They are relocated to the
new local block-rank node's proof plan, not pruned from the import closure. The
parent retains `def-weil-matrix-rank` and `def-weil-residue-field` and adds
`lem-pc-local-block-residue-rank`. No modules are claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The existing dependency declarations supply restriction/pullback comparison and matrix rank definitions, but none states the local block-rank equality itself. The plan's image-dimension calculation therefore needed a separate intermediate statement. The shorter minor argument avoids the plan's arbitrary-point lifting and subsequent injectivity descent. LeanSearch returned Internal Server Error; LeanFinder, Loogle, and source searches were available. The existing docstring describes the former proof plan and is preserved; the delivered node records the actual route.

Edge cases for the new statement: a=0 gives the rank of the complementary map; empty complementary indices have zero second image; if a exceeds m or n the required local decomposition cannot exist at the supplied point; empty U admits no x. Reducedness is not needed.

## New nodes

`lem-pc-local-block-residue-rank`, in `dag/nodes/sec-picard-framework/`, states the residue block-rank equality in `Sheaf.AlgebraicGeometry.Modules.LocalBlockResidueRank`. Its source is the existing parent's proof (3), steps 1 and 2. The declaration and node contain the complete pullback, basis-invariance, and direct-sum dimension argument. No change records or forced adaptations are needed.

## Second reading by G2

1. Compared the delivered existing module with the repository using `diff` and
   byte-compared its entire theorem signature. Verdict: unchanged statement,
   definitions, visibility, and original public imports. The only additions are
   three plain proof imports and the proof body. The separate rank module is new;
   no change records or forced adaptations are needed.
2. Compiled both modules in dependency order with `lcompile.py --all`: clean,
   without errors or warnings. Scanned both sources: exactly the reported whole-proof
   `sorry` in `AlgebraicGeometry.Scheme.Modules.local_block_residue_rank`; no forbidden
   declarations or hollow definitions. Independent scratch `#print axioms` checks
   cover both delivered theorems. Their allowed `sorryAx` dependency is recorded;
   this is a decomposition, not a complete proof of the import closure.
3. Read the new rank theorem, its docstring argument, and node. Verdict: true and
   strictly part of the argument; it does not assume the parent's test point or rank
   bound and does not restate vanishing. At a=0 it computes the complementary rank;
   with an empty complementary source or target that rank is zero. A supplied point
   rules out empty U, and the local fibre isomorphisms rule out a>m or a>n.
   Independently searched LeanFinder for image dimensions of direct sums, Loogle for
   `Matrix.rank, Matrix.fromBlocks`, and grep for `rank_freeMatrix`, rank maps, range
   dimensions, and biproducts. Read the nearby `FreeComplex` fibre-rank comparison and
   `LocalInvertibleMinorBlockData` restriction comparison. Results provide pieces
   (including `Module.finrank_directSum` and `Matrix.exists_rank_normal_form`), not
   the stated local sheaf comparison. Completing the sheaf/biproduct comparison is
   substantial; no quick closure was found.
4. Read the parent proof from the conclusion upward and checked its nonvanishing-
   minor transfer against the proved source lemmas. All three new imports are used
   only by the proof; original public imports are needed by the statements. Verdict:
   the shorter minor route is sound, and the local normal-form step is kept. Read
   `dag/units/sk-thm-picard-semicon.json`: its pre-existing `realized.statement` and
   sole `realized.steps` entry are empty, an existing metadata gap, not altered or
   bypassed by this delivery. No module is pruned.
5. Checked both nodes against the Lean signatures and checked that each
   `proof_deps` equals the union of its proof steps' `uses`. Read the sources,
   provenance, searches, creation, blueprint, chapter, unit, and Lean records of the
   new node. Verdict: the parent records the actual minor-transfer/cancellation
   proof; the child records the remaining restriction, fibre, and biproduct
   calculation. The new node satisfies the stage-3 fields and has a complete
   natural-language proof in its theorem docstring.

Second reading changed only this report: explicitly enumerated every old parent
proof dependency relocated to the new node, clarified that none is pruned from the
closure, and recorded the independent checks and the existing unit metadata gap.
The Lean proofs and statements were left unchanged.
