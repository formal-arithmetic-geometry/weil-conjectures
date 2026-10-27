## What changed

Replaced the whole-proof sorry in
`AlgebraicGeometry.SymmetricProjTautologicalCharts.free_compatibility_of_normalized_quotient`
by a complete assembly of the ordered relative comparison, the existing proved
`RelativeProjectiveSpace.existsUnique_freeProjectiveBundleBaseChangeSpace`, and the
ordered twist-gluing comparison. The standard-model isomorphism is the composite of
the relative comparison and the existing normalized base-change comparison. Its
structure equation is proved by composition and associativity.

Added two modules, each containing one public theorem:
`Sheaf.AlgebraicGeometry.SymmetricProjOrderedRelativeComparison` and
`Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistGluing`.
Validation: `lcompile.py --all` compiled the relative comparison, twist-gluing
statement and original module successfully in 16.6 s, 18.1 s and 15.8 s respectively.
All new imports in the item are private proof imports. Existing signatures,
public imports, definitions, attributes and target statements are unchanged.
The item node's proof and dependencies now follow this assembly.

## Proved and sorry left

This is a decomposition, not a completed geometric proof or a net hole reduction.
The original module had one sorry and now has zero. Its theorem has a complete
Lean proof from the two strictly smaller statements and the existing normalized
standard-model comparison. Unconditionally proved original holes: 0 of 1;
original holes decomposed: 1; new holes: 2; net holes closed minus added: -1.

Every sorry added, and all the sorries left in this delivery:

- `AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_ordered_relative_comparison`
  (`lem-trf-symmetric-proj-ordered-relative-comparison`): constructs only the relative
  scheme isomorphism and affine polynomial/twist comparisons. It neither quantifies
  over a tautological quotient nor asserts a global standard twist comparison.
- `AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_ordered_twist_comparison`
  (`lem-trf-symmetric-proj-ordered-twist-gluing`): assumes the scheme comparisons,
  their affine polynomial/twist normalizations, and the standard-model normalization;
  it constructs only the global line isomorphism and its coordinate equations.

Both statements retain r=0, empty charts, arbitrary schemes and all normalized
quotients. The local proof uses invertible coordinates only after passage to a
standard chart, so zero and nilpotent coefficients are allowed.
No sorry is inside a definition or a partially completed proof.

## No longer needed

No existing import was removed and no module is withdrawn. No unit route is changed.
The original parent no longer directly uses
`lem-weil-pbc-symmetric-algebra-free-module-polynomial`,
`lem-weil-pbc-symmetric-algebra-graded`,
`prop-nagata-relative-proj-functoriality`,
`def-nagata-relative-projective-space`, or `def-pc-projective-space-twist`
as proof steps: their work is assigned to the two smaller statements or the existing
standard-model theorem. They remain needed below those steps; none is claimed as
pruned from the targets' closure. The parent proof dependencies are exactly the two
new nodes and `lem-trf-free-projective-bundle-base-change-space`.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated the comparison with standard base-change projective
space as part of the unfinished construction, but its normalized scheme comparison
is already proved in `FreeProjectiveBundleBaseChangeSpace`. Reusing it avoids a
second construction and supplies the precise affine normalization needed for gluing.

The existing ring-level Mathlib polynomial equivalence does not itself supply either
the relative-Proj chart equation or the global quotient-preserving twist comparison.
The available frame-model theorem has a different realization and finite locally free
inputs; it does not directly prove the statement for an arbitrary normalized D on
the fixed canonical symmetric Proj. No false statement was found.

## New nodes

`lem-trf-symmetric-proj-ordered-relative-comparison`: the ordered algebra and relative
scheme portion of the original argument, together with the affine degree-one twist
comparison. Its source proof specifies beta, gamma, their Proj maps, the chart equation
and the degree-one section equation.

`lem-trf-symmetric-proj-ordered-twist-gluing`: the sheaf-gluing portion after all scheme
and affine twist comparisons have been supplied. Its source proof uses the normalized
integral polynomial charts, D.generator, local free frames and gluing of inverse maps.
Neither new statement is the original HasFreeCompatibility obligation under another
name. The existing normalized standard-model theorem is a separate essential input
to the complete parent proof. The proof-only record is
`coord/changes/S1-symmetric-proj-free-reduction.md`; it records the unchanged consumer
interface and the two new theorem modules. No existing definition is changed.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
