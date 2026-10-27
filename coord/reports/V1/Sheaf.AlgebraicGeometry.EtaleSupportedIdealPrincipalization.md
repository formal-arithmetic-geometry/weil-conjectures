## What changed

Replaced the proof hole in
`AlgebraicGeometry.Scheme.IdealSheafData.exists_admissibleBlowup_isInvertible_comap_etale`
with a Lean proof applying the existing module-flattening theorem and two smaller geometric
lemmas. The statement, universes, hypotheses, conclusion and public imports of the item are
unchanged. No other existing Lean module is changed.

The proof of the open hypotheses is complete: the ideal inclusion restricted to the open is
an isomorphism, checked using its affine section image and injectivity. Its restricted module
is therefore finitely presented. At each point of the open the induced stalk inclusion is an
isomorphism; a private, proved structure-module stalk identification and flatness of the etale
stalk ring map give relative flatness after restriction of scalars. There is no arbitrary
object chosen from an unproved existence theorem in a definition.

After applying flattening, the proof transports finite presentation and relative flatness
along the strict-transform/extended-ideal isomorphism. It pulls back the Cartier boundary using
the existing blowup theorem, and proves the unit-ideal restriction by the pullback square,
`support_comap`, restriction of the first projection and `comap_comp`. Base-change instances
supply the etale, quasi-compact and separated properties of the second projection. Applying
the new rank-one criterion finishes the theorem for that very blowup.

Two new modules contain the remaining strictly smaller geometric steps. Their statements have
been checked against the parent's proof and the Stacks sources. In particular neither is a
renaming or a repackaging of the modification-existence statement: one is an isomorphism for
an arbitrary specified centre and flat morphism; the other is a criterion for a specified
finitely presented relatively flat ideal and has no blowup or modification existence clause.
The parent node now records exactly this composition and both new nodes record their sources,
complete proofs in words, Lean statements and three kinds of Mathlib search.

Compilation uses only the prescribed `lcompile.py` server route. All three files compiled
in import order (3.4 s, 4.0 s and 31.4 s). The schematic-density hypothesis is retained
with an explicit local reference without changing its binder; the route needs no additional
schematic-density argument. The delivery tool runs final compilation
and the required mechanical and axiom checks.

## Proved and sorry left

Original holes: 1. The original hole closed is
`AlgebraicGeometry.Scheme.IdealSheafData.exists_admissibleBlowup_isInvertible_comap_etale`
(node `lem-per-etale-supported-ideal-principalization`). Its Lean proof and all private helpers
are complete. There are zero textual holes left in the item module.

Added holes: 2, each the entire proof of a public theorem in its own module:

- `AlgebraicGeometry.Scheme.Modules.nonempty_moduleStrictTransform_ideal_iso_comap`,
  node `lem-per-flat-ideal-strict-transform-comparison`.
- `AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_of_etale_flat_finitePresentation`,
  node `lem-per-etale-flat-supported-ideal-invertible`.

This is a decomposition, not a net proof-completion claim: one upper hole closed and two
lower holes added (net minus one). Existing holes in the imported flattening theorem are
unchanged. No sorry was added to a definition or a private declaration.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.IdealTensorPullbackComparison`.
- `WeilConjectures.Blowup.Complement`.
- `Sheaf.AlgebraicGeometry.ModuleStrictTransform` (still publicly supplied by flattening).
- `WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`.
- `Sheaf.TraceFormula.FlatFibreFreeNeighbourhood`.

The direct dependencies `lem-trf-relative-flat-cartier-support`,
`lem-pur-ideal-tensor-pullback-comparison`, `thm-nagata-global-blowup-complement`,
`def-trf-module-strict-transform`, `lem-weil-pbc-etale-fibre-discrete-separable-points`,
`lem-trf-flat-fibre-free-neighbourhood` and `def-nagata-invertible-ideal` are replaced in the
parent proof by the two new nodes. Their mathematics remains required in those smaller
subarguments; this delivery does not claim that those modules or nodes are globally obsolete.
The five old direct generic-tool approvals whose proofs move into the new nodes are removed
from the parent's top-level `tool_uses`; the two remaining approvals are kept in their order.

No existing module is withdrawn and no blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The parent's step 3 is mathematically sound but its label `elementary: true` hides a genuine
module-sheaf kernel/quotient comparison. The ideal tensor-pullback image statement alone does
not identify that quotient. This delivery names the missing comparison explicitly rather than
assuming it follows immediately from the imported image theorem.

For that comparison the original Cartier boundary is unnecessary: the exceptional centre
itself becomes Cartier on its blowup, and flatness of the second projection suffices for
injectivity away from it. The new comparison therefore applies to any specified finite-type
centre and any ideal under a flat morphism, without changing the parent's statement.

The final rank-one step also needs a module-to-ideal calculation beyond the stated
free-neighbourhood theorem: a nonzero localization forces the rank to be one and the ideal
inclusion makes its generator regular. The second new node retains precisely this missing
argument together with the existing fibre-flatness/free-neighbourhood input.

## New nodes

`lem-per-flat-ideal-strict-transform-comparison`, in
`lean/Sheaf/AlgebraicGeometry/FlatIdealStrictTransformComparison.lean`, isolates the equality of
the restriction kernel and the pulled-back ideal-inclusion kernel for a flat morphism and a
specified base blowup. Its proof uses principalization of the exceptional ideal,
Cartier-support injectivity, the blowup complement isomorphism and the existing ideal image
comparison. Zero and unit ideals, an empty source and an empty blowup satisfy the same
kernel argument. No new construction is chosen from a sorried existence statement.

`lem-per-etale-flat-supported-ideal-invertible`, in
`lean/Sheaf/AlgebraicGeometry/EtaleFlatSupportedIdealInvertible.lean`, isolates the finite
presentation plus relative flatness criterion for an ideal trivial off a base Cartier
divisor. Etale fibre local rings are fields, so the existing free-neighbourhood theorem
applies; localization on a nonempty affine Cartier chart forces rank one. The regularity of
the generator follows from the actual ideal inclusion. The assertion is vacuous on an empty
scheme and includes the unit ideal and nonreduced bases.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
