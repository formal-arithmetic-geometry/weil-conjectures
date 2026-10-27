## What changed

Preserved the statement of `AlgebraicGeometry.ProEtale.spIntegralRationalRootBasis` and
replaced its hole by an argument using an isomorphism of the finite towers, two
limit cones on the given slice, and preservation of a local basis by scalar extension.
The limit transport and the identification of reconstructed regular coefficients with
the section-module unit are proved in the item module.

Added `SpEllCoefficientTower`: it constructs the actual quotient modules, reduction
maps, and reduction cone, including the proofs of their integral linearity and cone
compatibility. Its completeness theorem is proved by the canonical continuous
coefficient comparison, the native continuous ell-power limit, and the initial
successor functor.
Added `SpRootBasisTowerComparison` for the finite-level basis and transition comparison.
Added `SpSliceScalarExtensionBasis` for preservation of a prescribed local basis under
extension along any commutative internal coefficient-ring map.

The new helpers use explicit universes and functor types, with normal transparency
checking enabled locally; the original statement keeps its original elaboration
setting. All new proof imports of the item are private. No existing public signature,
definition, attribute, or public import was changed. The unit route is retained.

## Proved and sorry left

The original module had one hole:
`AlgebraicGeometry.ProEtale.spIntegralRationalRootBasis`. Its combining proof is now
complete. This is a decomposition, not a claim that its axioms are sorry-free.

`AlgebraicGeometry.ProEtale.spEllCoefficientCone_isLimit` is also proved, including
the exact quotient projections and the integral module action.

The delivery leaves this finite-level obligation:

- `AlgebraicGeometry.ProEtale.spRootBasisTowerComparison`
  (`lem-sp-root-basis-tower-comparison`): the finite-level linear comparison and its
  normalized transition squares, without any inverse-limit or rational assertion.

`AlgebraicGeometry.ProEtale.spSliceScalarExtensionBasis` is proved. Its proof
constructs the ordinary tensor comparison under section reconstruction, restricts
sheafification to the slice, and tensors the prescribed basis with the new ring.
The scalar module compiled cleanly on the project server in 13.5 seconds.

Thus one original hole is closed and one strictly finite-level hole is added.
The item itself contains zero holes; the packet contains the single named hole
listed above. This is a decomposition, not a net reduction in the packet's hole count.

The item and all three new modules have been checked using the required server
compiler. The item compiled cleanly in 14.6 seconds, and the scalar-extension
module in 13.5 seconds. The coefficient module and finite-tower statement also
compiled without errors or warnings. The delivery tool performs the final checks
on the complete packet, including the redundant-import cleanup.

## No longer needed

No original import was removed. Redundant explicit proof imports were removed:
`Mathlib.CategoryTheory.Category.GaloisConnection`,
`Mathlib.CategoryTheory.Limits.Final`, `Mathlib.Data.Nat.SuccPred`, and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`; their declarations are already
available through the retained public imports.

The new main proof does not use
`det-prop-sfb-qlbar-colimit-x-invert-ell`: scalar extension preserves a given basis
without a localization or flatness argument. It also does not use
`lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`: this item has no field
colimit or algebraic-closure conclusion. These two planned dependencies were removed
from the item's proof route.

The uniformizer coefficient-limit node
`det-prop-sfb-qlbar-colimit-x-integral-limit` is also unnecessary for this route:
the native continuous ell-power limit and its positive tail apply directly.

The finite-discrete comparisons and finite-level comparison remain needed by the new
finite-tower obligation. They have been moved into that proof route, not claimed as
globally pruned. The previous coefficient-limit and localization modules also remain
in the unchanged upstream public import closure; this delivery does not withdraw
them. No module is withdrawn, and no adopted source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The original plan combines several distinct comparisons. The existing finite-level
comparison supplies an abelian-sheaf isomorphism, but does not state linearity and
compatibility with the normalized successor maps. The planned coefficient-limit
declaration uses uniformizer quotients and another coefficient presentation. The native ell-power completeness theorem avoids that
translation; naturality of the canonical continuous coefficient comparison supplies
the required normalized cone isomorphism directly.

No statement is disputed. For coefficient completeness, the successor functor is
initial on the opposite natural-number category, so passing to positive exponents
retains the source limit. For scalar extension, the statement also holds for zero
rings and empty slices, and requires no flatness. The finite-tower statement uses both the
root compatibility and the supplied normalization of every local basis map.

## New nodes

`lem-sp-ell-coefficient-cone-limit` records the coefficient-only completeness step,
proved using the positive tail of the native continuous ell-power tower and
naturality of the canonical coefficient comparisons.

`lem-sp-root-basis-tower-comparison` records finite-level basis maps and the transition
squares. It makes no integral-limit or rational assertion and is not a renamed copy of
the original obligation.

`lem-sp-slice-scalar-extension-basis` records the independent scalar-extension step.
It concerns an arbitrary internal commutative coefficient-ring map and an arbitrary
module already trivialized on the specified slice; it constructs no root tower and
assumes no coefficient completeness.

No change record is needed: no existing interface or definition is repaired.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
