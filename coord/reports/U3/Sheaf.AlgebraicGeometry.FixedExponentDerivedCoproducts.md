## What changed

Proved `AlgebraicGeometry.Etale.isIso_sigmaComparison_rightDerivedLowerStar_of_fixedExponent`
in `Sheaf.AlgebraicGeometry.FixedExponentDerivedCoproducts`, with its signature unchanged.
All added helpers are private and proved. No definition or statement is weakened.
The file-scoped elaboration commands are documented in
`coord/changes/fixed-exponent-derived-coproduct-proof-scope.md`; public signatures
and imports are unchanged.

The shorter route uses the existing coinduction from abelian groups to Z/n-modules.
For a degreewise injective representative I of an abelian object A killed by n,
the counit identifies U Hom(Z/n,I) with the kernel of multiplication by n.
Divisibility makes `0 -> U Hom(Z/n,I) -> I -> I -> 0` short exact. Since multiplication
by n is zero after localization, representable exactness gives a section of the
first arrow. Thus A is a retract of an underlying Z/n complex. This is the dual
kernel version of the quotient-cone splitting in the original plan.

Applied the proved Z/n coproduct theorem, transported it through the natural
unbounded coefficient comparison, and proved an explicit inverse for the coproduct
comparison on retract families. Exact conservative coefficient forgetting reflects
the result. Empty families and n=1 are included by the same construction.
The unit route is unchanged: the item remains the fixed-exponent input to the
constant-coefficient projection formula, with only its internal reduction replaced.

Updated the existing node's proof, proof dependencies, proof origin, and removed
obsolete tool approvals. No source-library declaration is changed. No new public
statement or module is introduced.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.Etale.isIso_sigmaComparison_rightDerivedLowerStar_of_fixedExponent`
(node `lem-sf-fixed-exponent-derived-coproducts`).

Added 0 holes. Remaining holes in the delivered module: 0. No split-off statements.
Imported declarations remain the existing project interfaces; this report does not
claim to close every hole in their transitive dependencies.

## No longer needed

Removed proof imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`;
- `Sheaf.Algebra.Homology.RegularQuotientConeAugmentation`;
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`;
- `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`;
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`;
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`;
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.

The new route does not directly use nodes
`def-weil-presheaf-modules-sheafification`, `lem-pc-kflat-resolution`,
`lem-cbc-regular-quotient-cone-augmentation`,
`lem-weil-pbc-module-sheaves-grothendieck-abelian`,
`lem-kun-grothendieck-derived-coproducts`, and `lem-pc-derived-zero-third-split`.
The removed top-level tool approvals are exactly the five lemma nodes listed above;
the retained approvals are the unbounded comparison and the Z/n coproduct theorem.
The existing ordinary-forgetting colimit theorem and exact-derived-coproduct API
provide the required preservation theorem, and coinduced kernels replace derived
quotient cones. This is pruning of this item's direct route only; modules used by
other declarations or transitively by the retained interfaces remain in the library.

## Where the brief, the DAG or earlier work was wrong

Validation: the complete revised proof compiled through `lcompile.py` in 25.7
seconds. The profiling run emitted only the development-profiler warning; that
option has been removed for delivery. A proved private helper isolates the
coefficient-comparison projection so the main proof does not repeatedly check
its identity-square construction. This reduced the previous 49.9-second run
and avoids the intermittent timeout seen during delivery. Final compilation,
axiom and packet checks are performed by the delivery tool.

No false statement was found. The original quotient-cone route is mathematically
valid but requires more coefficient-model transport than the available coinduction
route. The implementation uses the latter and documents the change in the node.

The replacement generic interfaces are existing proved tools: exact derived
coproduct preservation, coefficient-forgetting colimits, degreewise-injective
resolutions, injective abelian-sheaf divisibility, and exact sheafification. They
serve only this internal kernel construction; they do not replace any step of the
proper-base-change unit. No additional tool approval was inserted in the node.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
