## What changed

Replaced the sole original hole in `AlgebraicGeometry.ProEtale.dualizingClosedSite` by
an assembly of ordinary finiteness, site Tor preservation, invertibility of the actual
coefficient mate, identity-open direct-image normalization, and an explicit computation
of the specified exceptional counit. All original public definitions and signatures
are unchanged. The retained origin is explicitly `(I H, asIso alpha)`.

Added `Sheaf.Paper.ClosedDualizingEtaleFiniteness` for steps 1--3 of the old node,
and `Sheaf.Paper.CompactSupportComparisonNormalization` for the agreement of the
canonical comparison used by the statement with the fixed comparison used by the
specified Hom chain. Neither intermediate contains the full site-transport conclusion.
No definitions choose data from mere existence and no source-library declarations change.
All three delivered Lean modules compile together through lcompile.py --all, with
no errors or warnings.

The direct-image clause is obtained from the existing identity-open normalization at
the zero input; its direct-image assertion is independent of that input. Tor transport
uses the existing generic upstream theorem on fixed module categories, avoiding a
change to intrinsic coefficient presentations. The counit calculation uses the actual
Hom equivalence, unit naturality and beta(counit)=identity, so it needs no separate
unbounded pro-etale adjunction.

## Proved and sorry left

Original hole closed by reduction:
`AlgebraicGeometry.ProEtale.dualizingClosedSite`
(node `lem-coef-dualizing-closed-site`). The assembly has no sorry, and all four
private helpers are proved.

Also proved:
`AlgebraicGeometry.ProEtale.compactSupportComparisonNormalization`
(node `lem-coef-compact-support-comparison-normalization`), by exact open-factor
compatibility and naturality of the proper inclusion comparison.

Holes added:
- `AlgebraicGeometry.ProEtale.closedDualizingEtaleFiniteness`
  (node `lem-coef-closed-dualizing-etale-finiteness`): ordinary four-object finiteness.

This is a decomposition: one original hole closed, one smaller hole added, net 0.
The sole remaining statement has a complete natural-language proof and its own module
and node. The normalization theorem is fully proved. Edge cases checked: empty source, r=0, m=n, and positive level m=1.
The finiteness proof does not assume finite Tor dimension of B over A. The proved comparison
normalization works for arbitrary compactifications and has no nonemptiness hypothesis.

## No longer needed

Removed private proof imports:
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`
- `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport`
- `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`

The parent proof no longer directly needs nodes `lem-coef-dualizing-construction`,
`lem-coef-dualizing-affine-space`, `lem-amb-etale-compact-comparisons`,
`lem-etale-upper-shriek-quasicompact-bounded-below`, `lem-exc-closed-ambient` or
`lem-weil-pbc-closed-immersion-proper`: their ordinary geometric argument is retained
in the new finiteness node, so these are not globally withdrawn.

`lem-coef-site-closed-counit-transport` is replaced by the explicit computation of the
specified Hom chain. Its stated coefficient universe and its ComparisonClassAdjunction
interface do not directly specialize to the ULift-valued specified witness here.
`lem-sf-comparison-tor-amplitude` remains as a mathematical dependency, realized by its
already proved upstream generic fixed-coefficient Tor-preservation theorem rather than
the intrinsic coefficient wrapper.

The coefficient-mate isomorphism is already proved in WitnessCompatibility, so the
parent no longer directly needs `lem-pc-kflat-resolution`,
`lem-sf-comparison-pullback-exact`, `lem-pur-derived-change-of-rings` or
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. Their theory may still be used by
that existing implementation. Removed the obsolete parent top-level tool approvals for
`lem-amb-etale-compact-comparisons`,
`lem-etale-upper-shriek-quasicompact-bounded-below`, `lem-exc-closed-ambient`,
`lem-pc-kflat-resolution`, `lem-pur-derived-change-of-rings`,
`lem-sf-comparison-pullback-exact`, `lem-weil-pbc-closed-immersion-proper`, and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. The geometric prerequisites
remain in the new finiteness node. No module is withdrawn and no global pruning
is claimed.

## Where the brief, the DAG or earlier work was wrong

The source of `SiteClosedCounitTransport` uses E in Type (u+1) and an abstract class
adjunction. It cannot be applied literally to the Type u coefficient extension and the
specified-origin Hom equivalence in this item. The direct calculation supplies that
step without a signature change. The two compact-support comparisons are separately
defined: their equality requires an explicit normalization obligation.

The ordinary finiteness argument also needs glue between the chosen structural
adjunction, the specified closed compactification and the fixed scalar extension.
This glue is recorded in the new ordinary finiteness node rather than assumed by
unfolding chosen adjoints. The blueprint unit route is preserved; its unit record has
no realized nodes for individual steps to bypass.

## New nodes

`lem-coef-closed-dualizing-etale-finiteness` states only the four ordinary etale
finiteness assertions, before any site transport, coefficient-comparison invertibility,
retained origin, direct-image equality or counit equation. It is the original plan's
steps 1--3 with their existing dependencies.

`lem-coef-compact-support-comparison-normalization` states equality of the two existing
natural isomorphisms for a finite ring and compactification. Its proof compares the
same exact open factor and specified proper counit mate through D+ inclusion.
Both nodes inherit the item's chapter/unit and cite the current blueprint source;
searches found generic adjunction tools but no duplicate site-specific assertion.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
