## What changed

Proved `AlgebraicGeometry.Etale.openImmersion_restriction_leray` in
`Sheaf.AlgebraicGeometry.OpenImmersionRestriction`, keeping its full original statement.
The counit is invertible because the direct image is fully faithful. The unbounded Leray
map is already a component of a natural isomorphism in the source library.

The final equality is proved by two fully proved private helpers. The first extracts
compatibility with units from `rightDerivedFunctorPlusCompatibility`. The second proves
that this compatibility commutes with the canonical composition isomorphisms. Precomposing
with the bounded composition isomorphism reduces the equality to the universal property
`Functor.rightDerived_ext`; the two unit factorization identities and naturality make
both sides the homotopy image of the same underived comparison followed by the unbounded
unit. Specializing to direct image and global sections gives exactly the required square,
including the inverse orientation of the bounded Leray isomorphism.

Updated the theorem's proof explanation and its existing DAG node to this route.
All public imports, existing declaration signatures and definitions are preserved.
No other library module is adapted.

On resumption, repaired two transparency-sensitive proof steps in the retained generic
comparison argument and removed an already-solved final goal. The complete module compiles
through `lcompile.py` in 3.6 seconds with no errors or warnings. Its existing theorem
signature is textually identical to the current source; its DAG changes are confined to
`proof`, `proof_deps`, `proof_origin` and deletion of obsolete `tool_uses` entries.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.openImmersion_restriction_leray`
(node `lem-kun-open-immersion-restriction`).

Holes closed: 1. Holes added: 0. Holes remaining in the delivered module: 0.
No statements are split off. Both private helpers are proved in full.
This reports local holes; pre-existing assumptions of imported library declarations
are not claimed to be eliminated.

## No longer needed

Removed these eleven direct proof imports:

- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.AlgebraicGeometry.RGammaUnboundedBounded`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
- `Mathlib.CategoryTheory.Sites.GlobalSections`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`

The composition, sections and derived-functor APIs are already exposed by the unchanged
public imports. The fully faithful open-immersion pushforward import remains necessary.

The following nodes are no longer direct proof dependencies of this item:

- `prop-weil-pbc-kinjective-resolutions-exist`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-kun-rgamma-unbounded-bounded`
- `def-pc-fibre-product`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `prop-weil-pbc-inverse-image-exact`

The canonical source-library constructions already encapsulate resolutions and the
underived sections isomorphism. This proof uses their universal properties instead of
reconstructing them or comparing individual resolutions. In particular it does not use
the module-coefficient theorem `rGamma_unbounded_bounded` to prove an abelian-coefficient
canonical-map identity. The right-adjoint preservation and exactness results can remain
transitive dependencies of those constructions; they are not asserted globally unused.
The obsolete top-level tool approvals for these removed proof dependencies are withdrawn;
the fully faithful pushforward approval is retained. The bounded Leray node and its
module remain used, preserving the unit route.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned explicit K-injective construction was longer
than necessary: the canonical unbounded Leray isomorphism and both canonical uniqueness
comparisons are already defined. Their unit identities prove the exact bounded/unbounded
compatibility directly. No coefficient bridge, new assumption or statement change is
needed. The generic argument also covers identity functors and zero objects; it makes no
nonemptiness, boundedness beyond the existing D-plus domain, quasi-compactness or
cohomological-dimension assumption.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
