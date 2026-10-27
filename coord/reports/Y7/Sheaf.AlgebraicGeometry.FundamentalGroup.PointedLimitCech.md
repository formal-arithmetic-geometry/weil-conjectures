## What changed

Completed all five theorem proofs in PointedLimitCech. The existence proof assembles
PointedGaloisLimitGeometry, PointedLimitFiniteSplitting, NormalizedPointedLimitCech,
and ProfiniteSchemeProductComponents. Limit uniqueness identifies the finite-quotient
comparison and constant sections; marked-section uniqueness identifies the existing
UniversalCover deck maps. The component homeomorphism is transported along the scheme
isomorphism. Naturality is proved for arbitrary supplied coordinates by testing each
vertex on finite covers and constant-label sections. A private diagonal argument
shows those sections detect maps into a finite étale cover. Identity and composition
use marked finite-cover uniqueness; the two cocycle proofs use associativity and freeness.

Moved nine existing explicit product/label constructions verbatim into
Sheaf.AlgebraicGeometry.FundamentalGroup.ProfiniteProductMaps and publicly re-exported
them from PointedLimitCech. This breaks the cycle between the assembly and its declared
product comparison dependency. The only change to the unclaimed
ProfiniteSchemeProductComponents is replacing its public import of PointedLimitCech
by ProfiniteProductMaps. No existing mathematical signature or defining term changes.
No WeilConjectures file changes. The two existing DAG records track the actual proof
and the relocated definitions. Change record:
coord/changes/Y7-pointed-cech-product-import-cycle.md.

## Proved and sorry left

Closed all five original holes, in namespace AlgebraicGeometry.Scheme.UniversalCover:

- nonempty_pointedLimitCechCoordinates
- pointedLimitCechCoordinates_natural
- right_torsor_cech_cocycle
- label_only_cocycle
- pointedLimitMap_identity_composition

The complete three-module packet was recompiled successfully through lcompile.py --all:
ProfiniteProductMaps (6.0 seconds), ProfiniteSchemeProductComponents (32.2 seconds),
and PointedLimitCech (48.5 seconds), each below the single-file limit.
Actual holes left in the item: zero. Holes added anywhere: zero. Split off: zero.
The imported existing NormalizedPointedLimitCech.exists_coordinates remains an
unproved named dependency, as intended by stage 3; its existing holes are unchanged.
The two private helpers are fully proved. The new basic module has no sorry.

## No longer needed

Removed eight unused direct private imports from PointedLimitCech:

- Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
- WeilConjectures.AlgebraicGeometry.FundamentalGroup.OpenSubgroups
- WeilConjectures.AlgebraicGeometry.LimitAffineTransition
- WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceDegree
- WeilConjectures.AlgebraicGeometry.LimitFibreProducts
- Sheaf.RingTheory.IndEtaleUniverseTransport
- Sheaf.AlgebraicGeometry.EtaleComparison
- Sheaf.AlgebraicGeometry.FiniteEtaleFiniteLimits

These lower results belong in the geometry and splitting dependencies, rather than
in this assembly. Some remain transitively used by those dependencies; no global
module withdrawal is asserted. Removed lem-galois-aut-profinite from the item's
proof_deps: G is already supplied as a ProfiniteGrp, so the comparison theorem applies
directly. No module is withdrawn. All four substantive stated dependencies are used.
Removed stale direct tool_uses entries thm-galois-fundamental,
cor-galois-open-subgroups, lem-weil-pbc-limit-affine-transition,
lem-weil-pbc-finite-etale-trace-degree, lem-weil-pbc-limit-fibre-products,
det-pe-morphisms-etale-comparison, lem-galois-aut-profinite,
lem-weil-pbc-locally-constant-prime-spectrum, and lem-fet-finite-limits.
Their lower-level work is delegated to the existing proved dependencies.
The direct functoriality source lem-galois-pi1-functoriality is used for
fundamentalGroupMap_smul. No blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The prescribed product comparison imported its parent assembly merely for explicit
product definitions, so the stated proof route initially formed an import cycle.
The verbatim relocation fixes this without weakening any statement or replacing
proved upstream work by holes. The extra automorphism-group profiniteness dependency
was redundant for the Lean interface, which already takes a bundled profinite group.
All theorem statements and all five target statements remain unchanged.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
