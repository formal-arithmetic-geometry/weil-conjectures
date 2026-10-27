## What changed

Proved the normalized closed/open immersion projection theorem without changing its
statement or any public definition. The proof uses native constant-coefficient module
sheaves throughout. Private helpers transport tensor comparisons along the exact versus
left-derived normalization, establish support detection for the named closed transpose,
and paste the closed mate square with the forward open projection square.
A local priority for the direct sheafification monoidality instance avoids an indirect
instance-search route; local irreducibility attributes keep tensor and projection
rewrites from expanding their constructions.

Updated the existing node's proof and proof dependencies to match this route. No new
public declarations or modules, no definition changes, and no source-library edits.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ImmersionProjectionComparison.immersion_projection_site_comparison`
(blueprint `lem-sf-immersion-projection-site-comparison`). The complete module compiled
cleanly through `lcompile.py` in 46.2 seconds (after an earlier 47.4-second pass).
A focused copy including the delivery's unchanged axiom probe subsequently passed in
50.3 seconds, reporting `SHEAF-PROBED 49` and no forbidden axioms or direct sorries.
Two earlier delivery attempts timed out under the 60-second combined check.
Elaboration of the public definitions now respects transparency before the proof
restores its original elaboration settings. Focused checks also verified exact
tensor normalization, closed support detection, both open comparison squares,
naturality, flat-stalk boundedness, and final open/closed pasting.

Holes added: 0. Holes split off: 0. Sorries left in the delivery: 0. No new public
statements, no axioms, and no changes to the statement or public definitions.

## No longer needed

Removed these proof-only imports from this module:

- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.Algebra.Homology.RingedFlatSingleTensorCohomology`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Sheaf.Algebra.Homology.RingedDerivedTensorNative`
- `Sheaf.SixFunctors.EtaleClosedTensorProjection`
- `Sheaf.SixFunctors.ProEtaleClosedTensorProjection`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`

The closed projection existence lemmas are unnecessary: the closed unit is invertible
on the tensor because its open-complement restriction vanishes, and its closed
restriction is invertible by the triangle identity. Native tensor comparison avoids
the ringed/native representative bridge and the ringed monoidal comparison statements.
The library's flat-stalk criterion and native Tor-amplitude bound avoid the ringed
flat-single cohomology statement. These removals concern this item's proof only;
no module is withdrawn and no adopted source declaration is removed.

Removed proof dependencies:
`lem-weil-etale-closed-tensor-projection`,
`lem-weil-proetale-closed-tensor-projection`,
`lem-sf-ringed-derived-native-tensor`,
`lem-sfb-ringed-derived-monoidal-comparisons`,
`lem-fd-ringed-flat-single-tensor-cohomology`,
`lem-pod-etale-stalk-tensor-scalar`,
`lem-sf-comparison-pullback-exact`,
`prop-weil-pbc-inverse-image-modules-exact`, and
`prop-weil-pbc-proetale-constant-exact`.
The statement dependencies and original public imports are retained.
The obsolete top-level `tool_uses` approvals for those nine removed proof
dependencies were removed; the remaining approvals retain their original order.

## Where the brief, the DAG or earlier work was wrong

The planned ringed-sheaf declarations do not directly describe the module's native
ModuleCat tensor presentation. Their underlying arguments apply, but the existing
native tensor, exact-functor and projection-mate APIs give a direct proof and remove
those extra bridges. The original mathematical statement and unit route are preserved.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
