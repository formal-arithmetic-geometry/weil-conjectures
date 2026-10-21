# PicardDerivedUnitNormalizationComposition restoration

## Reason

Restore the assigned module from the archive named in coord/rework.tsv. The module
was removed after the upstream synchronization and a failed cluster restore. Its
archived source contains zero sorry holes. The adopted source comparison now
explicitly uses AlgebraicGeometry.derivedPullback. In the private helper inside
Scheme.Modules, the unqualified name instead resolves to the newer
Scheme.Modules.derivedPullback, whose standard derived category has a different
Hom universe. The compiler reports Quiver.Hom.{v, v + 1} where the canonical
comparison has Quiver.Hom.{v + 1, v + 1}.

Qualify the intended functor in that private helper. This preserves the shared
HasDerivedCategory family, both public signatures, the actual composite defining
picardDerivedUnitNormalization, and the full composition statement. The restored
proof still uses the ordinary unit composition calculation, naturality of the
canonical comparison, and canonicalSinglePullbackComposition. The named
normalization is still constructed from the actual canonical comparison and
ordinary structure-sheaf isomorphism. No target or definition changes meaning.

The private-helper namespace also marks tensorPullback and
Adjunction.leftAdjointUniq locally irreducible. This reduces needless unfolding
of the large chosen constructions while checking naturality. These annotations
end with the private-helper namespace and export no attributes or notation.
The full restored file already compiled without them in 57.7 seconds; the
helper-only check fell from 51.3 to 39.9 seconds with them. The final complete
module compiles cleanly in 32.9 seconds with the annotations.

## Old

There is no live file at the assigned path. The rework archive is
quarantine/Sheaf/AlgebraicGeometry/PicardDerivedUnitNormalizationComposition.lean.
Its failing private helper signature is:

```lean
private theorem singlePullback_naturality
    {X Y : Scheme.{v}} (f : X ⟶ Y) {M N : Y.Modules} (a : M ⟶ N) :
    (derivedPullback f).map ((DerivedCategory.singleFunctor _ 0).map a) ≫
      canonicalSinglePullbackMap f N =
    canonicalSinglePullbackMap f M ≫
      (DerivedCategory.singleFunctor _ 0).map ((pullback f).map a)
```

## New

The archive is restored at its original Lean path. The helper instead reads:

```lean
private theorem singlePullback_naturality
    {X Y : Scheme.{v}} (f : X ⟶ Y) {M N : Y.Modules} (a : M ⟶ N) :
    (AlgebraicGeometry.derivedPullback f).map ((DerivedCategory.singleFunctor _ 0).map a) ≫
      canonicalSinglePullbackMap f N =
    canonicalSinglePullbackMap f M ≫
      (DerivedCategory.singleFunctor _ 0).map ((pullback f).map a)
```

## Users

The read-only downstream.py check reports the module as unknown while it is
quarantined. Searching both lean/ and quarantine/ finds exactly two direct
importers. Scanning every DAG statement dependency, proof dependency, and proof
step use finds these same two external parents. Both are quarantined. Their
source uses the identical public normalization and composition theorem; the
factorization parent unfolds the unchanged normalization body. No adaptation is
forced. The existing node attachments, dependency lists and unit route remain.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardDerivedUnitNormalizationComposition | J1 | Restore the archived implementation and repair private functor name resolution. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeFactorization | unclaimed | Quarantined direct importer and definition-node parent; identical public definition and body, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposePasting | unclaimed | Quarantined direct importer and theorem-node parent; identical public theorem, no adaptation. |

The source-library tree is not edited. Restoring the item does not withdraw any
quarantined consumer, its attachment, or its proof obligation.

## Status

landed 20261021T011022-L-2029074 2026-10-21 (merge of deliver/J1/Sheaf.AlgebraicGeometry.PicardDerivedUnitNormalizationComposition)
