# WeilConjectures.CompactSupportFiniteProjection.fixedDerivedPull

## Reason

Withdrawn by the reviewer (2026-10-26). The delivery restated the body of `fixedDerivedPull`
in the unclaimed module `Sheaf.Paper.ConstructibleProjectionMates` through a local
coefficient-generic function. The item `Sheaf.Paper.ProjectionFormulaCoherence`, including
the proof of `sixFunctorProjection_reduction_finite`, compiles against the published,
unchanged module (about 44 s). The adaptation is therefore not needed. Under brief point 2b,
an unneeded change to a shared definition is reverted. The module is restored byte for byte
to its published version.

## Old

Unchanged published definition:

```lean
def fixedDerivedPull {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    DerivedCategory (Sheaf (ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) ⥤
    DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) :=
  (AlgebraicGeometry.ProEtale.upperStar
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
    f.hom.left).leftDerivedFunctor
```

## New

Identical to Old: no change remains.

## Users

None affected: no declaration of Sheaf.Paper.ConstructibleProjectionMates changes.

## Status

landed 20261026T071400-L-3922877 2026-10-26 (merge of deliver/V5/Sheaf.Paper.ProjectionFormulaCoherence)
