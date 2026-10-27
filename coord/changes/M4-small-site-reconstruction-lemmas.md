# CategoryTheory.AdicSites.reductionCompletionUnit_isIso and smallSiteDirectImageReconstruction

## Reason

The assigned word theorem needs the reduced-unit theorem over the lifted coefficient
ring and the direct-image projection/unit equation on its actual small-site models.
The existing generator lemmas use other coefficient or site presentations. Add explicit
interfaces for those two geometric steps; prove the reduced-unit interface and leave
the strictly smaller direct-image presentation comparison as a named theorem hole.

## Old

Neither of these two declarations or modules existed. All existing public signatures,
definitions, docstrings and public imports are preserved.

## New

```lean
theorem reductionCompletionUnit_isIso (S : Site.{u}) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    IsIso (Functor.whiskerRight (S.unit A I) (S.reduction A I))
```

```lean
theorem smallSiteDirectImageReconstruction
    {V U : Site.{t + 1}} (f : Morphism V U)
    {A : Type t} [CommRing A] (d : AlgebraicGeometry.Scheme.CompleteCoefficientDatum A)
    (K : U.derived (ULift.{t + 1, t} A))
    (hK : U.IsComplete _ (d.ideal.map ULift.ringEquiv.symm.toRingHom) K) :
    let I := d.ideal.map ULift.ringEquiv.symm.toRingHom
    IsIso (f.towerProjection (ULift.{t + 1, t} A) I K) ∧
      (V.unit _ I).app ((f.push _).obj K) ≫
          (V.rlim _).map (f.towerProjection _ I K) =
        (f.push _).map ((U.unit _ I).app K) ≫
          (f.directLimitIso _).hom.app ((U.reduction _ I).obj K)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | M4 | Proof imports the two new geometric interfaces. Existing statements and constructions unchanged. |

These are new declarations and new modules; there are no preexisting consumers to adapt.
No source-library module or target statement is changed.

## Status

landed 20261025T123324-L-1858071 2026-10-25 (merge of deliver/M4/Sheaf.Paper.SfCbcCompactSupportCompositionLimit)
