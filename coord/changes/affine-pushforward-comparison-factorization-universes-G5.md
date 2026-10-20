# AlgebraicGeometry.affinePushforwardComparison_factorization

## Reason

Restore the quarantined module by consolidating its duplicate theorem with the adopted
upstream theorem of the same name. The original fails with `u + 1 =?= u` because its
implicit `SheafOfModules` universes no longer agree with the affine comparison coordinates.
The adopted upstream theorem already supplies exactly the intended statement, uses
`SheafOfModules.{u}`, and has a complete naturality proof. A version retaining the local
proof with explicit universes compiled in 49 seconds but exceeded 60 seconds with the
required delivery probe. Reusing the existing upstream theorem removes that duplicate
proof and the need to unfold its large comparison composite in this module.

The restored module publicly re-exports the upstream theorem. Its consumer retains its
existing import path and theorem application. No adopted source declaration is changed.
The DAG now records the upstream theorem as its Lean declaration; its two-step proof and
its dependency on the comparison-coordinate definitions are retained.

For the landing-conflict return at head `d9e7e9592c`, rechecked the current sources:
the original remains quarantined and the canonical upstream provider is unchanged.
The restored module now also includes `@[expose] public section`, as required by the
module-header convention. Fresh server compilation of the re-export and the scratch
consumer passes, and the upstream theorem again reports only the three allowed axioms.
The delivery tool rebuilds this repair on the current `sheaf-dag` base.

## Old

The quarantined module directly imports the upstream comparison coordinates and declares
its private `cancelComparison` helper and the following theorem:

```lean
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules (moduleRings Y.toRingedSpace))]

theorem affinePushforwardComparison_factorization
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (σ : ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B ≅
      affinePushforwardTilde A ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ)))
    [(affinePushforwardTilde A ⋙ RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesZeroMorphisms]
    [(affinePushforwardTilde A ⋙ RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesHomology]
    (C : CochainComplex (ModuleCat A) ℤ) :
    affinePushforwardCohomologyMapOfComparison A B φ σ C i =
      σ.hom.app (C.homology i) ≫
        ((C.sc i).mapHomologyIso
          (affinePushforwardTilde A ⋙ RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)).inv ≫
        ((DerivedCategory.homologyFunctorFactors
          (SheafOfModules (moduleRings (Spec (.of B)).toRingedSpace)) i).app
          (((affinePushforwardTilde A ⋙ RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).mapHomologicalComplex
              (.up ℤ)).obj C)).inv ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          ((RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj
              (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C)))
```

## New

The restored module contains this public import instead of duplicate declarations,
followed by its module docstring and `@[expose] public section`:

```lean
public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonFactorization
```

The theorem provided by that import has this existing upstream signature:

```lean
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

theorem affinePushforwardComparison_factorization
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (σ : ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B ≅
      affinePushforwardTilde A ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ)))
    [(affinePushforwardTilde A ⋙ RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesZeroMorphisms]
    [(affinePushforwardTilde A ⋙ RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesHomology]
    (C : CochainComplex (ModuleCat A) ℤ) :
    affinePushforwardCohomologyMapOfComparison A B φ σ C i =
      σ.hom.app (C.homology i) ≫
        ((C.sc i).mapHomologyIso
          (affinePushforwardTilde A ⋙ RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)).inv ≫
        ((DerivedCategory.homologyFunctorFactors
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).app
          (((affinePushforwardTilde A ⋙ RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).mapHomologicalComplex
              (.up ℤ)).obj C)).inv ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          ((RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj
              (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C)))
```

The mathematical hypotheses and conclusion keep their intended meaning; the sheaf universe
is explicitly the one used by the coordinate definitions. No definition or target changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffinePushforwardComparisonFactorization | G5 | Restore the module as a public re-export of its proved upstream theorem. |
| Sheaf.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity | unclaimed | Quarantined direct consumer; same theorem name and application. Its own implicit sheaf universes require its separate repair. |
| WeilConjectures.Algebra.Homology.AffinePushforwardComparisonFactorization | unclaimed | Existing canonical provider, read only; no source change. |

The active and quarantined source trees have only the direct consumer listed above.
There are no active importers because that consumer is quarantined; `tools/downstream.py`
reports the assigned module as unknown for the same reason. Its original text independently
fails at line 19 with the same universe mismatch. A scratch version making only its own
sheaf universes explicit checks the original consumer proof and theorem application
against the final re-export in 49.4 seconds. The restored module compiles in 4.0 seconds.
A direct axiom check of the reused upstream theorem lists only `propext`, `Classical.choice`,
and `Quot.sound`; the import-direction check confirms that the new import creates no cycle.
The adopted upstream consumer already imports the canonical upstream theorem and is
unaffected. This packet does not restore or modify the quarantined consumer.

## Status

landed 20261020T153008-L-2861292 2026-10-20 (merge of deliver/G5/Sheaf.Algebra.Homology.AffinePushforwardComparisonFactorization)
