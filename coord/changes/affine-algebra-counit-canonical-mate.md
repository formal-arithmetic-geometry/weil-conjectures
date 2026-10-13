# AlgebraicGeometry.affine_algebra_kinjective_counit_compatibility

## Reason

STATEMENT-DISPUTED: the previous statement asserted compatibility for every
isomorphism e, with no condition selecting the canonical comparison. Take the
identity on Spec(Q), its identity module adjunction, and a rank-one Q-module
complex concentrated in degree zero (injective and K-injective). For the
canonical identification the counit acts as identity; choosing its negative
negates the displayed composite. Identity is not minus identity over Q.
Thus the statement was false, rather than simply difficult to prove.

Construct the canonical morphism as the mate of homology of the termwise
counit after the inverse exact-functor comparison. Prove compatibility by the
adjunction bijection and isomorphism cancellation. Separate invertibility of
that specific map, which is the affine chart calculation of Stacks Tags 0AVW
and 08D4, from the formal identity. No target statement or definition changes.
The added definition constructs a fixed morphism from the existing maps,
without choosing data from an existence theorem. asIso uses invertibility of
that fixed morphism, which determines the inverse uniquely.

## Old

```lean
theorem affine_algebra_kinjective_counit_compatibility
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    [P.Additive] [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ)
    (e : (((RingedSpace.moduleDirectImage
          (toDirectImageAlgebraSpace f)).mapHomologicalComplex (.up ℤ)).obj I).homology n ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj (I.homology n)) :
      HomologicalComplex.homologyMap ((a.mapHomologicalComplex (.up ℤ)).counit.app I) n =
        (P.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app
            (((RingedSpace.moduleDirectImage
              (toDirectImageAlgebraSpace f)).mapHomologicalComplex (.up ℤ)).obj I) ≫
          P.map e.hom ≫ a.counit.app (I.homology n)
```

## New

```lean
theorem affine_algebra_kinjective_counit_compatibility
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    [P.Additive] [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    (n : ℤ) :
    HomologicalComplex.homologyMap ((a.mapHomologicalComplex (.up ℤ)).counit.app I) n =
      (P.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app
        (((RingedSpace.moduleDirectImage
          (toDirectImageAlgebraSpace f)).mapHomologicalComplex (.up ℤ)).obj I) ≫
        P.map (affineAlgebraCounitHomologyComparison f P a I n) ≫
          a.counit.app (I.homology n)
```

The new public definition affineAlgebraCounitHomologyComparison is the image
under a.homEquiv of the inverse exact comparison composed with homology of
the termwise counit. Its complete signature and implementation are in the
item's module and def-sc-affine-algebra-counit-homology-comparison.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveCounitCompatibility | G1 | Canonical-map definition and proved compatibility replace the false arbitrary-isomorphism assertion. |
| Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveCounitHomologyFactorization | unclaimed | Forced adaptation: its existing signature and visibility remain identical; select asIso of the canonical map instead of an unconstrained existential witness. |
| Sheaf.AlgebraicGeometry.AffineAlgebraCounitHomologyComparisonIsIso | new G1 module | Uses the explicit fixed-map definition to state its geometric invertibility; no pre-existing signature to adapt. |

The downstream search found 317 transitive importers; only the factorization
module mentions the changed theorem. The item's unused public cohomology-comparison import is replaced by its two
actual public statement-context imports, DirectImageAlgebraDerivedCategory and
RingedSpaceDerivedDirectImage. The removed re-export is used only by the adapted
factorization, whose original private import already supplied it. A whole-library
search found no other use of that theorem or module. All other importers retain
their existing statements and definitions; no target statement uses the new map
in its signature, and no existing definition is changed. The new comparison adds a name without changing any existing
definition. The new IsIso module is used only by the adapted proof.

The adapted module's original line 67 fails against the changed dependency:
Application type mismatch: hI has type forall n, (I.homology n).IsQuasicoherent
but is expected to have type Int in affine_algebra_kinjective_counit_compatibility.
Replace its proof-only cohomology-comparison import with the fixed-map IsIso
module. Replace the two final proof lines by a local IsIso instance, asIso of
the constructed map, and the proved canonical compatibility. Each replacement
is required to produce the existential isomorphism and its compatibility
without applying the false statement. No other line of the factorization module is adapted.

## Status

landed 20261013T040746-L-3948359 2026-10-13 (merge of deliver/G1/Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveCounitCompatibility)
