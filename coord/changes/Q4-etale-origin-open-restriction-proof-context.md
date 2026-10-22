# AlgebraicGeometry.Scheme.etaleOriginOpenRestriction_transport

## Reason

Stage-3 preflight requests a change record for the added proof-context commands in
`Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport`. The private proof uses
local irreducibility attributes to keep derived constructions behind their proved
APIs, a private section for its helpers, and one declaration-scoped adjunction
namespace opening. These commands support the completed proof and prevent costly
unfolding; they do not change the mathematical interface.

All six existing public comparison definitions retain their names, signatures and
bodies verbatim. The target signature and all public imports are unchanged. All new
helpers and the proposition structure are private and proved; there are no new
public declarations, global instances, simp rules or notation. Every added attribute
is explicitly local. No adopted source-library file or consumer is edited. No
statement becomes weaker, stronger or different, and no target review is reopened.

The complete module passed the server-only compilation check in 42.6 seconds. A
private structure generic over the coefficient category and its class instances
keeps the ordinary cube equation stable under specialization, avoiding the kernel's
repeated comparison of nested proof-instance arguments. This is an implementation
choice, with no change to any comparison map.

## Old

The original target signature, verbatim:

```lean
theorem etaleOriginOpenRestriction_transport {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsOpenImmersion i]
    [QuasiCompact p] [QuasiSeparated p]
    [QuasiCompact (pullback.snd p i)] [QuasiSeparated (pullback.snd p i)]
    (K : DerivedCategory.Plus
      (Sheaf (pullback p i).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (lam :
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).mapDerivedCategory.obj
              K.obj)) ≅
      (Etale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.snd p i)).rightDerivedFunctor.obj
          K.obj)
    (hlam : lam.hom =
      (Etale.exactDerivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (IsPullback.of_hasPullback p i).toCommSq).app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).mapDerivedCategory.obj
              K.obj) ≫
        (Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.snd p i)).rightDerivedFunctor.map
            (inv ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).unit.app K.obj))) :
    (etaleOriginOpenComparison A W).map lam.inv ≫
        (etaleOriginOpenRestrictionMate A i).app _ ≫
          (sfIntrinsicDerivedPullback A i).map (etaleOriginOpenTargetComparison A p i K).hom =
      (etaleOriginOpenDirectImageComparison A (pullback.snd p i) K).hom ≫
        (proEtaleOpenRestrictionLambdaInverse p i A).app
          ((etaleOriginOpenComparison A (pullback p i)).obj K.obj)
```

The original file used `set_option autoImplicit false`, the existing universe and
namespace openings, and this local attribute block:

```lean
attribute [local irreducible] etaleOriginOpenComparison etaleOriginOpenCoordinates
  etaleOriginOpenExtensionComparison etaleOriginOpenDirectImageComparison
  sfIntrinsicDerivedEquivalence sfIntrinsicModuleEquivalence sfIntrinsicExtensionByZero
  sfIntrinsicPullback exceptionalOpenAdjunction
  Etale.lowerStar Etale.upperStar Etale.openImmersionLowerShriek
```

## New

The target signature remains verbatim:

```lean
theorem etaleOriginOpenRestriction_transport {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsOpenImmersion i]
    [QuasiCompact p] [QuasiSeparated p]
    [QuasiCompact (pullback.snd p i)] [QuasiSeparated (pullback.snd p i)]
    (K : DerivedCategory.Plus
      (Sheaf (pullback p i).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (lam :
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).mapDerivedCategory.obj
              K.obj)) ≅
      (Etale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.snd p i)).rightDerivedFunctor.obj
          K.obj)
    (hlam : lam.hom =
      (Etale.exactDerivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (IsPullback.of_hasPullback p i).toCommSq).app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).mapDerivedCategory.obj
              K.obj) ≫
        (Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.snd p i)).rightDerivedFunctor.map
            (inv ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).unit.app K.obj))) :
    (etaleOriginOpenComparison A W).map lam.inv ≫
        (etaleOriginOpenRestrictionMate A i).app _ ≫
          (sfIntrinsicDerivedPullback A i).map (etaleOriginOpenTargetComparison A p i K).hom =
      (etaleOriginOpenDirectImageComparison A (pullback.snd p i) K).hom ≫
        (proEtaleOpenRestrictionLambdaInverse p i A).app
          ((etaleOriginOpenComparison A (pullback p i)).obj K.obj)
```

The file uses the following elaboration and linter options:

```lean
set_option autoImplicit false
set_option maxErrors 1
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
```

The original universe, `open CategoryTheory CategoryTheory.Limits
CategoryTheory.Functor`, namespace and section variables are unchanged. The new
private development is scoped by `section DerivedCoordinates` and its matching
`end DerivedCoordinates`, before the original restriction-mate definition. The
single additional namespace opening is declaration-scoped:

```lean
open CategoryTheory.Adjunction in
private lemma exact_unit_square_Qh
```

The local attribute commands are:

```lean
attribute [local irreducible] derivedCoordinates
attribute [local irreducible] sfIntrinsicModuleEquivalence
  sfIntrinsicDirectImageComparison sfIntrinsicDerivedDirectImageComparison
  sfProperOpenFixedRestrictionIso
attribute [local irreducible] sfProperOpenDerivedRestriction
attribute [local irreducible] Etale.upperStar Etale.lowerStar
  ProEtale.upperStar ProEtale.lowerStar ProEtale.comparisonUpperStar
  ProEtale.comparisonUpperStarCompUpperStarIso
  Etale.squareUpperStarIso ProEtale.upperStarCompIso
  presheafToSheaf Functor.sheafPullbackConstruction.sheafPullback
  Etale.upperStarLowerStarAdjunction ProEtale.upperStarLowerStarAdjunction
attribute [local irreducible] etaleOriginOpenCoordinates
  etaleOriginOpenExtensionComparison etaleOriginOpenDirectImageComparison
  sfIntrinsicModuleEquivalence sfIntrinsicExtensionByZero
  sfIntrinsicPullback exceptionalOpenAdjunction
  Etale.lowerStar Etale.upperStar Etale.openImmersionLowerShriek
```

All but the last command occur inside `DerivedCoordinates`. The last is local to
this module and controls elaboration of the unchanged public comparison definitions
and the new proof. No attribute is exported to an importing module.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport
--uses AlgebraicGeometry.Scheme.etaleOriginOpenRestriction_transport` lists the four
transitive consumers below. Its textual search finds the theorem only in the item
and the direct consumer `EtaleOriginProperOpenInterchange`. Their statements and
constructions use the unchanged public definitions and theorem signature, so no
consumer adaptation is required. Claim holders are from the current shared checkout.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | Q4 | Sole proof hole closed; public interface unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Direct theorem user; signature and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Unchanged interface; no adaptation. |

## Status

landed 20261022T020113-L-27828 2026-10-22 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport)
