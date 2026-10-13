# flatBaseChangeResolutionBeta_openMap_sections

## Reason

The main proof needs controlled unfolding of the section-class maps and the open-map
construction. Without that control, repeated definitional comparisons exceed the
single-file compiler budget. The delivery adds file-local irreducibility attributes
and elaboration settings. The preflight classifies changed command blocks conservatively
as an interface change and requires this record. No existing declaration signature,
visibility, or definition body changes; all irreducibility registrations are `local`
and remain scoped to this file. The two new private helper declarations are fully proved.

## Old

Original proof configuration:
```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives
```
Existing public statement:
```lean
theorem flatBaseChangeResolutionBeta_openMap_sections {X S S' : Scheme.{uBC}}
    (f : X ⟶ S) (g : S' ⟶ S)
    [Flat g] [Flat (pullback.snd g f)] {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (p : ℕ) :
    ∀ (V : S.Opens)
        (D : FlatBaseChangeOpenChoices f g F I J V)
        (xi : (forget₂ _ AddCommGrpCat.{uBC}).obj
          ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
            ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F))),
        Hom.app ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _
          (flatBaseChangeResolutionBeta f g I J t p)) V
          (D.sourceClass p xi) =
        D.targetClass p
          (flatBaseChangeResolutionOpenMap f g I J t p V D xi)
```

## New

Proof configuration:
```lean
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives
attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackMap
attribute [local irreducible] sectionCohomologyTheta flatBaseChangeResolutionBeta
attribute [local irreducible] flatBaseChangeResolutionOpenMap
attribute [local irreducible] FlatBaseChangeOpenChoices.sourceClass
attribute [local irreducible] FlatBaseChangeOpenChoices.targetClass
set_option maxHeartbeats 160000 in
```
The existing public statement is identical:
```lean
theorem flatBaseChangeResolutionBeta_openMap_sections {X S S' : Scheme.{uBC}}
    (f : X ⟶ S) (g : S' ⟶ S)
    [Flat g] [Flat (pullback.snd g f)] {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (p : ℕ) :
    ∀ (V : S.Opens)
        (D : FlatBaseChangeOpenChoices f g F I J V)
        (xi : (forget₂ _ AddCommGrpCat.{uBC}).obj
          ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
            ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F))),
        Hom.app ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _
          (flatBaseChangeResolutionBeta f g I J t p)) V
          (D.sourceClass p xi) =
        D.targetClass p
          (flatBaseChangeResolutionOpenMap f g I J t p V D xi)
```
Its proof now combines the raw section-mate identity with adjunction transport and
cancellation of the resolution comparisons. The raw identity is stated in a new module
with its own node and remains the sole named `sorry` added by this delivery.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FlatPullbackHomologySections
--uses flatBaseChangeResolutionBeta_openMap_sections` lists the item's own declaration
and one external module that directly uses it. The 319 transitive importers retain the
same public signature and definition interfaces; local attributes are not exported.
No module is adapted or requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FlatPullbackHomologySections | G4 | Its statement is unchanged; its proof is reduced. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionSections | unclaimed | Its existing application uses the identical public statement; no edit needed. |

## Status

landed 20261013T141527-L-379131 2026-10-13 (merge of deliver/G4/Sheaf.AlgebraicGeometry.FlatPullbackHomologySections)
