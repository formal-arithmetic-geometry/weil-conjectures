# Flat base-change resolution construction module

## Reason

Extract the existing constructions to FlatBaseChangeMapSectionsDefs so the three
new proof modules can refer to them without importing the theorem that imports
those modules. Every declaration has identical name, signature, body and public
visibility. The original module publicly re-exports the construction module.
No target signature or definition is changed and no downstream adaptation is required.

## Old

In Sheaf.AlgebraicGeometry.FlatBaseChangeMapSections:

```lean
/-- Flat pullback preserves finite limits, from the recorded exactness theorem.
Source: Stacks, Tag 02N4 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
instance flatBaseChangePullbackLimits {X Y : Scheme.{uBC}} (g : X ⟶ Y) [Flat g] :
    PreservesFiniteLimits (tensorPullback g) :=
  (flat_module_pullback_exact_pushforward_injective g).1.1

/-- Flat pullback preserves finite colimits, from the recorded exactness theorem.
Source: Stacks, Tag 02N4 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
instance flatBaseChangePullbackColimits {X Y : Scheme.{uBC}} (g : X ⟶ Y) [Flat g] :
    PreservesFiniteColimits (tensorPullback g) :=
  (flat_module_pullback_exact_pushforward_injective g).1.2

/-- Additivity follows from preservation of finite biproducts.
Source: Stacks, Tag 02N4 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
instance flatBaseChangePullbackAdditive {X Y : Scheme.{uBC}} (g : X ⟶ Y) [Flat g] :
    (tensorPullback g).Additive := Functor.additive_of_preserves_binary_products _

/-- The sectionwise comparison of the two composites of direct images in a square.
Source: Stacks, Tag 02N7 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
def flatBaseChangePushforwardSquare {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S) :
    pushforward (pullback.snd g f) ⋙ pushforward f ≅
      pushforward (pullback.fst g f) ⋙ pushforward g :=
  pushforwardComp (pullback.snd g f) f ≪≫
    pushforwardCongr (pullback.condition (f := g) (g := f)).symm ≪≫
      (pushforwardComp (pullback.fst g f) g).symm

/-- Push the augmented lift down along f, and use the sectionwise square comparison.
Source: Stacks, Tag 02N7 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
def flatBaseChangeResolutionQ {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S)
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶
      ((pushforward (pullback.snd g f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) :
    ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶
      ((pushforward g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (((pushforward (pullback.fst g f)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj J.cocomplex) :=
  ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).map t ≫
    (NatIso.mapHomologicalComplex (flatBaseChangePushforwardSquare f g)
      (ComplexShape.up ℕ)).hom.app J.cocomplex

/-- The termwise adjoint c of q, with the canonical tensor-pullback adjunction.
Source: Stacks, Tag 02N7 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
def flatBaseChangeResolutionC {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S) [Flat g]
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶
      ((pushforward (pullback.snd g f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) :=
  ((Classical.choose (exists_tensorPullbackAdjunction g)).mapHomologicalComplex
    (ComplexShape.up ℕ)).homEquiv _ _ |>.symm (flatBaseChangeResolutionQ f g I J t)

/-- H^p(c), with exact pullback's homology comparison and the resolution comparisons.
Source: Stacks, Tag 02N7 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
def flatBaseChangeResolutionBeta {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S) [Flat g]
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶
      ((pushforward (pullback.snd g f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) (p : ℕ) :
    (tensorPullback g).obj (((pushforward f).rightDerived p).obj F) ⟶
      ((pushforward (pullback.fst g f)).rightDerived p).obj
        ((tensorPullback (pullback.snd g f)).obj F) :=
  (tensorPullback g).map (I.isoRightDerivedObj (pushforward f) p).hom ≫
    (((((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).sc p).mapHomologyIso (tensorPullback g)).inv ≫
    (HomologicalComplex.homologyFunctor S'.Modules (ComplexShape.up ℕ) p).map
      (flatBaseChangeResolutionC f g I J t) ≫
    (J.isoRightDerivedObj (pushforward (pullback.fst g f)) p).inv

/-- The canonical class map into R^p f_*F, using the restricted source resolution.
Source: Stacks, Tag 01E4 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
def FlatBaseChangeOpenChoices.sourceClass {X S S' : Scheme.{uBC}}
    {f : X ⟶ S} {g : S' ⟶ S} {F : X.Modules} {I : InjectiveResolution F}
    {J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)} {V : S.Opens}
    (D : FlatBaseChangeOpenChoices f g F I J V) (p : ℕ) :=
  resolutionSectionClass D.source.resolution
    (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
    V D.source.sections p ≫ Hom.app (I.isoRightDerivedObj (pushforward f) p).inv V

/-- The canonical class map into R^p f'_*F', using the restricted target resolution.
Source: Stacks, Tag 01E4 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
def FlatBaseChangeOpenChoices.targetClass {X S S' : Scheme.{uBC}}
    {f : X ⟶ S} {g : S' ⟶ S} {F : X.Modules} {I : InjectiveResolution F}
    {J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)} {V : S.Opens}
    (D : FlatBaseChangeOpenChoices f g F I J V) (p : ℕ) :=
  resolutionSectionClass D.target.resolution
    (((pushforward (pullback.fst g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex) (g ⁻¹ᵁ V) (D.target.sections ≪≫
      eqToIso (congrArg (fun U => ((RingedSpace.openModuleSections
        (Limits.pullback g f).toRingedSpace U).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj J.cocomplex) (flatBaseChangeOpenEquality f g V))) p ≫
    Hom.app (J.isoRightDerivedObj (pushforward (pullback.fst g f)) p).inv (g ⁻¹ᵁ V)

```

## New

The identical declarations above occur verbatim in
Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs, with the same public section.
The original module has `public import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs`.
The data and theorem types seen by downstream modules are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FlatBaseChangeMapSections | R2 | Re-exports all constructions; theorem proved from new proof modules. |

The downstream scan finds no other module mentioning one of the nine moved names.
The second reader reran tools/downstream.py and the textual name search against
the current local snapshot: zero transitive importers and no external users of
the nine moved names. The earlier count of 213 is withdrawn. Future importers
see the identical declarations through the public re-export.
No target review is reopened because every definition body is identical.

## Status

landed 20261012T160142-L-2566203 2026-10-12 (merge of deliver/R2/Sheaf.AlgebraicGeometry.FlatBaseChangeMapSections)
