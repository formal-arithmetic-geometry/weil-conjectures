# SheafOfModules.RingedSliceDerivedImage

## Reason

Move the existing interfaces unchanged into RingedDerivedSliceData, publicly re-exported by the original module, to let independent proof-obligation modules use them without an import cycle. Add the proved generic ofMate construction. All moved signatures, bodies, universes, visibility and mathematical definitions are preserved. The main theorem only renames its existential continuity witness from hc to _hc to satisfy the unused-variable linter; its elaborated type is identical. Target meanings are unchanged; no target statement correction is needed.

## Old

The following declarations were in Sheaf.Paper.RingedDerivedSliceLocalization:

```lean
/-- The recorded derived restriction with its coefficient presentation fixed explicitly.
Source: Stacks Tags 03DJ and 08JB
(blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
def ringedSliceRestriction {E : Type u} [SmallCategory E] {T : GrothendieckTopology E}
    (A : Sheaf T CommRingCat.{u}) (W : E)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj A))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose T (forget₂ CommRingCat RingCat)).obj A).over W))] :
    ringedSiteDerived A ⥤ ringedSiteDerived (A.over W) :=
  CategoryTheory.ringedSliceDerivedRestriction.{u, u, u, w, w} T A W

/-- Restriction of Q of a complex is Q of its actual termwise restriction.
Source: Stacks Tags 03DJ and 08JB
(blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
def ringedSliceRestrictionFactors {E : Type u} [SmallCategory E] {T : GrothendieckTopology E}
    (A : Sheaf T CommRingCat.{u}) (W : E)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj A))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose T (forget₂ CommRingCat RingCat)).obj A).over W))] :
    DerivedCategory.Q.{w} ⋙ ringedSliceRestriction.{u, w} A W ≅
      CategoryTheory.ringedSliceComplexRestriction.{u, u, u} T A W ⋙
        DerivedCategory.Q.{w} (C := SheafOfModules.{u}
          ((sheafCompose (T.over W) (forget₂ CommRingCat RingCat)).obj (A.over W))) :=
  CategoryTheory.ringedSliceLocalizationIso.{u, u, u, w, w} T A W

variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J]
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
  (a : R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S)

/-- The existing module direct image, with a fixed head for instance inference.
Source: Stacks Tag 04J0 (blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
def ringedSliceModulePushforward := pushforward.{u} (ringedSiteModuleMap u a)

/-- The existing module pullback, with a fixed head for instance inference.
Source: Stacks Tag 03D7 (blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
def ringedSliceModulePullback := pullback.{u} (ringedSiteModuleMap u a)

/-- The actual adjunction of these existing functors.
Source: Stacks Tag 03D7 (blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
def ringedSliceModuleAdjunction :
    ringedSliceModulePullback u a ⊣ ringedSliceModulePushforward u a :=
  pullbackPushforwardAdjunction (ringedSiteModuleMap u a)

/-- Direct image is additive because its maps are the original maps on sections.
Source: Stacks Tag 04J0 (blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
instance ringedSlicePushforwardAdditive : (ringedSliceModulePushforward u a).Additive where
  map_add := rfl

/-- The canonical module pullback inherits additivity from its right adjoint.
Source: Stacks Tag 03D7 (blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
instance ringedSlicePullbackAdditive : (ringedSliceModulePullback u a).Additive :=
  (ringedSliceModuleAdjunction u a).left_adjoint_additive

/-- A presentation of the canonical derived adjunction, retaining both universal
transformations and their normalization under the original module adjunction.
This is data to be produced by the theorem, not an extra assumption on the morphism.
Source: Stacks Tags 06YY, 07A6 and 09T5
(blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
structure RingedSliceDerivedImage
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))] where
  left : ringedSiteDerived.{u, w} R ⥤ ringedSiteDerived.{u, w} S
  right : ringedSiteDerived.{u, w} S ⥤ ringedSiteDerived.{u, w} R
  epsilon : DerivedCategory.Q.{w} ⋙ left ⟶
    (ringedSliceModulePullback u a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w}
  eta : (ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ right
  isLeftDerived : left.IsLeftDerivedFunctor epsilon
    (HomologicalComplex.quasiIso _ (.up ℤ))
  isRightDerived : right.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso _ (.up ℤ))
  adjunction : left ⊣ right
  normalized : ∀ (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ)
    (h : ((ringedSliceModulePullback u a).mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    adjunction.homEquiv (DerivedCategory.Q.{w}.obj P) (DerivedCategory.Q.{w}.obj I)
      (epsilon.app P ≫ DerivedCategory.Q.{w}.map h) =
      DerivedCategory.Q.{w}.map
        (((ringedSliceModuleAdjunction u a).mapHomologicalComplex
          (.up ℤ)).homEquiv P I h) ≫ eta.app I

variable [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))]

/-- Ordinary direct image and slice restriction are literally the same complex.
Source: Stacks Tag 04J0 (blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
def ringedSlicePushforwardComplexIso (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    (I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ) :
    (CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj
      (((ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ)).obj I) ≅
    ((ringedSliceModulePushforward (Over.post (X := V) u)
        (localizedRingedSiteMap u a V)).mapHomologicalComplex (.up ℤ)).obj
      ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj I) :=
  Iso.refl _

/-- The image of the unit generator in the localized target coefficient sheaf.
It is pullback of the ring followed by the actual localization unit, in degree zero.
Source: Stacks Tag 099J (blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
def ringedSliceLocalizationGenerator
    (t : (S.obj ⋙ CategoryTheory.forget CommRingCat).sections) :
    ((ringedSliceModulePullback u a).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor _ 0).obj
          (unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))) ⟶
      (CochainComplex.singleFunctor _ 0).obj (ringedSectionLocalization S t) :=
  ((HomologicalComplex.singleMapHomologicalComplex
      (ringedSliceModulePullback u a) (.up ℤ) 0).app _).hom ≫
    (CochainComplex.singleFunctor _ 0).map
      (pullbackObjUnitToUnit (ringedSiteModuleMap u a) ≫ ringedSectionLocalizationUnit S t)

/-- The two natural slice comparisons with their unit and counit coherence equations.
These fields bundle precisely the compatibility clauses of the node, with no further
condition on either adjunction or restriction functor.
Source: Stacks Tags 04J0 and 07A6
(blueprint: lem-weil-pbc-ringed-derived-slice-localization). -/
structure RingedSliceAdjunctionSquare
    {A B C D : Type v} [Category.{x} A] [Category.{x} B]
    [Category.{x} C] [Category.{x} D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (jA : A ⥤ C) (jB : B ⥤ D) where
  /-- Restriction commutes with the right adjoints. -/
  beta : R ⋙ jA ≅ jB ⋙ R'
  /-- Restriction commutes with the left adjoints, in the inverse orientation. -/
  lambda : jA ⋙ L' ≅ L ⋙ jB
  /-- The counit square. -/
  counit : ∀ M : B,
    L'.map (beta.hom.app M) ≫ adj'.counit.app (jB.obj M) =
      lambda.hom.app (R.obj M) ≫ jB.map (adj.counit.app M)
  /-- The unit square. -/
  unit : ∀ N : A,
    jA.map (adj.unit.app N) ≫ beta.hom.app (L.obj N) ≫ R'.map (lambda.inv.app N) =
      adj'.unit.app (jA.obj N)

```

## New

The exact same declarations and bodies are in Sheaf.Paper.RingedDerivedSliceData and are publicly imported by Sheaf.Paper.RingedDerivedSliceLocalization. The additional ofMate definition derives both coherence equations from Mathlib's mate identities; it contains no holes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.RingedDerivedSliceLocalization | Q7 | Imports and re-exports the extracted interfaces; completes its assembly proof. |

The current downstream tool reports 932 transitive importers, but its declaration-use
check for RingedSliceDerivedImage finds only the original module. An rg search for every
moved declaration likewise finds no external user. All importer-visible signatures and
bodies are preserved by the public import, so those modules need no adaptations.
No other group's module is edited.

## Status

landed 20261019T192821-L-1871607 2026-10-19 (merge of deliver/Q7/Sheaf.Paper.RingedDerivedSliceLocalization)
