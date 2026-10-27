# SheafOfModules.ToposOpenScalar section definitions

## Reason

The derived-from-ordinary theorem needs the same section definitions as the parent theorem.
Move their unchanged declarations to a foundation module to avoid a circular import.
The original module publicly imports that module. This is dependency factoring, not a
change to any object, statement, universe, visibility, or normalization.

## Old

The following block was declared in `Sheaf.CategoryTheory.ToposOpenScalarUnit`:

```lean
def sliceMap {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J (Type u)) {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    presentationElementRing R A ⟶ presentationElementRing S A :=
  ObjectProperty.homMk (Functor.whiskerLeft (elementProjection A).op a.hom)

/-- The recorded restriction, with its definitionally equal commutative-ring endpoint exposed.
Source: Stacks 04IE (blueprint: lem-pur-topos-open-scalar-unit). -/
abbrev restriction {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :
    ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients
        (elementTopology A) (presentationElementRing R A)) :=
  elementModulePullback.{u, u} (derivedChangeRingIndependentCoefficients J R) A

/-- The recorded sheafified extension, with the same normalized ring endpoint.
Source: Stacks 04IE (blueprint: lem-pur-topos-open-scalar-unit). -/
abbrev extension {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :
    ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients
        (elementTopology A) (presentationElementRing R A)) ⥤
      ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R) :=
  elementModuleExtension.{u} (derivedChangeRingIndependentCoefficients J R) A

/-- The actual extension/restriction adjunction of the element-site construction.
Source: Stacks 04IE (blueprint: lem-pur-topos-open-scalar-unit). -/
abbrev adjunction {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :=
  SheafOfModules.pullbackPushforwardAdjunction.{u, u, u, u, u, u}
    (R := derivedChangeRingIndependentCoefficients J R)
    (S := elementRing (derivedChangeRingIndependentCoefficients J R) A)
    (F := elementProjection A)
    (𝟙 (elementRing (derivedChangeRingIndependentCoefficients J R) A))

/-- The same fixed adjunction, with the ringed-site endpoints explicitly normalized.
Source: Stacks 04IE (blueprint: lem-pur-topos-open-scalar-unit). -/
def normalizedAdjunction {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :
    extension R A ⊣ restriction R A := adjunction R A

/-- A pure tensor in the sheafified scalar extension, transported by its prescribed object
identification. The scalar is written first because Mathlib uses the left S-action.
Source: Stacks 03EK (blueprint: lem-pur-topos-open-scalar-unit). -/
def tensorSection {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients J S))]
    (E : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    (M : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (m : M.val.obj U) (s : S.obj.obj U) : (E.E.obj M).val.obj U :=
  (eqToHom (E.obj_eq M).symm).val.app U
    (((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
      (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
        (changeOfRingsPresheaf.{u, u, u} a M)).app U
      (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] m))

/-- The original extension summand, expressed by the actual extension-adjunction unit.
Source: Stacks 04IE (blueprint: lem-pur-topos-open-scalar-unit). -/
def extensionSection {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u))
    (M : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients
      (elementTopology A) (presentationElementRing R A)))
    (U : Cᵒᵖ) (f : A.obj.obj U) (m : M.val.obj (elementObj A U f)) :
    ((extension R A).obj M).val.obj U :=
  ((normalizedAdjunction R A).unit.app M).val.app (elementObj A U f) m
```

## New

The identical declarations are in `Sheaf.CategoryTheory.ToposOpenScalarBasic`, publicly
imported by `Sheaf.CategoryTheory.ToposOpenScalarUnit`. Only blueprint ownership references
in docstrings change to `def-pur-topos-open-scalar-section-data`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ToposOpenScalarUnit | R7 | Retains the public API by public import; proves ordinary balancing. |
| Sheaf.CategoryTheory.ToposOpenScalarDerivedFromOrdinary | new, R7 | Uses the unchanged definitions in its hypothesis and conclusion. |
| Sheaf.CategoryTheory.ToposOpenUnitIsIso | new, R7 | Proves actual-unit invertibility using the same definitions. |
| Sheaf.CategoryTheory.ToposOpenScalarRestriction | new, R7 | Proves ordinary restriction balancing using the same definitions. |
| Sheaf.CategoryTheory.ToposOpenScalarBasic | new, R7 | Owns the verbatim definitions. |

The downstream script reports zero importing modules and only the item's own lexical
uses for `sliceMap` and `normalizedAdjunction`. No consumer adaptation is required.
Targets retain the same definitions and statements.

## Status

landed 20261024T234251-L-2548466 2026-10-24 (merge of deliver/R7/Sheaf.CategoryTheory.ToposOpenScalarUnit)
