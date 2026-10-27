# SheafOfModules.FiniteFreeScalarArrow and the strict-limit comparison interface

## Reason

The ordinary finite-basis lemma must use the finite-free arrow type without importing
its own consumer theorem. Move the existing interface, unchanged, into
`Sheaf.Paper.FieldScalarStrictLimitData` and publicly reexport it from the original
module. This removes the prospective import cycle. This extraction was made before
profiling the main proof; it is not a split to evade the compile-time limit.
A parser-level comparison against the shared source confirms that all five moved
signatures and normalized bodies are identical, and the main theorem signature
is identical. No definition body, theorem signature, universe, binder, or mathematical
meaning changes.
The original theorem statement is retained verbatim. No target statement changes or
semantic target review is needed: the definitions used by targets are identical.

## Old

Location: `lean/Sheaf/Paper/FieldScalarStrictLimit.lean`. The relocated declaration
block, including its original namespace and variable context, is:

```lean
abbrev FiniteFreeScalarArrow (R S : Sheaf J CommRingCat.{u}) :=
  {a : R ⟶ S // ∃ d : ℕ, Nonempty
    ((∏ᶜ fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction a).obj (unit (ringSheaf S)))}

variable [hD : ∀ R : Sheaf J CommRingCat.{u},
    HasDerivedCategory.{w} (ringedSiteModules.{u} (ringSheaf R))]
  [hDT : ∀ R : Sheaf J CommRingCat.{u},
    HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R))]

/-- Projection-normalized scalar/limit compatibility for one finite-free map.
All maps are module-sheaf maps over S, and hence S-linear. The ordinary normalization
and uniqueness exclude a choice of a triangle filler. The cone formula uses the same beta
on both coordinates with the canonical shifted-cone coordinates roosχ.
Source: blueprint field-extension-towers proof (1)
(blueprint: lem-sp-field-scalar-strict-limit). -/
structure ScalarStrictLimitComparison
    {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasCountableProducts B]
    [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) F)]
    [PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) F)]
    (LR : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (LS : DerivedCategory.{w} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w} B)
    (rhoR : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ LR)
    (rhoS : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ LS) where
  /-- Naturality is on the derived category of entire strict towers. -/
  comparison : LR ⋙ F.mapDerivedCategory ≅
    (projectionPost (I := ℕᵒᵖ) F).mapDerivedCategory ⋙ LS
  /-- The ordinary scalar/limit comparison fixes the derived map. -/
  normalized : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    F.mapDerivedCategory.map ((roosDerivedUnit rhoR).app X) ≫
        comparison.hom.app (DerivedCategory.Q.obj X) =
      F.mapDerivedCategoryFactors.hom.app (limit X.asFunctor) ≫
        DerivedCategory.Q.map (limit.post X.asFunctor
          (F.mapHomologicalComplex (.up ℤ))) ≫
        (roosDerivedUnit rhoS).app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X) ≫
        LS.map ((projectionPost (I := ℕᵒᵖ) F).mapDerivedCategoryFactors.inv.app X)
  /-- The product map is the canonical map specified by all its projections. -/
  beta : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, (F.mapHomologicalComplex (.up ℤ)).obj (roosP X) ≅
    roosP (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X)
  /-- Projection formula; in a finite basis this is finite-sum/product reindexing. -/
  beta_projection : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
    (beta X).hom ≫ Pi.π _ n =
      (F.mapHomologicalComplex (.up ℤ)).map
        (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n)
  /-- The product map intertwines one minus the transition shift. -/
  beta_transition : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    (F.mapHomologicalComplex (.up ℤ)).map (roosU X) ≫ (beta X).hom =
      (beta X).hom ≫ roosU
        (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X)
  /-- An actual natural chain isomorphism of the signed Roos cones. -/
  cone : roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅
    (projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ) ⋙ roosF
  /-- First product coordinate of the actual cone map. -/
  cone_first : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ),
    (cone.hom.app X).f (p + 1) ≫
        (roosχ (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex
          (.up ℤ)).obj X) p).hom ≫ biprod.fst =
      F.map ((roosχ X p).hom ≫ biprod.fst) ≫ (beta X).hom.f p
  /-- Second product coordinate of the same cone map. -/
  cone_second : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ),
    (cone.hom.app X).f (p + 1) ≫
        (roosχ (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex
          (.up ℤ)).obj X) p).hom ≫ biprod.snd =
      F.map ((roosχ X p).hom ≫ biprod.snd) ≫ (beta X).hom.f (p + 1)
  /-- The cone map realizes precisely the canonical comparison in the derived category. -/
  cone_realizes : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    F.mapDerivedCategory.map (rhoR.hom.app X) ≫
        comparison.hom.app (DerivedCategory.Q.obj X) =
      F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
        DerivedCategory.Q.map (cone.hom.app X) ≫
        rhoS.hom.app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X) ≫
        LS.map ((projectionPost (I := ℕᵒᵖ) F).mapDerivedCategoryFactors.inv.app X)



namespace FieldScalarStrictLimit

universe uA vA uD vD

/-- The existing exact derived functor with explicit exactness witnesses. This is only
an abbreviation, preventing repeated searches for an entire family of witnesses.
Source: blueprint field-extension-towers (1)
(blueprint: lem-sp-field-scalar-strict-limit). -/
abbrev exactDerived
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive]
    (hl : PreservesFiniteLimits F) (hc : PreservesFiniteColimits F) :
    DerivedCategory.{w} A ⥤ DerivedCategory.{w} B :=
  @Functor.mapDerivedCategory A _ _ _ B _ _ _ F _ hl hc

/-- The balanced derived associator is the existing localization of the ordinary one.
Source: blueprint field-extension-towers (1)
(blueprint: lem-sp-field-scalar-strict-limit). -/
def exactDerivedComp
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{w} D]
    {F : A ⥤ B} [F.Additive] {G : B ⥤ D} [G.Additive] {H : A ⥤ D} [H.Additive]
    (hlF : PreservesFiniteLimits F) (hcF : PreservesFiniteColimits F)
    (hlG : PreservesFiniteLimits G) (hcG : PreservesFiniteColimits G)
    (hlH : PreservesFiniteLimits H) (hcH : PreservesFiniteColimits H)
    (alpha : F ⋙ G ≅ H) :
    exactDerived F hlF hcF ⋙ exactDerived G hlG hcG ≅ exactDerived H hlH hcH :=
  letI := hlF
  letI := hcF
  letI := hlG
  letI := hcG
  letI := hlH
  letI := hcH
  Functor.mapDerivedCategoryCompNatIso alpha

/-- The existing derived identity unitor, induced by the ordinary scalar unitor.
Source: blueprint field-extension-towers (1)
(blueprint: lem-sp-field-scalar-strict-limit). -/
def exactDerivedUnit
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {F : A ⥤ A} [F.Additive]
    (hl : PreservesFiniteLimits F) (hc : PreservesFiniteColimits F)
    (alpha : F ≅ 𝟭 A) : exactDerived F hl hc ≅ 𝟭 (DerivedCategory.{w} A) :=
  letI := hl
  letI := hc
  Functor.mapDerivedCategoryNatIso alpha ≪≫ Functor.mapDerivedCategoryIdIso A

end FieldScalarStrictLimit
open FieldScalarStrictLimit
```

## New

The exact block under Old now lives in
`lean/Sheaf/Paper/FieldScalarStrictLimitData.lean`, in the same `SheafOfModules`
namespace, with the original universe and section-variable context. Its five public
declarations retain the same names, signatures and bodies. The original module has
`public import Sheaf.Paper.FieldScalarStrictLimitData`, so its consumers see the same API.
The new ordinary-coordinate and small-site-product lemmas import the data module.
All original public imports are retained through the data module. The exact-functor
import is public there because the interface definitions explicitly use that API.

## Users

The four `tools/downstream.py --uses` runs for ScalarStrictLimitComparison,
exactDerived, exactDerivedComp and exactDerivedUnit, and the corresponding run for
FiniteFreeScalarArrow, report only the item module; there are zero downstream modules.
A source-wide `rg` check agrees. No other group's module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FieldScalarStrictLimit | G3 | Publicly reexports the unchanged interface; proves its theorem. |
| Sheaf.Paper.FieldScalarStrictLimitData | G3, new | Owns the five unchanged interface declarations. |
| Sheaf.Paper.FieldScalarOrdinaryCoordinates | G3, new | Imports the interface without importing its consumer. |
| Sheaf.Paper.SmallProEtaleExactProducts | G3, new | Imports the existing ringed-site and pro-etale notation. |

## Status

landed 20261025T202058-L-2671112 2026-10-25 (merge of deliver/G3/Sheaf.Paper.FieldScalarStrictLimit)
