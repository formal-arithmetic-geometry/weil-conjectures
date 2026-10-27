module

public import Sheaf.Paper.SupportedIntegralModelTowerData

/-! # Supported integral restriction and strict quotient tower comparison

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md (2), first paragraph
(blueprint: def-sfb-supported-integral-restriction-arrows).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.SupportedIntegral
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ Ab.{u + 1})]

/-- The actual integral restriction arrow, natural in the full category of finite models.
Source: blueprint integral closed-fibre comparison, left displayed arrow
(blueprint: def-sfb-supported-integral-restriction-arrows). -/
abbrev integralArrows {T₀ T S : Scheme.{u}} (t : T₀ ⟶ T)
    {tree : QcqsOpenClosedTree T} (p : tree.Path S) :
    Models R S ⥤ Arrow (DerivedCategory Ab.{u + 1}) :=
  supportedModels R p ⋙ DerivedCategory.singleFunctor (Modules R T) 0 ⋙
    arrows (derivedRestriction R t)



/-- The actual derived restriction of strict etale module towers.
Source: blueprint integral closed-fibre comparison, finite horizontal arrows
(blueprint: def-sfb-supported-integral-restriction-arrows). -/
def etaleTowerRestriction {T₀ T : Scheme.{u}} (t : T₀ ⟶ T)
    [Resolutions R T] [Resolutions R T₀] :
    (towerMap (etaleSections R T)).rightDerivedFunctor ⟶
      (towerMap (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) t)).mapDerivedCategory ⋙
        (towerMap (etaleSections R T₀)).rightDerivedFunctor :=
  derivedTowerRestriction
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) t)
    (etaleSections R T) (etaleSections R T₀) (etaleRestriction R t)



/-- The finite horizontal arrow is derived on strict etale module towers; total inverse
limit is then applied in D(strict towers of Ab) to both endpoints and the arrow.
Source: blueprint integral closed-fibre comparison, right displayed arrow
(blueprint: def-sfb-supported-integral-restriction-arrows). -/
def etaleArrows {T₀ T S : Scheme.{u}} (t : T₀ ⟶ T)
    [Resolutions R T] [Resolutions R T₀]
    (F : Models R S ⥤ (ℕᵒᵖ ⥤ Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} R)))) :
    Models R S ⥤ Arrow (DerivedCategory Ab.{u + 1}) :=
  F ⋙ DerivedCategory.singleFunctor _ 0 ⋙ arrows (etaleTowerRestriction R t) ⋙
    (lim : (ℕᵒᵖ ⥤ Ab.{u + 1}) ⥤ Ab.{u + 1}).rightDerivedFunctor.mapArrow



/-- Quotient augmentation normalization at the source endpoint.
Source: blueprint integral closed-fibre comparison, actual quotient maps
(blueprint: def-sfb-supported-integral-restriction-arrows). -/
def SourceNormalized {T₀ T S : Scheme.{u}} (t : T₀ ⟶ T)
    [Resolutions R T] [Resolutions R T₀]
    {tree : QcqsOpenClosedTree T} (p : tree.Path S) (π : R) (ℓ : ℕ)
    (c : Coordinates R T) (d : Descent R p π ℓ c)
    (e : integralArrows R t p ≅ etaleArrows R t d.functor) : Prop :=
  ∀ M : Models R S,
    EndpointNormalized
      (C := Modules R T)
      (B := Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
      (A := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} R)))
      c.functor
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) T)
      (condensedModuleSections (Profinite.continuousCoefficientRingObj R) T)
      (etaleSections R T) (proetaleSections R T)
      (comparisonSections R T) c.sectionsIso.inv
      ((supportedModels R p).obj M) ((supportedQuotients R p π).obj M)
      (supportedUnit R p π M) (d.functor.obj M) (d.identification.hom.app M)
      _ (𝟙 _) (e.hom.app M).left



end AlgebraicGeometry.ProEtale.SupportedIntegral
