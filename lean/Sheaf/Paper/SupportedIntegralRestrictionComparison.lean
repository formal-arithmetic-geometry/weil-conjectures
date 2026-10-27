module

public import Sheaf.Paper.SupportedIntegralRestrictionArrows

/-! # Supported integral restriction and strict quotient tower comparison

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md (2), first paragraph
(blueprint: def-sfb-supported-integral-restriction-comparison).
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

/-- The complete normalized arrow comparison. Its endpoint equations use the whole
strict quotient augmentation. The pullback identification is fixed by the canonical
comparison square and the unit-normalized scalar-coordinate mate.
Source: blueprint integral closed-fibre comparison, all compatibility clauses
(blueprint: def-sfb-supported-integral-restriction-comparison). -/
structure RestrictionComparison {T₀ T S : Scheme.{u}} (t : T₀ ⟶ T)
    [Resolutions R T] [Resolutions R T₀]
    {tree : QcqsOpenClosedTree T} (p : tree.Path S) (π : R) (ℓ : ℕ)
    (c₀ : Coordinates R T₀) (c : Coordinates R T) (d : Descent R p π ℓ c) where
  pullback : PullbackCoordinates R t c₀ c
  identification₀ :
    d.functor ⋙ towerMap (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) t) ⋙
        towerMap (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) T₀) ≅
      supportedQuotients R p π ⋙
        towerMap (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj R) t) ⋙
        towerMap c₀.functor
  pullback_normalization : ∀ (M : Models R S) (n : ℕᵒᵖ),
    (identification₀.hom.app M).app n =
      (comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) t).inv.app ((d.functor.obj M).obj n) ≫
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) t).map
        ((d.identification.hom.app M).app n) ≫
      pullback.upper.hom.app (((supportedQuotients R p π).obj M).obj n)
  iso : integralArrows R t p ≅ etaleArrows R t d.functor
  source_normalization : SourceNormalized R t p π ℓ c d iso
  target_normalization : ∀ M : Models R S,
    PulledEndpointNormalized
      (C0 := Modules R T) (C := Modules R T₀)
      (B := Sheaf (Scheme.ProEt.topology T₀) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
      (A0 := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} R)))
      (A := Sheaf T₀.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} R)))
      (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj R) t)
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) t)
      c₀.functor (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) T₀)
      (condensedModuleSections (Profinite.continuousCoefficientRingObj R) T₀)
      (etaleSections R T₀) (proetaleSections R T₀)
      (comparisonSections R T₀) c₀.sectionsIso.inv
      ((supportedModels R p).obj M) ((supportedQuotients R p π).obj M)
      (supportedUnit R p π M) (d.functor.obj M) (identification₀.hom.app M)
      (iso.hom.app M).right



end AlgebraicGeometry.ProEtale.SupportedIntegral
