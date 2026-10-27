/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.SupportedIntegralRestrictionComparison

/-! # Coherence of normalized restriction endpoints

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md (2),
integral closed-fibre comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.SupportedIntegral
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

variable [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ Ab.{u + 1})]
/-- Normalized endpoint reconstructions intertwine the actual horizontal restrictions.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md (2), integral
closed-fibre comparison, restriction and adjunction coherence
(blueprint: lem-sfb-supported-integral-restriction-square).

Proof in words:
1. Use the normalized ringed restriction/strict-limit coherence theorem on the supported
ordinary quotient tower and its actual augmentation. It identifies integral restriction,
followed by the pulled-back augmented limit, with augmented limit followed by the total
finite-level pro-etale restriction. The inverse-image comparison is the canonical
adjunction mate, so the stated marking he₀ identifies the same pulled-back tower.
2. The etale/pro-etale comparison square and its adjunction mate identify the actual
finite-level restrictions. Scalar-forgetting coherence retains this equality in fixed
scalar coordinates. Derive on strict towers and then apply total inverse limit;
normalized evaluation retains all transitions and the ordinary single comparisons.
3. Substitute the two endpoint normalization equations. Step 1 and step 2 equate their
composites with the target finite comparison and marked tower map. Both latter maps
are invertible by bounded-below comparison and the marked isomorphism. Cancel them
on the right. The remaining equation is exactly the displayed square. No torsion
rigidity assumption is used in this coherence argument. -/
theorem supported_integral_restriction_square
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (π : R)
    (hR :
      (∃ e : R ≃+* ℤ_[ℓ], Continuous e ∧ Continuous e.symm ∧ e π = (ℓ : ℤ_[ℓ])) ∨
      (letI := spectralNorm.nontriviallyNormedField (Padic ℓ) E
       ∃ e : R ≃+* Padic.coefficientExtensionIntegers ℓ E,
         Continuous e ∧ Continuous e.symm ∧
         Ideal.span ({e π} : Set (Padic.coefficientExtensionIntegers ℓ E)) =
           Padic.coefficientExtensionMaximalIdeal ℓ E))
    {T₀ T S : Scheme.{u}} [Resolutions R T] [Resolutions R T₀]
    [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace T₀] [QuasiSeparatedSpace T₀]
    (t : T₀ ⟶ T) [IsClosedImmersion t]
    (tree : QcqsOpenClosedTree T) (p : tree.Path S)
    (c₀ : Coordinates R T₀) (c : Coordinates R T)
    (d : Descent R p π ℓ c) (b : PullbackCoordinates R t c₀ c)
    (e₀ :
      d.functor ⋙ towerMap (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) t) ⋙
          towerMap (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) T₀) ≅
        supportedQuotients R p π ⋙
          towerMap (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj R) t) ⋙
          towerMap c₀.functor)
    (he₀ : ∀ (M : Models R S) (n : ℕᵒᵖ),
      (e₀.hom.app M).app n =
        (comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1} R)) t).inv.app ((d.functor.obj M).obj n) ≫
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) t).map
          ((d.identification.hom.app M).app n) ≫
        b.upper.hom.app (((supportedQuotients R p π).obj M).obj n))
    (l : integralArrows R t p ⋙ Arrow.leftFunc ≅
      etaleArrows R t d.functor ⋙ Arrow.leftFunc)
    (r : integralArrows R t p ⋙ Arrow.rightFunc ≅
      etaleArrows R t d.functor ⋙ Arrow.rightFunc)
    (hl : ∀ M : Models R S,
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
        _ (𝟙 _) (l.hom.app M))
    (hr : ∀ M : Models R S,
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
        (supportedUnit R p π M) (d.functor.obj M) (e₀.hom.app M)
        (r.hom.app M)) :
    ∀ M : Models R S,
      l.hom.app M ≫ ((etaleArrows R t d.functor).obj M).hom =
        ((integralArrows R t p).obj M).hom ≫ r.hom.app M := by sorry

end AlgebraicGeometry.ProEtale.SupportedIntegral
