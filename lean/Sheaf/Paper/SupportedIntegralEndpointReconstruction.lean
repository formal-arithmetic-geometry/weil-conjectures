/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.SupportedIntegralRestrictionComparison

/-! # Normalized endpoint reconstruction

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
/-- The source marking of an endpoint comparison, using the actual strict augmentation.
Source: blueprint integral closed-fibre comparison, quotient normalization
(blueprint: lem-sfb-supported-integral-endpoint-reconstruction). -/
def SourceEndpointNormalized {T₀ T S : Scheme.{u}} (t : T₀ ⟶ T)
    [Resolutions R T] [Resolutions R T₀]
    {tree : QcqsOpenClosedTree T} (p : tree.Path S) (π : R) (ℓ : ℕ)
    (c : Coordinates R T) (d : Descent R p π ℓ c)
    (e : integralArrows R t p ⋙ Arrow.leftFunc ≅
      etaleArrows R t d.functor ⋙ Arrow.leftFunc) : Prop :=
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
      _ (𝟙 _) (e.hom.app M)

/-- The target marking after exact inverse image, using its degree-zero comparison.
Source: blueprint integral closed-fibre comparison, pulled-back quotient normalization
(blueprint: lem-sfb-supported-integral-endpoint-reconstruction). -/
def TargetEndpointNormalized {T₀ T S : Scheme.{u}} (t : T₀ ⟶ T)
    [Resolutions R T] [Resolutions R T₀]
    {tree : QcqsOpenClosedTree T} (p : tree.Path S) (π : R) (ℓ : ℕ)
    (c₀ : Coordinates R T₀) (c : Coordinates R T) (d : Descent R p π ℓ c)
    (identification₀ :
      d.functor ⋙ towerMap (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) t) ⋙
          towerMap (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) T₀) ≅
        supportedQuotients R p π ⋙
          towerMap (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj R) t) ⋙
          towerMap c₀.functor)
    (e : integralArrows R t p ⋙ Arrow.rightFunc ≅
      etaleArrows R t d.functor ⋙ Arrow.rightFunc) : Prop :=
  ∀ M : Models R S,
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
      (e.hom.app M)

/-- The two endpoint reconstructions, before asserting that they intertwine restriction.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md (2), integral
closed-fibre comparison, strict completion and finite-level comparison
(blueprint: lem-sfb-supported-integral-endpoint-reconstruction).

Proof in words:
1. The strict two-term reductions have transition (pi,1). Finite scalar local-model
completeness makes their augmented limit the original module, including torsion models.
The cone-to-ordinary-quotient map is an isomorphism after total inverse limit and carries
the degree-zero identity augmentation to the actual quotient projection.
2. Each support edge is exact and preserves countable products: use the pro-etale open
extension product theorem for open edges, and the right adjoint property for closed ones.
Exact countable products and the normalized strict-limit comparison transport the entire
augmentation. The closed inverse image also preserves these products, with no assumption
on its complementary open. Thus both supported endpoint augmentations are invertible.
3. Scalar restriction identifies actual module-derived sections with finite-coefficient
derived sections. Bounded-below etale/pro-etale comparison applies at every quotient
level. The normalized evaluation comparisons identify these maps with the evaluations
of the actual comparison of derived strict towers. Levelwise detection gives its
invertibility. Apply total inverse limit to these strict-tower isomorphisms.
4. Compose the maps of step 2 with the inverses of step 3 and the marked identifications
d and e₀. Their unit equations give exactly SourceEndpointNormalized and
TargetEndpointNormalized. All transformations are functorial in actual model maps,
so the pointwise isomorphisms form the displayed natural isomorphisms. -/
theorem supported_integral_endpoint_reconstruction
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
        b.upper.hom.app (((supportedQuotients R p π).obj M).obj n)) :
    ∃ (l : integralArrows R t p ⋙ Arrow.leftFunc ≅
          etaleArrows R t d.functor ⋙ Arrow.leftFunc)
      (r : integralArrows R t p ⋙ Arrow.rightFunc ≅
          etaleArrows R t d.functor ⋙ Arrow.rightFunc),
      SourceEndpointNormalized R t p π ℓ c d l ∧
        TargetEndpointNormalized R t p π ℓ c₀ c d e₀ r := by sorry

end AlgebraicGeometry.ProEtale.SupportedIntegral
