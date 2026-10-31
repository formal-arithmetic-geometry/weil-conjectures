/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # The unit component of normalized vector purity -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe u uB
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.OrientationRefinement

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
  Etale.vectorBundleIntegration

-- Reuse the canonical localization instances cached by the ordinary pullback.
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  Etale.ordinaryFinitePullback._proof_1
  Etale.ordinaryFinitePullback._proof_2
  Etale.ordinaryFinitePullback._proof_3
  Etale.ordinaryFinitePullback._proof_4
  Etale.ordinaryFinitePullback._proof_5
  Etale.ordinaryFinitePullback._proof_6
  Etale.ordinaryFinitePullback._proof_7
  Etale.ordinaryFinitePullback._proof_8
  Etale.ordinaryFinitePullback._proof_9
  Etale.ordinaryFinitePullback._proof_10
  Etale.ordinaryFinitePullback._proof_11
  Etale.ordinaryFinitePullback._proof_12
  Etale.ordinaryFinitePullback._proof_13

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
  Etale.leftDerivedUpperStarIsoMapDerivedCategory

private theorem normalized_unit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) (R P : D ⥤ C) (adj : L ⊣ R) (W : C) (t : L.obj W ⟶ 𝟙_ D)
    (γ : P ⋙ tensorLeft W ⟶ R) (unit : P.obj (𝟙_ D) ≅ 𝟙_ C)
    (π : L.obj W ⊗ 𝟙_ D ⟶ L.obj (W ⊗ P.obj (𝟙_ D)))
    (hn : π ≫ L.map (γ.app (𝟙_ D)) ≫ adj.counit.app (𝟙_ D) =
      t ▷ (𝟙_ D) ≫ (λ_ (𝟙_ D)).hom)
    (hu : π ≫ L.map (W ◁ unit.hom ≫ (ρ_ W).hom) = (ρ_ (L.obj W)).hom) :
    ((ρ_ W).inv ≫ W ◁ unit.inv) ≫ γ.app (𝟙_ D) = adj.homEquiv W (𝟙_ D) t := by
  rw [Category.assoc]
  have : IsIso π := IsIso.of_isIso_fac_right hu
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Equiv.symm_apply_apply]
  have hm : L.map (γ.app (𝟙_ D)) ≫ adj.counit.app (𝟙_ D) =
      L.map (W ◁ unit.hom ≫ (ρ_ W).hom) ≫ t := by
    apply (cancel_epi π).1
    simpa only [← Category.assoc, hu, unitors_equal, rightUnitor_naturality] using hn
  rw [hm, ← L.map_comp_assoc, ← L.map_comp_assoc]
  simp

/-- Retain the abstract monoidal cache when specializing coefficient categories. -/
private theorem normalized_etale_component
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [Etale.UpperStarPreservesFlat B]
    {FC : B → B → Type (u + 1)} {CC : B → Type (u + 1)}
    [∀ (M N : B), FunLike (FC M N) (CC M) (CC N)] [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    letI := purityEtaleMonoidal B X
    letI := purityEtaleMonoidal B Y
    ∀ (R : DerivedCategory (Sheaf Y.smallEtaleTopology B) ⥤
        DerivedCategory (Sheaf X.smallEtaleTopology B))
      (adj : Etale.rightDerivedLowerShriek B f ⊣ R)
      (W : DerivedCategory (Sheaf X.smallEtaleTopology B))
      (t : (Etale.rightDerivedLowerShriek B f).obj W ⟶ 𝟙_ _)
      (γ : (Etale.upperStar B f).leftDerivedFunctor ⋙ tensorLeft W ⟶ R)
      (_hn : IntegrationGammaNormalized (Etale.rightDerivedLowerShriek B f) R
        (Etale.upperStar B f).leftDerivedFunctor adj W t
        ((Etale.projectionMap B f).app W) γ),
      ((ρ_ W).inv ≫ W ◁ (Etale.leftDerivedUpperStarUnitIso B f).inv) ≫ γ.app (𝟙_ _) =
        adj.homEquiv _ _ t := by
  intro R adj W t γ hn
  obtain ⟨m, hm, hp⟩ := hn (𝟙_ _)
  have hm' := eq_of_heq hm
  have hp' := eq_of_heq hp
  rw [← hm'] at hp'
  exact normalized_unit (Etale.rightDerivedLowerShriek B f) R
    (Etale.upperStar B f).leftDerivedFunctor adj W t γ
    (Etale.leftDerivedUpperStarUnitIso B f)
    (((Etale.projectionMap B f).app W).app (𝟙_ _)) hp'
    (Etale.projectionMap_rightUnitality B f W)

/-- The unit component of a normalized vector-purity family is the Brown adjunct
of the specified integration map, after inserting the inverse source unitor.
Source: latest blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, specified integration and transposition.
(blueprint: lem-pur-vector-normalized-unit-adjunct).

Proof: Evaluate IntegrationGammaNormalized at the tensor unit and eliminate its
heterogeneous equality witnesses. Right unitality of the compact-support projection
identifies the projection followed by the image of the source unit map with the
right unitor. This proves that the projection at the unit is invertible. Cancel it
in the normalization equation, using equality of the unitors at the tensor unit
and naturality of the right unitor. Apply the inverse Brown Hom equivalence to
identify the unit component with the adjunct of integration. This calculation uses
only unit isomorphisms and works for rank zero and empty bases as well.
-/
theorem vector_normalized_unit_adjunct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hB : IsUnit (N : Γ(B, ⊤)))
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    (γ : VectorPurityGamma A N hA B d F)
    (hn : VectorPurityGammaNormalized A N hN hA B hB d F γ) :
    letI := (Etale.vectorIntegration_geometry B d F).1
    letI := (Etale.vectorIntegration_geometry B d F).2.1
    let π := VectorBundleZeroSection.π B d F
    let W := Etale.vectorIntegrationCoefficient A N hA B d F
    let adj := Etale.rightDerivedUpperShriekAdjunction A π
    ((ρ_ W).inv ≫ W ◁ (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) π).inv) ≫
        γ.app (𝟙_ _) =
      adj.homEquiv W (𝟙_ _) (Etale.vectorBundleIntegration N hN A hA B hB d F ≫
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B).hom) := by
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  exact normalized_etale_component (ModuleCat.{u + 1} A)
    (VectorBundleZeroSection.π B d F) (RfUpper A (VectorBundleZeroSection.π B d F))
    (Etale.rightDerivedUpperShriekAdjunction A
      (VectorBundleZeroSection.π B d F))
    (Etale.vectorIntegrationCoefficient A N hA B d F)
    (Etale.vectorBundleIntegration N hN A hA B hB d F ≫
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B).hom) γ hn

end WeilConjectures.PurityFiniteSetting.OrientationRefinement
