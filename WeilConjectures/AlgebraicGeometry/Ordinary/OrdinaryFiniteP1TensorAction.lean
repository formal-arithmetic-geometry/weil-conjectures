/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryAffineTensorActions.OrdinaryAffineTensorActions
import WeilConjectures.CategoryTheory.Normalized.NormalizedTensorCounitAction
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.LeftCoefficientProjectionAction
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.Compactification.ProjectiveSpace
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.SixFunctors.Etale.Derived.WeilDual

/-! # Coefficient linearity of the normalized ordinary projective-line counit -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

private theorem tensorStrength_hom
    {C : Type*} [Category* C] [MonoidalCategory C]
    {X Y Z W : C} (e : X ⊗ Y ≅ Z) :
    ((α_ X Y W).symm ≪≫
      (((curriedTensor C).flip.obj W).mapIso e ≪≫
        ((curriedTensor C).flip.mapIso (Iso.refl W)).app Z)).hom =
      (α_ X Y W).inv ≫ e.hom ▷ W := by
  have hi : ((curriedTensor C).flip.map (𝟙 W)).app Z = 𝟙 _ :=
    congr_app ((curriedTensor C).flip.map_id W) Z
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.refl_hom, Functor.flip_obj_map, curriedTensor_map_app]
  exact congrArg (fun z => (α_ X Y W).inv ≫ z)
    ((congrArg (fun z => (e.hom ▷ W) ≫ z) hi).trans (Category.comp_id _))

/-- Combine projection coherence and normalized-counit linearity before specialization. -/
private theorem normalizedAdjunctionTensorCounit_action
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalCategory D] [SymmetricCategory D]
    (F : C ⥤ D) [F.Braided] (G : D ⥤ C) (adj : F ⊣ G)
    [∀ X M, IsIso (Adjunction.leftCoefficientProjectionMap adj X M)]
    (W : D) (b : G.obj W ⟶ 𝟙_ C)
    (c : ∀ X : C, G.obj (F.obj X ⊗ W) ⟶ X)
    (hc : ∀ X, Adjunction.leftCoefficientProjectionMap adj X W ≫ c X =
      X ◁ b ≫ (ρ_ X).hom) (H K : C) :
    Adjunction.leftCoefficientProjectionMap adj H (F.obj K ⊗ W) ≫
      G.map ((α_ (F.obj H) (F.obj K) W).inv ≫
        Functor.LaxMonoidal.μ F H K ▷ W) ≫ c (H ⊗ K) = H ◁ c K := by
  apply normalizedTensorCounit_action F G
    (Adjunction.leftCoefficientProjectionMap adj) ?_ W b c hc H K
  intro X Y M
  simpa only [tensorHom_id, id_tensorHom] using
    (Adjunction.leftCoefficientProjectionMap_coherence adj).2.2.2 X Y M

/-- The abstract action identity expressed with the specified inverse tensor comparison. -/
private theorem normalizedAdjunctionTensorCounit_strength
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalCategory D] [SymmetricCategory D]
    (F : C ⥤ D) [F.Braided] (G : D ⥤ C) (adj : F ⊣ G)
    [∀ X M, IsIso (Adjunction.leftCoefficientProjectionMap adj X M)]
    (W : D) (b : G.obj W ⟶ 𝟙_ C)
    (c : ∀ X : C, G.obj (F.obj X ⊗ W) ⟶ X)
    (hc : ∀ X, Adjunction.leftCoefficientProjectionMap adj X W ≫ c X =
      X ◁ b ≫ (ρ_ X).hom) (H K : C)
    (e : F.obj (H ⊗ K) ≅ F.obj H ⊗ F.obj K)
    (he : Functor.OplaxMonoidal.δ F H K = e.hom) :
    Adjunction.leftCoefficientProjectionMap adj H (F.obj K ⊗ W) ≫
      G.map ((α_ (F.obj H) (F.obj K) W).symm ≪≫
        (((curriedTensor D).flip.obj W).mapIso e.symm ≪≫
          ((curriedTensor D).flip.mapIso (Iso.refl W)).app (F.obj (H ⊗ K)))).hom ≫
        c (H ⊗ K) = H ◁ c K := by
  have hμ : Functor.LaxMonoidal.μ F H K = e.inv := by
    apply (cancel_mono e.hom).mp
    calc
      Functor.LaxMonoidal.μ F H K ≫ e.hom =
          Functor.LaxMonoidal.μ F H K ≫ Functor.OplaxMonoidal.δ F H K :=
        congrArg (fun z => Functor.LaxMonoidal.μ F H K ≫ z) he.symm
      _ = 𝟙 _ := Functor.Monoidal.μ_δ F H K
      _ = e.inv ≫ e.hom := e.inv_hom_id.symm
  have hh := normalizedAdjunctionTensorCounit_action F G adj W b c hc H K
  have ht := congrArg
    (fun m : F.obj H ⊗ F.obj K ⟶ F.obj (H ⊗ K) =>
      Adjunction.leftCoefficientProjectionMap adj H (F.obj K ⊗ W) ≫
        G.map ((α_ (F.obj H) (F.obj K) W).inv ≫ m ▷ W) ≫ c (H ⊗ K)) hμ
  have hs := congrArg
    (fun v : F.obj H ⊗ (F.obj K ⊗ W) ⟶ F.obj (H ⊗ K) ⊗ W =>
      Adjunction.leftCoefficientProjectionMap adj H (F.obj K ⊗ W) ≫ G.map v ≫ c (H ⊗ K))
    (tensorStrength_hom e.symm)
  exact hs.trans (ht.symm.trans hh)

/-- Use an explicitly identified projection, without unfolding it in the action proof. -/
private theorem normalizedProjectionCounit_strength
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalCategory D] [SymmetricCategory D]
    (F : C ⥤ D) [F.Braided] (G : D ⥤ C) (adj : F ⊣ G)
    (p : ∀ (X : C) (M : D), X ⊗ G.obj M ⟶ G.obj (F.obj X ⊗ M))
    [∀ X M, IsIso (p X M)]
    (hp : ∀ X M, p X M = Adjunction.leftCoefficientProjectionMap adj X M)
    (W : D) (b : G.obj W ⟶ 𝟙_ C)
    (c : ∀ X : C, G.obj (F.obj X ⊗ W) ⟶ X)
    (hc : ∀ X, p X W ≫ c X = X ◁ b ≫ (ρ_ X).hom) (H K : C)
    (e : F.obj (H ⊗ K) ≅ F.obj H ⊗ F.obj K)
    (he : Functor.OplaxMonoidal.δ F H K = e.hom) :
    p H (F.obj K ⊗ W) ≫
      G.map ((α_ (F.obj H) (F.obj K) W).symm ≪≫
        (((curriedTensor D).flip.obj W).mapIso e.symm ≪≫
          ((curriedTensor D).flip.mapIso (Iso.refl W)).app (F.obj (H ⊗ K)))).hom ≫
        c (H ⊗ K) = H ◁ c K := by
  let (X : C) (M : D) : IsIso (Adjunction.leftCoefficientProjectionMap adj X M) := by
    rw [← hp X M]
    infer_instance
  have hn (X : C) : Adjunction.leftCoefficientProjectionMap adj X W ≫ c X =
      X ◁ b ≫ (ρ_ X).hom := by
    rw [← hp X W]
    exact hc X
  have ha := normalizedAdjunctionTensorCounit_strength F G adj W b c hn H K e he
  rw [← hp H (F.obj K ⊗ W)] at ha
  exact ha

/-- Finite proper projection invertibility, checked before comparing adjunction actions. -/
private theorem ordinaryProjection_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {P S : Scheme.{u}} (q : P ⟶ S) [IsProper q]
    (X : DerivedCategoryModule A S) (M : DerivedCategoryModule A P) :
    IsIso (ordinaryFiniteProjection A q M X) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite A q
  dsimp [ordinaryFiniteProjection]
  infer_instance

/-- Translate the specified constant-unit normalization to the monoidal unit. -/
private theorem ordinaryCounit_unitNormalization
    (A : Type (u + 1)) [CommRing A]
    {P S : Scheme.{u}} (q : P ⟶ S)
    (W : DerivedCategoryModule A P)
    (b₀ : (ordinaryFinitePushforward A q).obj W ⟶ ordinaryFiniteUnit A S)
    (X : DerivedCategoryModule A S)
    (c : (ordinaryFinitePushforward A q).obj
      (((ordinaryFiniteTensor A P).obj ((ordinaryFinitePullback A q).obj X)).obj W) ⟶ X)
    (hc : ordinaryFiniteProjection A q W X ≫ c =
      ((ordinaryFiniteTensor A S).obj X).map b₀ ≫ (derivedTensorSingleUnitIso X).hom) :
    ordinaryFiniteProjection A q W X ≫ c =
      X ◁ (b₀ ≫ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom) ≫ (ρ_ X).hom := by
  change ordinaryFiniteProjection A q W X ≫ c =
    X ◁ b₀ ≫ X ◁ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom ≫ (ρ_ X).hom at hc
  simpa only [whiskerLeft_comp, Category.assoc] using hc

/-- Bundle the canonical monoidal and braided structures before specializing coefficients. -/
@[instance_reducible]
private noncomputable def etalePullbackBraided
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {P S : Scheme.{u}} (q : P ⟶ S) [(upperStar B q).PreservesFlat] :
    (upperStar B q).leftDerivedFunctor.Braided :=
  { toMonoidal := leftDerivedUpperStarMonoidal B q
    braided := leftDerivedUpperStar_μ_map_braiding_hom B q }

/-- Evaluate the cached symmetry before specializing to a concrete sheaf category. -/
private theorem canonicalTensorSymmetry_hom_app
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (K M : DerivedCategory C) :
    ((DerivedCategory.canonicalTensorSymmetry C).hom.app K).app M =
      (letI := DerivedCategory.braidedCategory' C; (β_ K M).hom) := by
  rfl

/-- The specified ordered projection is the canonical left adjunction projection. -/
private theorem ordinaryProjection_eq_adj
    (A : Type (u + 1)) [CommRing A]
    {P S : Scheme.{u}} (q : P ⟶ S)
    (X : DerivedCategoryModule A S) (M : DerivedCategoryModule A P) :
    let F := ordinaryFinitePullback A q
    let G := ordinaryFinitePushforward A q
    let adj : F ⊣ G := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q
    letI : F.Braided := etalePullbackBraided (ModuleCat.{u + 1} A) q
    ordinaryFiniteProjection A q M X = Adjunction.leftCoefficientProjectionMap adj X M := by
  let F := ordinaryFinitePullback A q
  let G := ordinaryFinitePushforward A q
  let adj : F ⊣ G := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q
  let : F.Braided := etalePullbackBraided (ModuleCat.{u + 1} A) q
  have hδ : Functor.OplaxMonoidal.δNatTrans F =
      leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) q := by
    ext X Y
    change Functor.OplaxMonoidal.δ F X Y = _
    exact leftDerivedUpperStar_δ_eq (ModuleCat.{u + 1} A) q X Y
  have hm := congrArg
    (fun φ => ((adj.rightAdjointProjectionMap φ).app M).app X) hδ
  have ha := congrArg
    (fun z => (β_ X (G.obj M)).hom ≫ z ≫ G.map (β_ M (F.obj X)).hom) hm.symm
  simp only [ordinaryFiniteProjection, derivedTensorSymmetry,
    canonicalTensorSymmetry_hom_app, Adjunction.leftCoefficientProjectionMap,
    rightDerivedLowerStarProjectionMap]
  convert ha using 3 <;> rfl

/-- The normalized projection calculation with the geometry and twist kept abstract. -/
private theorem normalizedOrdinaryProperCounit_tensorAction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {P S : Scheme.{u}} (q : P ⟶ S) [IsProper q]
    (W : DerivedCategoryModule A P)
    (b₀ : (ordinaryFinitePushforward A q).obj W ⟶ ordinaryFiniteUnit A S)
    (c : ∀ X : DerivedCategoryModule A S,
      (ordinaryFinitePushforward A q).obj
        (((ordinaryFiniteTensor A P).obj ((ordinaryFinitePullback A q).obj X)).obj W) ⟶ X)
    (hc₀ : ∀ X : DerivedCategoryModule A S,
      ordinaryFiniteProjection A q W X ≫ c X =
        ((ordinaryFiniteTensor A S).obj X).map b₀ ≫ (derivedTensorSingleUnitIso X).hom)
    (H K : DerivedCategoryModule A S) :
    ordinaryFiniteProjection A q
        (((ordinaryFiniteTensor A P).obj ((ordinaryFinitePullback A q).obj K)).obj W) H ≫
      (ordinaryFinitePushforward A q).map
        ((derivedTensorAssociator (ModuleCat.{u + 1} A) P
          ((ordinaryFinitePullback A q).obj H) ((ordinaryFinitePullback A q).obj K) W).symm ≪≫
          ordinaryFiniteTensorRightMapIso A P
            (ordinaryFiniteTensorPullback A q H K).symm (Iso.refl W)).hom ≫
      c (((ordinaryFiniteTensor A S).obj H).obj K) =
        ((ordinaryFiniteTensor A S).obj H).map (c K) := by
  let F := ordinaryFinitePullback A q
  let G := ordinaryFinitePushforward A q
  let adj : F ⊣ G := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q
  let : F.Braided := etalePullbackBraided (ModuleCat.{u + 1} A) q
  let p := fun X M => ordinaryFiniteProjection A q M X
  let (X : DerivedCategoryModule A S) (M : DerivedCategoryModule A P) :
      IsIso (p X M) := ordinaryProjection_isIso A q X M
  have hp (X : DerivedCategoryModule A S) (M : DerivedCategoryModule A P) :
      p X M = Adjunction.leftCoefficientProjectionMap adj X M :=
    ordinaryProjection_eq_adj A q X M
  let b := b₀ ≫ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom
  have hc (X : DerivedCategoryModule A S) :
      p X W ≫ c X = X ◁ b ≫ (ρ_ X).hom := by
    exact ordinaryCounit_unitNormalization A q W b₀ X (c X) (hc₀ X)
  exact normalizedProjectionCounit_strength F G adj p hp W b c hc H K
    (ordinaryFiniteTensorPullback A q H K)
    (leftDerivedUpperStarMonoidal_δ (ModuleCat.{u + 1} A) q H K)

/-- A normalized projective-line counit respects the ordered tensor action.
Source: blueprint affine-space top trace, the projective factor in step 3;
Stacks Tags 0B56 and 0GL1
(blueprint: lem-pur-ordinary-finite-p1-tensor-action).

Proof: the finite-coefficient proper projection theorem makes every ordered
projection invertible. Replace the constant single complex in normalization by
the derived monoidal unit using its canonical isomorphism. The associativity of
the actual ordered proper projection and normalizedTensorCounit_action give the
stated action identity. The tensorator is precisely the inverse of
ordinaryFiniteTensorPullback, so no choice of comparison or trace occurs. -/
theorem ordinaryFiniteP1Counit_tensorAction
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (D : OrdinaryFiniteP1Datum A N hA t S hS)
    (H K : DerivedCategoryModule A S) :
    (OrdinaryAffineTensorActions.properActionNat A S H).app
        ((ordinaryFiniteP1Right A N hA S).obj K) ≫
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
        (OrdinaryAffineTensorActions.properStrength A N hA S H K).hom ≫
      D.adjunction.counit.app (((ordinaryFiniteTensor A S).obj H).obj K) =
        ((ordinaryFiniteTensor A S).obj H).map (D.adjunction.counit.app K) := by
  exact normalizedOrdinaryProperCounit_tensorAction A (ProjectiveLine S ↘ S)
    ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (D.decomposition.inv ≫ biprod.snd)
    (fun X => D.adjunction.counit.app X) D.counit_normalization H K

end AlgebraicGeometry.Etale
