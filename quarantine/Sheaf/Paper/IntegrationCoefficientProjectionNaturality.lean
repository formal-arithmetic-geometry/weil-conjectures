/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.Paper.IntegrationExponentTransposeData

/-! # Exponent transport: a step of the normalized integration argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

private theorem inverse_projection_square {C : Type*} [Category C]
    {X X' Y Y' : C} (p : X ≅ Y) (q : X' ≅ Y')
    (a : X ⟶ X') (b : Y ⟶ Y')
    (h : b ≫ q.inv = p.inv ≫ a) : a ≫ q.hom = p.hom ≫ b := by
  apply (cancel_epi p.inv).mp
  rw [← Category.assoc, ← h]
  simp

private theorem naturality_pasting
    {C : Type*} [Category C] {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ : C}
    (a : O₀ ⟶ O₁) (s' : O₁ ⟶ O₂) (s : O₀ ⟶ O₃) (b : O₃ ⟶ O₂)
    (p' : O₂ ⟶ O₄) (p : O₃ ⟶ O₅) (d : O₅ ⟶ O₄)
    (t' : O₄ ⟶ O₆) (t : O₅ ⟶ O₇) (e : O₇ ⟶ O₆)
    (hs : a ≫ s' = s ≫ b) (hp : b ≫ p' = p ≫ d)
    (ht : d ≫ t' = t ≫ e) :
    a ≫ s' ≫ p' ≫ t' = (s ≫ p ≫ t) ≫ e := by
  simp only [Category.assoc]
  rw [reassoc_of% hs, reassoc_of% hp, ht]

private theorem map_square {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {O₀ O₁ O₂ O₃ : C} {a : O₀ ⟶ O₁} {b : O₁ ⟶ O₃}
    {c : O₀ ⟶ O₂} {d : O₂ ⟶ O₃} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, h, F.map_comp]

private theorem ordinary_projection_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [HasCompactification q]
    (K : Etale.DerivedCategoryModule A Y)
    {L L' : Etale.DerivedCategoryModule A X} (b : L ⟶ L') :
    ((Etale.ordinaryFiniteTensor A Y).obj K).map
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map b) ≫
      Etale.compactProjectionMapCoeffFirst A q K L' =
      Etale.compactProjectionMapCoeffFirst A q K L ≫
        (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map
          (((Etale.ordinaryFiniteTensor A X).obj
            ((Etale.ordinaryFinitePullback A q).obj K)).map b) := by
  have hs := ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).naturality
    ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map b)
  have hp := NatTrans.congr_app
    ((Etale.projectionMap (ModuleCat.{u + 1} A) q).naturality b) K
  have ht := NatTrans.congr_app
    ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.naturality b)
    ((Etale.ordinaryFinitePullback A q).obj K)
  simp -implicitDefEqProofs only [Etale.ordinaryFinitePullback, Etale.ordinaryFiniteTensor,
    Functor.flip_obj_obj, Functor.flip_obj_map] at *
  simp -implicitDefEqProofs only [Etale.derivedTensorRightDerivedLowerShriek,
    Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar, Functor.comp_map] at hp
  unfold Etale.compactProjectionMapCoeffFirst
  simp -implicitDefEqProofs only [Etale.rightDerivedLowerShriek] at *
  simp -implicitDefEqProofs only [Etale.derivedTensorRightDerivedLowerShriek,
    Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar, Functor.comp_obj,
    Functor.comp_map] at *
  simp -implicitDefEqProofs only [NatTrans.comp_app] at hp
  exact naturality_pasting _ _ _ _ _ _ _ _ _ _ hs hp
    (map_square (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification q)) ht)

private theorem pro_projection_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {q : X ⟶ Y} (c : Compactification q)
    (K : integrationPro A Y) {W W' : integrationPro A X} (b : W ⟶ W') :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map b) ≫
      projection (ModuleCat.{u + 1} A) c W' K =
      projection (ModuleCat.{u + 1} A) c W K ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj
            ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj K)).map b) := by
  have hs := ((symmetry (ModuleCat.{u + 1} A) Y).hom.app K).naturality
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map b)
  have hp := NatTrans.congr_app
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).naturality b) K
  have ht := NatTrans.congr_app
    ((symmetry (ModuleCat.{u + 1} A) X).hom.naturality b)
    ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj K)
  simp -implicitDefEqProofs only [Functor.flip_obj_obj, Functor.flip_obj_map] at *
  simp -implicitDefEqProofs only [derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar, Functor.comp_obj,
    Functor.comp_map, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.postcompose₂_obj_obj_obj_obj, NatTrans.comp_app] at hp
  unfold projection
  exact naturality_pasting _ _ _ _ _ _ _ _ _ _ hs hp
    (map_square (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c) ht)

private theorem tensor_pullback_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) (K : Etale.DerivedCategoryModule A Y)
    {W W' : Etale.DerivedCategoryModule A X} (b : W ⟶ W') :
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj
          ((comparison A Y).obj K))).map ((comparison A X).map b)) ≫
        (tensorPullbackComparison A q K W').inv =
      (tensorPullbackComparison A q K W).inv ≫ (comparison A X).map
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((Etale.ordinaryFinitePullback A q).obj K)).map b) := by
  have hc := (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} A) ((Etale.ordinaryFinitePullback A q).obj K)).inv.naturality b
  have ht := (((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
    ((pullback A q).app K)).inv).naturality ((comparison A X).map b)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.mapIso_inv, Iso.app_inv] at hc ht
  unfold tensorPullbackComparison tensorComparison
  simp only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv]
  rw [← Category.assoc, ht, Category.assoc, hc]
  simp only [Category.assoc]

private theorem compared_projection_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {q : X ⟶ Y} (c : Compactification q)
    (K : Etale.DerivedCategoryModule A Y)
    {W W' : Etale.DerivedCategoryModule A X} (b : W ⟶ W') :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj ((comparison A Y).obj K)).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          ((comparison A X).map b)) ≫ comparedModuleProjection A c W' K =
      comparedModuleProjection A c W K ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          ((comparison A X).map (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
            ((Etale.ordinaryFinitePullback A q).obj K)).map b)) := by
  unfold comparedModuleProjection moduleProjection
  rw [← Category.assoc, pro_projection_natural, Category.assoc,
    ← Functor.map_comp, tensor_pullback_natural, Functor.map_comp]
  simp only [Category.assoc]

/-- Naturality of the inverse coefficient-first projections in the bundle line.
Source: accepted exponent-transport proof Steps 8 and 11; Stacks 0B65.
(blueprint: lem-pur-coefficient-projection-naturality).
Proof: for fixed K the canonical compact-support projection is natural in W.
For the bundle root map j and i=1 tensor j this says
P_s followed by F(i) = tensor(K,F(j)) followed by P_r. The coefficient-first
convention conjugates the usual naturality square by two signed symmetries;
their own naturality preserves this equation. ordinary_projection identifies
D.pe.inv with P_r and Dprime.pe.inv with P_s. Multiply by their inverses on
both sides to obtain the first displayed equation. On the pro-etale site
apply the same argument to moduleProjection, then use naturality of the fixed
tensorPullbackComparison to pass to comparedModuleProjection coordinates.
pro_projection identifies D.pp.inv and Dprime.pp.inv with these actual maps.
Invert the square to obtain the second equation. The statement involves no
trace equality, integration-arrow formula, adjunction transpose or inverse purity.
-/
theorem integrationCoefficientProjectionNaturality (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) S)
    (D : IntegrationTransposeData (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _) hr S
      (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F K
      (vectorIntegration l E n S r hr d F hS) (vectorSite l E n S r hr d F hS))
    (D' : IntegrationTransposeData (Scheme.finiteTateCoefficient l E n)
      (l ^ (s + 1)) (pow_pos (Fact.out : l.Prime).pos _) hs S
      (by simpa only [Nat.cast_pow] using hS.pow (s + 1)) d F K
      (vectorIntegration l E n S s hs d F hS) (vectorSite l E n S s hs d F hS))
    :
    (integrationLower (Scheme.finiteTateCoefficient l E n) S d F).map
      (integrationTensorTransition l E n S hS r s hrs hr hs d F K).hom ≫
        D.data.pe.hom = D'.data.pe.hom ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) S).obj K).map
        ((integrationLower (Scheme.finiteTateCoefficient l E n) S d F).map
          (integrationVectorTransition l E n S hS r s hrs hr hs d F).hom) ∧
    (integrationProLower (Scheme.finiteTateCoefficient l E n) S d F).map
      ((comparison (Scheme.finiteTateCoefficient l E n) _).map
        (integrationTensorTransition l E n S hS r s hrs hr hs d F K).hom) ≫
      D.data.pp.hom = D'.data.pp.hom ≫
      ((derivedTensor (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) S).obj
        ((comparison (Scheme.finiteTateCoefficient l E n) S).obj K)).map
          ((integrationProLower (Scheme.finiteTateCoefficient l E n) S d F).map
            ((comparison (Scheme.finiteTateCoefficient l E n) _).map
              (integrationVectorTransition l E n S hS r s hrs hr hs d F).hom)) := by
  let A := Scheme.finiteTateCoefficient l E n
  have : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (Etale.vectorIntegration_geometry S d F).1
  have : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
    (Etale.vectorIntegration_geometry S d F).2.1
  let j := integrationVectorTransition l E n S hS r s hrs hr hs d F
  constructor
  · apply inverse_projection_square D'.data.pe D.data.pe
    rw [D'.data.ordinary_projection, D.data.ordinary_projection]
    exact ordinary_projection_natural A (VectorBundleZeroSection.π S d F) K j.hom
  · apply inverse_projection_square D'.data.pp D.data.pp
    rw [eq_of_heq D'.data.pro_projection, eq_of_heq D.data.pro_projection]
    exact compared_projection_natural A
      (Etale.vectorBundlePurityCompactification S d F) K j.hom

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
