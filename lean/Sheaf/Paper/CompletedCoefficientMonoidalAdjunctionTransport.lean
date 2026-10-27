/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.Paper.CompletedCoefficientSystemTransport
import Sheaf.Paper.CompletedCoefficientNormalizedTransport

/-!
# Completed-coefficient monoidal and adjunction transport

Source: Stacks 099I and 099K; blueprint main-20261015,
lem-fix-operation-reduction.proof.md, final paragraph
(blueprint: lem-pur-completed-coefficient-monoidal-adjunction-transport).
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u s i j
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.CompletedCoefficientTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem monoidal_associator_square
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {A B C' : C} {X Y Z : D} (p : X ⟶ F.obj A) (q : Y ⟶ F.obj B)
    (r : Z ⟶ F.obj C') :
    (α_ X Y Z).hom ≫
        (p ⊗ₘ ((q ⊗ₘ r) ≫ Functor.LaxMonoidal.μ F B C')) ≫
        Functor.LaxMonoidal.μ F A (B ⊗ C') =
      (((p ⊗ₘ q) ≫ Functor.LaxMonoidal.μ F A B) ⊗ₘ r) ≫
        Functor.LaxMonoidal.μ F (A ⊗ B) C' ≫ F.map (α_ A B C').hom := by
  have h₁ : p ⊗ₘ ((q ⊗ₘ r) ≫ Functor.LaxMonoidal.μ F B C') =
      (p ⊗ₘ (q ⊗ₘ r)) ≫ (F.obj A ◁ Functor.LaxMonoidal.μ F B C') := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
  have h₂ : (((p ⊗ₘ q) ≫ Functor.LaxMonoidal.μ F A B) ⊗ₘ r) =
      ((p ⊗ₘ q) ⊗ₘ r) ≫ (Functor.LaxMonoidal.μ F A B ▷ F.obj C') := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
  rw [h₁, h₂]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.associativity, ← Category.assoc, ← associator_naturality]
  simp only [Category.assoc]

private theorem monoidal_left_unitor_square
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {A : C} {X : D} (p : X ⟶ F.obj A) :
    (λ_ X).hom ≫ p =
      (Functor.LaxMonoidal.ε F ⊗ₘ p) ≫ Functor.LaxMonoidal.μ F (𝟙_ C) A ≫
        F.map (λ_ A).hom := by
  rw [← leftUnitor_naturality, Functor.LaxMonoidal.left_unitality]
  simp only [← Category.assoc, ← id_tensorHom, ← tensorHom_id,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

private theorem monoidal_right_unitor_square
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {A : C} {X : D} (p : X ⟶ F.obj A) :
    (ρ_ X).hom ≫ p =
      (p ⊗ₘ Functor.LaxMonoidal.ε F) ≫ Functor.LaxMonoidal.μ F A (𝟙_ C) ≫
        F.map (ρ_ A).hom := by
  rw [← rightUnitor_naturality, Functor.LaxMonoidal.right_unitality]
  simp only [← Category.assoc, ← id_tensorHom, ← tensorHom_id,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

private theorem tensor_substitution_square
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {A B A' B' : C} {X Y X' Y' X'' Y'' : D}
    (p : X ⟶ F.obj A) (q : Y ⟶ F.obj B) (r : A ⟶ A') (s : B ⟶ B')
    (x : X ⟶ X') (y : Y ⟶ Y') (x' : X' ⟶ X'') (y' : Y' ⟶ Y'')
    (p' : X'' ⟶ F.obj A') (q' : Y'' ⟶ F.obj B')
    (hp : p ≫ F.map r = x ≫ x' ≫ p') (hq : q ≫ F.map s = y ≫ y' ≫ q') :
    ((p ⊗ₘ q) ≫ Functor.LaxMonoidal.μ F A B) ≫ F.map (r ⊗ₘ s) =
      (x ⊗ₘ y) ≫ (x' ⊗ₘ y') ≫ ((p' ⊗ₘ q') ≫ Functor.LaxMonoidal.μ F A' B') := by
  rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural, ← Category.assoc,
    tensorHom_comp_tensorHom, hp, hq]
  simp only [← Category.assoc, tensorHom_comp_tensorHom]

private theorem natural_iso_substitution_square
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (U : C ⥤ D) (L : D ⥤ E) (R : C ⥤ F) (V : F ⥤ E)
    (b : U ⋙ L ≅ R ⋙ V)
    {A B : C} {X X' X'' : D}
    (p : X ⟶ U.obj A) (p' : X'' ⟶ U.obj B) (r : A ⟶ B)
    (x : X ⟶ X') (x' : X' ⟶ X'')
    (hp : p ≫ U.map r = x ≫ x' ≫ p') :
    (L.map p ≫ b.hom.app A) ≫ V.map (R.map r) =
      L.map x ≫ L.map x' ≫ L.map p' ≫ b.hom.app B := by
  have hn := b.hom.naturality r
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn]
  simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [hp]
  simp only [Category.assoc]

private theorem natural_iso_structural_square
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (U : C ⥤ D) (L : D ⥤ E) (R : C ⥤ F) (V : F ⥤ E)
    (b : U ⋙ L ≅ R ⋙ V)
    {A B : C} {X Y : D} (p : X ⟶ U.obj A) (q : Y ⟶ U.obj B)
    (r : A ⟶ B) (x : X ⟶ Y) (h : x ≫ q = p ≫ U.map r) :
    L.map x ≫ (L.map q ≫ b.hom.app B) =
      (L.map p ≫ b.hom.app A) ≫ V.map (R.map r) := by
  have hn := b.hom.naturality r
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn]
  simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [h]

private theorem braided_square
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) [F.LaxMonoidal]
    (hF : ∀ A B : C, Functor.LaxMonoidal.μ F A B ≫ F.map (β_ A B).hom =
      (β_ (F.obj A) (F.obj B)).hom ≫ Functor.LaxMonoidal.μ F B A)
    {A B : C} {X Y : D} (p : X ⟶ F.obj A) (q : Y ⟶ F.obj B) :
    (β_ X Y).hom ≫ (q ⊗ₘ p) ≫ Functor.LaxMonoidal.μ F B A =
      ((p ⊗ₘ q) ≫ Functor.LaxMonoidal.μ F A B) ≫ F.map (β_ A B).hom := by
  rw [Category.assoc, hF, ← BraidedCategory.braiding_naturality_assoc]

private theorem tensor_structural_square
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {A B A' B' : C} {X Y X' Y' : D}
    (p : X ⟶ F.obj A) (q : Y ⟶ F.obj B) (p' : X' ⟶ F.obj A')
    (q' : Y' ⟶ F.obj B') (r : A ⟶ A') (s : B ⟶ B')
    (x : X ⟶ X') (y : Y ⟶ Y')
    (hp : x ≫ p' = p ≫ F.map r) (hq : y ≫ q' = q ≫ F.map s) :
    (x ⊗ₘ y) ≫ ((p' ⊗ₘ q') ≫ Functor.LaxMonoidal.μ F A' B') =
      ((p ⊗ₘ q) ≫ Functor.LaxMonoidal.μ F A B) ≫ F.map (r ⊗ₘ s) := by
  rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural]
  simp only [← Category.assoc, tensorHom_comp_tensorHom]
  rw [hp, hq]

attribute [local irreducible] completeR IntegralOnSlice.duality
  IntegralOnSlice.completion IntegralOnSlice.completionUnit
  completedIntegralCoefficientSheafUnrestricted HasDerivedCategory.standard constantSheaf
  CategoryTheory.Limits.limit SheafOfModules.monoidalCategory
attribute [local implicit_reducible] valueR valueA Site.restriction
  IntegralOnSlice.Site IntegralOnSlice.siteCategory IntegralOnSlice.topology
  IntegralOnSlice.restrict IntegralOnSlice.ring completedIntegralCommRingSheafUnrestricted

private theorem expression_substitution {S : Type s} {W : S → Scheme.{t}}
    (T : Transport.{t, u, s, i, j} l E W) : ExpressionSubstitutionLaw l E T := by
  intro I J location location' σ a P M
  induction P with
  | input k =>
      change (expressionTransport l E T (σ k) M).hom ≫
          ((T.site (location k)).restriction l E).map (𝟙 _) =
        𝟙 _ ≫ (expressionTransport l E T (σ k) M).hom ≫ 𝟙 _
      simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  | unit a =>
      let := (T.site a).r_tensor.monoidal
      let := (T.site a).a_tensor.monoidal
      let := (T.tensor a).monoidal
      change (Functor.Monoidal.εIso ((T.site a).restriction l E)).hom ≫
          ((T.site a).restriction l E).map (𝟙 _) =
        𝟙 _ ≫ 𝟙 _ ≫ (Functor.Monoidal.εIso ((T.site a).restriction l E)).hom
      simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  | @tensor a P Q hP hQ =>
      let := (T.site a).r_tensor.monoidal
      let := (T.site a).a_tensor.monoidal
      let := (T.tensor a).monoidal
      simpa only [expressionTransport, substitutionR, substitutionA,
        CompletedOperations.Expression.substitute, valueR, valueA, Iso.trans_hom,
        Functor.mapIso_hom, Iso.prod_hom, MonoidalCategory.tensor_map,
        Functor.Monoidal.μIso_hom, Functor.comp_map, Functor.prod'_map,
        Category.assoc] using tensor_substitution_square ((T.site a).restriction l E)
        (A := (valueR l E T (P.substitute σ)).obj M)
        (B := (valueR l E T (Q.substitute σ)).obj M)
        (A' := (valueR l E T P).obj (fun k ↦ (valueR l E T (σ k)).obj M))
        (B' := (valueR l E T Q).obj (fun k ↦ (valueR l E T (σ k)).obj M))
        (expressionTransport l E T (P.substitute σ) M).hom
        (expressionTransport l E T (Q.substitute σ) M).hom
        (substitutionR l E T σ P M).hom (substitutionR l E T σ Q M).hom
        (substitutionA l E T σ P
          (fun k ↦ ((T.site (location' k)).restriction l E).obj (M k))).hom
        (substitutionA l E T σ Q
          (fun k ↦ ((T.site (location' k)).restriction l E).obj (M k))).hom
        ((valueA l E T P).map (fun k ↦ (expressionTransport l E T (σ k) M).hom))
        ((valueA l E T Q).map (fun k ↦ (expressionTransport l E T (σ k) M).hom))
        (expressionTransport l E T P (fun k ↦ (valueR l E T (σ k)).obj M)).hom
        (expressionTransport l E T Q (fun k ↦ (valueR l E T (σ k)).obj M)).hom hP hQ
  | @pullback a b f P hP =>
      exact natural_iso_substitution_square
        ((T.site b).restriction l E) ((T.arrow f).leftA l E)
        ((T.arrow f).leftR l E) ((T.site a).restriction l E) (T.adjunction f).b
        (A := (valueR l E T (P.substitute σ)).obj M)
        (B := (valueR l E T P).obj (fun k ↦ (valueR l E T (σ k)).obj M))
        (expressionTransport l E T (P.substitute σ) M).hom
        (expressionTransport l E T P (fun k ↦ (valueR l E T (σ k)).obj M)).hom
        (substitutionR l E T σ P M).hom
        (substitutionA l E T σ P
          (fun k ↦ ((T.site (location' k)).restriction l E).obj (M k))).hom
        ((valueA l E T P).map (fun k ↦ (expressionTransport l E T (σ k) M).hom)) hP

private theorem expression_structural {S : Type s} {W : S → Scheme.{t}}
    (T : Transport.{t, u, s, i, j} l E W) : ExpressionStructuralLaw l E T := by
  intro I location a P Q α M
  induction α with
  | @associator a P Q R =>
      dsimp only [valueR, valueA, Functor.comp_obj, Functor.prod'_obj,
        MonoidalCategory.tensor_obj, Functor.const_obj_obj]
      let := (T.site a).r_tensor.monoidal
      let := (T.site a).a_tensor.monoidal
      let := (T.tensor a).monoidal
      simpa only [structureA, structureR, expressionTransport, Iso.trans_hom,
        Functor.mapIso_hom, Iso.prod_hom, MonoidalCategory.tensor_map,
        Functor.Monoidal.μIso_hom, Functor.Monoidal.εIso_hom, valueR, valueA, Functor.comp_obj,
        Functor.prod'_obj, MonoidalCategory.tensor_obj, Functor.const_obj_obj,
        Category.assoc] using monoidal_associator_square ((T.site a).restriction l E)
        (A := (valueR l E T P).obj M) (B := (valueR l E T Q).obj M)
        (C' := (valueR l E T R).obj M)
        (expressionTransport l E T P M).hom (expressionTransport l E T Q M).hom
        (expressionTransport l E T R M).hom
  | @leftUnitor a P =>
      dsimp only [valueR, valueA, Functor.comp_obj, Functor.prod'_obj,
        MonoidalCategory.tensor_obj, Functor.const_obj_obj]
      let := (T.site a).r_tensor.monoidal
      let := (T.site a).a_tensor.monoidal
      let := (T.tensor a).monoidal
      simpa only [structureA, structureR, expressionTransport, Iso.trans_hom,
        Functor.mapIso_hom, Iso.prod_hom, MonoidalCategory.tensor_map,
        Functor.Monoidal.μIso_hom, Functor.Monoidal.εIso_hom, valueR, valueA, Functor.comp_obj,
        Functor.prod'_obj, MonoidalCategory.tensor_obj, Functor.const_obj_obj,
        Category.assoc] using monoidal_left_unitor_square ((T.site a).restriction l E)
        (A := (valueR l E T P).obj M)
        (expressionTransport l E T P M).hom
  | @rightUnitor a P =>
      dsimp only [valueR, valueA, Functor.comp_obj, Functor.prod'_obj,
        MonoidalCategory.tensor_obj, Functor.const_obj_obj]
      let := (T.site a).r_tensor.monoidal
      let := (T.site a).a_tensor.monoidal
      let := (T.tensor a).monoidal
      simpa only [structureA, structureR, expressionTransport, Iso.trans_hom,
        Functor.mapIso_hom, Iso.prod_hom, MonoidalCategory.tensor_map,
        Functor.Monoidal.μIso_hom, Functor.Monoidal.εIso_hom, valueR, valueA, Functor.comp_obj,
        Functor.prod'_obj, MonoidalCategory.tensor_obj, Functor.const_obj_obj,
        Category.assoc] using monoidal_right_unitor_square ((T.site a).restriction l E)
        (A := (valueR l E T P).obj M)
        (expressionTransport l E T P M).hom
  | @symmetry a P Q =>
      let := (T.site a).r_tensor.monoidal
      let := (T.site a).a_tensor.monoidal
      let := (T.tensor a).monoidal
      let := (T.site a).r_tensor.symmetric
      let := (T.site a).a_tensor.symmetric
      simpa only [structureA, structureR, expressionTransport, Iso.trans_hom,
        Functor.mapIso_hom, Iso.prod_hom, MonoidalCategory.tensor_map,
        Functor.Monoidal.μIso_hom, Category.assoc] using
          braided_square ((T.site a).restriction l E) (T.tensor a).braided
            (A := (valueR l E T P).obj M) (B := (valueR l E T Q).obj M)
            (expressionTransport l E T P M).hom (expressionTransport l E T Q M).hom
  | composition g f P =>
      have hn := (T.compositionA f g).hom.naturality (expressionTransport l E T P M).hom
      dsimp only [Functor.comp_map] at hn
      simp only [structureA, structureR, expressionTransport, Iso.trans_hom,
        Functor.mapIso_hom, Iso.app_hom, Category.assoc,
        CategoryTheory.Functor.map_comp]
      rw [T.b_composition]
      simpa only [Category.assoc, valueR, valueA, Functor.comp_obj] using congrArg
        (fun k ↦ k ≫ ((T.arrow g).leftA l E).map
            ((T.adjunction f).b.hom.app ((valueR l E T P).obj M)) ≫
          (T.adjunction g).b.hom.app
            (((T.arrow f).leftR l E).obj ((valueR l E T P).obj M))) hn.symm
  | identity P =>
      simp only [structureA, structureR, Iso.refl_hom,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  | @inverse a P Q α hα =>
      dsimp only [structureA, structureR, Iso.symm_hom]
      apply (cancel_epi (structureA l E T α
        (fun k ↦ ((T.site (location k)).restriction l E).obj (M k))).hom).1
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc, hα]
      simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.comp_id]
  | @compose a P Q R α β hα hβ =>
      dsimp only [structureA, structureR, Iso.trans_hom]
      rw [Category.assoc, hβ, ← Category.assoc, hα]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  | @tensor a P Q R V α β hα hβ =>
      let := (T.site a).r_tensor.monoidal
      let := (T.site a).a_tensor.monoidal
      let := (T.tensor a).monoidal
      simpa only [structureA, structureR, expressionTransport, Iso.trans_hom,
        Functor.mapIso_hom, Iso.prod_hom, MonoidalCategory.tensor_map,
        Functor.Monoidal.μIso_hom, Category.assoc] using
          tensor_structural_square ((T.site a).restriction l E)
            (A := (valueR l E T P).obj M) (B := (valueR l E T R).obj M)
            (A' := (valueR l E T Q).obj M) (B' := (valueR l E T V).obj M)
            (expressionTransport l E T P M).hom (expressionTransport l E T R M).hom
            (expressionTransport l E T Q M).hom (expressionTransport l E T V M).hom
            (structureR l E T α M).hom (structureR l E T β M).hom
            (structureA l E T α
              (fun k ↦ ((T.site (location k)).restriction l E).obj (M k))).hom
            (structureA l E T β
              (fun k ↦ ((T.site (location k)).restriction l E).obj (M k))).hom hα hβ
  | @pullback a b f P Q α hα =>
      exact natural_iso_structural_square
        ((T.site b).restriction l E) ((T.arrow f).leftA l E)
        ((T.arrow f).leftR l E) ((T.site a).restriction l E) (T.adjunction f).b
        (A := (valueR l E T P).obj M) (B := (valueR l E T Q).obj M)
        (expressionTransport l E T P M).hom (expressionTransport l E T Q M).hom
        (structureR l E T α M).hom
        (structureA l E T α
          (fun k ↦ ((T.site (location k)).restriction l E).obj (M k))).hom hα

/-- Constant/completed restriction preserves the specified completed tensor and
pullback comparisons, their whole-system substitution and structural maps, and the
actual completed adjunctions, including their counits, Hom bijections and units.
There are no bounds, constructibility or finite Tor-amplitude assumptions.

Source: Stacks Project, algebraization.tex, Tags 099I and 099K; the combined refinement
in node proof steps 1--11; blueprint main-20261015, lem-fix-operation-reduction.proof.md,
final paragraph (blueprint: lem-pur-completed-coefficient-monoidal-adjunction-transport).

Proof: apply the constant/completed equivalence to the DVR and its principal ideal.
Its finite-quotient comparisons identify strict reduction systems and their total
limits, including the augmented units. Restriction preserves flat-term K-flat
representatives. On them the finite tensor comparison is reassociation
(p tensor q) tensor s ↦ (p tensor 1) tensor (q tensor s); its inverse multiplies
the two coefficients. Both commute with every quotient transition. Total limit of
the inverse defines a; its augmentation is the balancing map followed by eta.
The scalar unit x ↦ 1 tensor x similarly gives b on entire pullback towers and
the equation b eta^A = U(eta^R) tau. These formulas descend on all unbounded good
representatives. The normalized coherent-system substitution theorem supplies
iteration, associators, unitors, Koszul symmetry and pullback composition. The same
pure-tensor formulas give tensor/pullback compatibility and monoidality of the
completion units. The pushforward comparison gives the K-injective-normalized kappa
and preservation of complete objects. The ordinary ringed coefficient counit lemma
gives tau U(epsilon_R) = Q_A(kappa) epsilon_A. Form each completed adjunction using
precomposition with its actual completion unit followed by the ordinary Hom
bijection. Its counit satisfies eta epsilon^c = epsilon. Precomposing both routes
of the completed counit square with eta^A reduces their equality to the ordinary
counit square. Cancel eta^A by the reflector Hom bijection into complete U(M).
Naturality of b then identifies the inverse Hom bijections. Evaluate those
bijections on the identity to obtain the unit identity. Induction on the recorded
expression syntax proves the simultaneous-substitution equation for
expressionTransport. Induction on StructuralMap proves its structural equation,
using the braided tensorator, monoidality of b and the normalized composition
square at the respective generators. -/
theorem completedCoefficientMonoidalAdjunctionTransport {S : Type s} (W : S → Scheme.{t})
    (_hl : ∀ (a : S) (x : W a), IsUnit (l : (W a).residueField x)) :
    ∃ T : Transport.{t, u, s, i, j} l E W,
      ExpressionSystemLaw l E T ∧ ExpressionSystemStructuralLaw l E T ∧
        ExpressionSubstitutionLaw l E T ∧ ExpressionStructuralLaw l E T := by
  obtain ⟨T, hS, hT⟩ := completedCoefficientNormalizedTransport.{t, u, s, i, j} l E W _hl
  exact ⟨T, hS, hT, expression_substitution l E T,
    expression_structural l E T⟩

end WeilConjectures.CompletedCoefficientTransport
