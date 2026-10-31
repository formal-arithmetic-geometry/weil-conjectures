/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.OpenInterchangeReduction.OpenInterchangeReductionData
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares
import WeilConjectures.SixFunctors.GeneratorReduction.CanonicalOpenReductionIsIso

/-! # The coefficient square for cartesian open base change
Source: the open-adjunction and clopen expansion of the coherence proof.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction
namespace WeilConjectures.OpenInterchangeReduction
-- Keep the derived constructions behind their functorial APIs during this proof.
attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  IntegralSystemRealization.ringedPullComp

private theorem paste_iso_squares {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) {X₀ X₁ X₂ X₃ : C} {Y₀ Z₀ Y₁ Y₂ Z₃ Y₃ : D}
    (a : X₁ ⟶ X₀) (ai : X₀ ⟶ X₁) (b : X₂ ⟶ X₃) (e : X₁ ⟶ X₂)
    (a' : Y₁ ⟶ Y₀) (ai' : Y₀ ⟶ Y₁) (b' : Y₂ ⟶ Y₃) (e' : Y₁ ⟶ Y₂)
    (q₀ : R.obj X₀ ⟶ Z₀) (r₀ : Z₀ ⟶ Y₀) (q₁ : R.obj X₁ ⟶ Y₁)
    (q₂ : R.obj X₂ ⟶ Y₂) (q₃ : R.obj X₃ ⟶ Z₃) (r₃ : Z₃ ⟶ Y₃)
    (ha : R.map a ≫ q₀ ≫ r₀ = q₁ ≫ a')
    (hb : R.map b ≫ q₃ ≫ r₃ = q₂ ≫ b')
    (he : R.map e ≫ q₂ = q₁ ≫ e') (hia : ai ≫ a = 𝟙 _) (hia' : a' ≫ ai' = 𝟙 _) :
    R.map ((ai ≫ e) ≫ b) ≫ q₃ ≫ r₃ = q₀ ≫ r₀ ≫ ((ai' ≫ e') ≫ b') := by
  have h := congrArg (fun f ↦ R.map ai ≫ f ≫ ai') ha
  simp only [← R.map_comp_assoc, hia, R.map_id, CategoryTheory.Category.id_comp,
    CategoryTheory.Category.assoc, hia', CategoryTheory.Category.comp_id] at h
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Category.assoc]
  rw [hb, reassoc_of% he, ← reassoc_of% h]

open IntegralSystemRealization in
private theorem pull_congr_reduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : GeneratorReduction.Operations l E) {X Y : Scheme.{u}}
    {f g : X ⟶ Y} (h : f = g) (K : Integral l E Y) :
    (calculus l E X).reduction.map
        (eqToHom (Functor.congr_obj (congrArg (ringedPull l E) h) K)) ≫
        (o.realization.reductionPull g).hom.app K =
      (o.realization.reductionPull f).hom.app K ≫
        (eqToHom (Functor.congr_obj (congrArg (pull l E) h)
          ((calculus l E Y).reduction.obj K))) := by
  subst g
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id,
    CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id]

open IntegralSystemRealization in
private theorem pull_square_reduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : GeneratorReduction.Operations l E) {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (h : a ≫ j = j' ≫ g) (K : Integral l E X) :
    (calculus l E U').reduction.map ((ringedSquare l E a j' j g h).inv.app K) ≫
        (o.realization.reductionPull j').hom.app ((ringedPull l E g).obj K) ≫
        (pull l E j').map ((o.realization.reductionPull g).hom.app K) =
      (o.realization.reductionPull a).hom.app ((ringedPull l E j).obj K) ≫
        (pull l E a).map ((o.realization.reductionPull j).hom.app K) ≫
        (o.composition.square l E a j' j g h).inv.app ((calculus l E X).reduction.obj K) := by
  have hA := canonicalReductionPullComposition l E o.system o.realization o.composition a j K
  have hB := canonicalReductionPullComposition l E o.system o.realization o.composition j' g K
  have hC := pull_congr_reduction l E o (f := a ≫ j) (g := j' ≫ g) h K
  have hp := paste_iso_squares (C := Integral l E U') (D := System l E U')
    (calculus l E U').reduction
    ((ringedPullComp l E a j).hom.app K) ((ringedPullComp l E a j).inv.app K)
    ((ringedPullComp l E j' g).hom.app K)
    _
    ((o.composition.pullComp a j).hom.app ((calculus l E X).reduction.obj K))
    ((o.composition.pullComp a j).inv.app ((calculus l E X).reduction.obj K))
    ((o.composition.pullComp j' g).hom.app ((calculus l E X).reduction.obj K))
    _
    ((o.realization.reductionPull a).hom.app ((ringedPull l E j).obj K))
    ((pull l E a).map ((o.realization.reductionPull j).hom.app K))
    ((o.realization.reductionPull (a ≫ j)).hom.app K)
    ((o.realization.reductionPull (j' ≫ g)).hom.app K)
    ((o.realization.reductionPull j').hom.app ((ringedPull l E g).obj K))
    ((pull l E j').map ((o.realization.reductionPull g).hom.app K)) hA hB hC
    ((ringedPullComp l E a j).inv_hom_id_app K)
    ((o.composition.pullComp a j).hom_inv_id_app _)
  simpa only [ringedSquare, Compositors.square, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, eqToIso.inv, eqToHom_app, Functor.comp_obj,
    CategoryTheory.Category.assoc] using hp

private theorem beta_mate_square
    {A B A' B' C D C' D' : Type*}
    [Category A] [Category B] [Category A'] [Category B']
    [Category C] [Category D] [Category C'] [Category D']
    {L : A ⥤ B} {P : B ⥤ A} {L' : A' ⥤ B'} {P' : B' ⥤ A'}
    {J : C ⥤ D} {Q : D ⥤ C} {J' : C' ⥤ D'} {Q' : D' ⥤ C'}
    {R₀ : A ⥤ C} {R₁ : B ⥤ D} {R₂ : A' ⥤ C'} {R₃ : B' ⥤ D'}
    {F : B ⥤ B'} {H : A ⥤ A'} {G : D ⥤ D'} {T : C ⥤ C'}
    (a : L ⊣ P) (a' : L' ⊣ P') (b : J ⊣ Q) (b' : J' ⊣ Q')
    (χ : P ⋙ R₀ ⟶ R₁ ⋙ Q) (χ' : P' ⋙ R₂ ⟶ R₃ ⋙ Q')
    (ξ : H ⋙ R₂ ⟶ R₀ ⋙ T) (ζ : F ⋙ R₃ ⟶ R₁ ⋙ G)
    (μ : R₀ ⋙ J ⟶ L ⋙ R₁) (ν : R₂ ⋙ J' ⟶ L' ⋙ R₃)
    (θ : F ⋙ P' ≅ P ⋙ H) (τ : G ⋙ Q' ≅ Q ⋙ T)
    (β : L ⋙ F ≅ H ⋙ L') (δ : J ⋙ G ≅ T ⋙ J')
    (hμ : ∀ X, R₀.map (a.unit.app X) ≫ χ.app (L.obj X) =
      b.unit.app (R₀.obj X) ≫ Q.map (μ.app X))
    (hν : ∀ X, R₂.map (a'.unit.app X) ≫ χ'.app (L'.obj X) =
      b'.unit.app (R₂.obj X) ≫ Q'.map (ν.app X))
    (hθ : ∀ X, R₂.map (θ.inv.app X) ≫ χ'.app (F.obj X) ≫ Q'.map (ζ.app X) =
      ξ.app (P.obj X) ≫ T.map (χ.app X) ≫ τ.inv.app (R₁.obj X))
    (hβ : ∀ X, a'.unit.app (H.obj X) ≫ P'.map (β.inv.app X) =
      H.map (a.unit.app X) ≫ θ.inv.app (L.obj X))
    (hδ : ∀ X, b'.unit.app (T.obj X) ≫ Q'.map (δ.inv.app X) =
      T.map (b.unit.app X) ≫ τ.inv.app (J.obj X)) (X : A) :
    J'.map (ξ.app X) ≫ δ.inv.app (R₀.obj X) ≫ G.map (μ.app X) =
      ν.app (H.obj X) ≫ R₃.map (β.inv.app X) ≫ ζ.app (L.obj X) := by
  apply (b'.homEquiv _ _).injective
  calc
    _ = ξ.app X ≫ T.map (b.unit.app (R₀.obj X)) ≫
        τ.inv.app (J.obj (R₀.obj X)) ≫ Q'.map (G.map (μ.app X)) := by
      rw [← CategoryTheory.Category.assoc, b'.homEquiv_naturality_right,
        b'.homEquiv_naturality_left]
      simp only [Adjunction.homEquiv_unit, CategoryTheory.Category.assoc,
        CategoryTheory.Functor.comp_obj]
      simpa only [CategoryTheory.Category.assoc] using
        congrArg (fun f ↦ ξ.app X ≫ f ≫ Q'.map (G.map (μ.app X))) (hδ (R₀.obj X))
    _ = ξ.app X ≫ T.map (b.unit.app (R₀.obj X) ≫ Q.map (μ.app X)) ≫
        τ.inv.app (R₁.obj (L.obj X)) := by
      have hn := τ.inv.naturality (μ.app X)
      dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj] at hn
      simp only [T.map_comp, CategoryTheory.Category.assoc]
      rw [← hn]
    _ = R₂.map (H.map (a.unit.app X)) ≫ ξ.app (P.obj (L.obj X)) ≫
        T.map (χ.app (L.obj X)) ≫ τ.inv.app (R₁.obj (L.obj X)) := by
      have hn := ξ.naturality (a.unit.app X)
      dsimp only [CategoryTheory.Functor.comp_map] at hn
      simp only [← hμ, T.map_comp, CategoryTheory.Category.assoc]
      rw [← reassoc_of% hn]
    _ = R₂.map (H.map (a.unit.app X)) ≫ R₂.map (θ.inv.app (L.obj X)) ≫
        χ'.app (F.obj (L.obj X)) ≫ Q'.map (ζ.app (L.obj X)) := by
      rw [hθ]
    _ = R₂.map (a'.unit.app (H.obj X)) ≫
        R₂.map (P'.map (β.inv.app X)) ≫ χ'.app (F.obj (L.obj X)) ≫
        Q'.map (ζ.app (L.obj X)) := by
      rw [← R₂.map_comp_assoc, ← hβ, R₂.map_comp]
      simp only [CategoryTheory.Category.assoc]
    _ = R₂.map (a'.unit.app (H.obj X)) ≫ χ'.app (L'.obj (H.obj X)) ≫
        Q'.map (R₃.map (β.inv.app X)) ≫ Q'.map (ζ.app (L.obj X)) := by
      have hn := χ'.naturality (β.inv.app X)
      dsimp only [CategoryTheory.Functor.comp_map] at hn
      rw [reassoc_of% hn]
    _ = _ := by
      simpa only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.comp_obj, CategoryTheory.Category.assoc] using
        congrArg (fun f ↦ f ≫ Q'.map (R₃.map (β.inv.app X)) ≫
          Q'.map (ζ.app (L.obj X))) (hν (H.obj X))

private theorem cancel_coefficient_isos {C D : Type*} [Category C] [Category D]
    [CategoryTheory.Limits.HasZeroMorphisms C] [CategoryTheory.Limits.HasZeroMorphisms D]
    (F : C ⥤ D) {X Y : C} (a : X ⟶ Y) [IsIso a]
    {V W Z T : D} (b : V ⟶ W) [IsIso b]
    (f₁ : V ⟶ Z) (f₂ : Z ⟶ F.obj X) (g₁ : W ⟶ T) (g₂ : T ⟶ F.obj Y)
    (h : f₁ ≫ f₂ ≫ F.map a = b ≫ g₁ ≫ g₂) :
    inverseOrZero b ≫ f₁ ≫ f₂ = g₁ ≫ g₂ ≫ F.map (inverseOrZero a) := by
  rw [GeneratorReduction.inverseOrZero_eq_inv, GeneratorReduction.inverseOrZero_eq_inv,
    CategoryTheory.Functor.map_inv]
  apply (cancel_epi b).1
  apply (cancel_mono (F.map a)).1
  simpa only [CategoryTheory.Category.assoc, IsIso.hom_inv_id_assoc,
    IsIso.inv_hom_id, CategoryTheory.Category.comp_id] using h

private theorem beta_inverse_mate_square
    {A B A' B' C D C' D' : Type*}
    [Category A] [Category B] [Category A'] [Category B']
    [Category C] [Category D] [Category C'] [Category D']
    [CategoryTheory.Limits.HasZeroMorphisms D]
    [CategoryTheory.Limits.HasZeroMorphisms D']
    {L : A ⥤ B} {P : B ⥤ A} {L' : A' ⥤ B'} {P' : B' ⥤ A'}
    {J : C ⥤ D} {Q : D ⥤ C} {J' : C' ⥤ D'} {Q' : D' ⥤ C'}
    {R₀ : A ⥤ C} {R₁ : B ⥤ D} {R₂ : A' ⥤ C'} {R₃ : B' ⥤ D'}
    {F : B ⥤ B'} {H : A ⥤ A'} {G : D ⥤ D'} {T : C ⥤ C'}
    (a : L ⊣ P) (a' : L' ⊣ P') (b : J ⊣ Q) (b' : J' ⊣ Q')
    (χ : P ⋙ R₀ ⟶ R₁ ⋙ Q) (χ' : P' ⋙ R₂ ⟶ R₃ ⋙ Q')
    (ξ : H ⋙ R₂ ⟶ R₀ ⋙ T) (ζ : F ⋙ R₃ ⟶ R₁ ⋙ G)
    (θ : F ⋙ P' ≅ P ⋙ H) (τ : G ⋙ Q' ≅ Q ⋙ T)
    (β : L ⋙ F ≅ H ⋙ L') (δ : J ⋙ G ≅ T ⋙ J')
    (hθ : ∀ X, R₂.map (θ.inv.app X) ≫ χ'.app (F.obj X) ≫ Q'.map (ζ.app X) =
      ξ.app (P.obj X) ≫ T.map (χ.app X) ≫ τ.inv.app (R₁.obj X))
    (hβ : ∀ X, (a'.homEquiv _ _) (β.inv.app X) =
      H.map (a.unit.app X) ≫ θ.inv.app (L.obj X))
    (hδ : ∀ X, (b'.homEquiv _ _) (δ.inv.app X) =
      T.map (b.unit.app X) ≫ τ.inv.app (J.obj X)) (X : A)
    (hμ : IsIso (((mateEquiv (G := R₀) (H := R₁) a b).symm χ).natTrans.app X))
    (hν : IsIso (((mateEquiv (G := R₂) (H := R₃) a' b').symm χ').natTrans.app (H.obj X))) :
    inverseOrZero (((mateEquiv (G := R₂) (H := R₃) a' b').symm χ').natTrans.app (H.obj X)) ≫
        J'.map (ξ.app X) ≫ δ.inv.app (R₀.obj X) =
      R₃.map (β.inv.app X) ≫ ζ.app (L.obj X) ≫
        G.map (inverseOrZero (((mateEquiv (G := R₀) (H := R₁) a b).symm χ).natTrans.app X)) := by
  let := hμ
  let := hν
  exact cancel_coefficient_isos G
    (((mateEquiv (G := R₀) (H := R₁) a b).symm χ).natTrans.app X)
    (((mateEquiv (G := R₂) (H := R₃) a' b').symm χ').natTrans.app (H.obj X))
    (J'.map (ξ.app X)) (δ.inv.app (R₀.obj X))
    (R₃.map (β.inv.app X)) (ζ.app (L.obj X))
    (beta_mate_square a a' b b' χ χ' ξ ζ _ _ θ τ β δ
      (fun M ↦ unit_mateEquiv_symm a b χ M)
      (fun M ↦ unit_mateEquiv_symm a' b' χ' M) hθ
      (fun M ↦ by simpa only [Adjunction.homEquiv_unit] using hβ M)
      (fun M ↦ by simpa only [Adjunction.homEquiv_unit] using hδ M) X)

private theorem forward_of_inverse_square {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) {X Y : C} {M N : D} (a : X ≅ Y) (b : M ≅ N)
    (q : R.obj X ⟶ M) (r : R.obj Y ⟶ N)
    (h : r ≫ b.inv = R.map a.inv ≫ q) : q ≫ b.hom = R.map a.hom ≫ r := by
  apply (cancel_mono b.inv).1
  simp only [CategoryTheory.Category.assoc, Iso.hom_inv_id, CategoryTheory.Category.comp_id]
  rw [h]
  simp only [← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, CategoryTheory.Category.id_comp]

open IntegralSystemRealization in
private theorem openReduction_as_mate (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : GeneratorReduction.Operations l E) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    o.realization.openReduction l E j =
      ((mateEquiv (G := (calculus l E U).reduction)
        (H := (calculus l E X).reduction)
        (ringedOpenAdj l E j) (o.system.extension j).adj).symm
        (o.realization.reductionPull j).hom).natTrans := by
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
open IntegralSystemRealization in
-- Parameterizing the restriction squares avoids expanding their equality transports.
private theorem beta_reduction_with_squares (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : GeneratorReduction.Operations l E) {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (h : a ≫ j = j' ≫ g) (sq : IsPullback a j' j g) (K : Integral l E U)
    (θR : ringedPull l E g ⋙ ringedPull l E j' ≅ ringedPull l E j ⋙ ringedPull l E a)
    (θS : pull l E g ⋙ pull l E j' ≅ pull l E j ⋙ pull l E a)
    (hθ : ∀ M : Integral l E X,
      (calculus l E U').reduction.map (θR.inv.app M) ≫
          (o.realization.reductionPull j').hom.app ((ringedPull l E g).obj M) ≫
          (pull l E j').map ((o.realization.reductionPull g).hom.app M) =
        (o.realization.reductionPull a).hom.app ((ringedPull l E j).obj M) ≫
          (pull l E a).map ((o.realization.reductionPull j).hom.app M) ≫
          θS.inv.app ((calculus l E X).reduction.obj M))
    (hβ : ∀ M : Integral l E U,
      (ringedOpenAdj l E j').homEquiv _ _ ((o.ringedOpens.beta a j' j g h sq).inv.app M) =
        (ringedPull l E a).map ((ringedOpenAdj l E j).unit.app M) ≫
          θR.inv.app ((ringedOpen l E j).obj M))
    (hδ : ∀ M : System l E U,
      (o.system.extension j').adj.homEquiv _ _ ((o.opens.beta a j' j g h sq).inv.app M) =
        (pull l E a).map ((o.system.extension j).adj.unit.app M) ≫
          θS.inv.app ((Operations.shriek l E o.system j).obj M)) :
    inverseOrZero ((o.realization.openReduction l E j').app ((ringedPull l E a).obj K)) ≫
        (Operations.shriek l E o.system j').map ((o.realization.reductionPull a).hom.app K) ≫
        (o.opens.beta a j' j g h sq).inv.app ((calculus l E U).reduction.obj K) =
      (calculus l E X').reduction.map ((o.ringedOpens.beta a j' j g h sq).inv.app K) ≫
        (o.realization.reductionPull g).hom.app ((ringedOpen l E j).obj K) ≫
        (pull l E g).map (inverseOrZero ((o.realization.openReduction l E j).app K)) := by
  have hμ := canonicalOpenReduction_isIso l E o j K
  have hν := canonicalOpenReduction_isIso l E o j' ((ringedPull l E a).obj K)
  simp only [openReduction_as_mate] at hμ hν ⊢
  exact beta_inverse_mate_square
    (A := Integral l E U) (B := Integral l E X)
    (A' := Integral l E U') (B' := Integral l E X')
    (C := System l E U) (D := System l E X)
    (C' := System l E U') (D' := System l E X')
    (L := ringedOpen l E j) (P := ringedPull l E j)
    (L' := ringedOpen l E j') (P' := ringedPull l E j')
    (J := Operations.shriek l E o.system j) (Q := pull l E j)
    (J' := Operations.shriek l E o.system j') (Q' := pull l E j')
    (F := ringedPull l E g) (H := ringedPull l E a)
    (G := pull l E g) (T := pull l E a)
    (R₀ := (calculus l E U).reduction) (R₁ := (calculus l E X).reduction)
    (R₂ := (calculus l E U').reduction) (R₃ := (calculus l E X').reduction)
    (ringedOpenAdj l E j) (ringedOpenAdj l E j')
    (o.system.extension j).adj (o.system.extension j').adj
    (o.realization.reductionPull j).hom (o.realization.reductionPull j').hom
    (o.realization.reductionPull a).hom (o.realization.reductionPull g).hom
    θR θS
    (o.ringedOpens.beta a j' j g h sq) (o.opens.beta a j' j g h sq)
    hθ hβ hδ K hμ hν

open IntegralSystemRealization in
private theorem beta_reduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : GeneratorReduction.Operations l E) {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (h : a ≫ j = j' ≫ g) (sq : IsPullback a j' j g) (K : Integral l E U) :
    inverseOrZero ((o.realization.openReduction l E j').app ((ringedPull l E a).obj K)) ≫
        (Operations.shriek l E o.system j').map ((o.realization.reductionPull a).hom.app K) ≫
        (o.opens.beta a j' j g h sq).inv.app ((calculus l E U).reduction.obj K) =
      (calculus l E X').reduction.map ((o.ringedOpens.beta a j' j g h sq).inv.app K) ≫
        (o.realization.reductionPull g).hom.app ((ringedOpen l E j).obj K) ≫
        (pull l E g).map (inverseOrZero ((o.realization.openReduction l E j).app K)) := by
  exact beta_reduction_with_squares l E o a j' j g h sq K
    (ringedSquare l E a j' j g h) (o.composition.square l E a j' j g h)
    (pull_square_reduction l E o a j' j g h)
    (fun M ↦ o.ringedOpens.beta_transpose a j' j g h sq M)
    (fun M ↦ o.opens.beta_transpose a j' j g h sq M)

open IntegralSystemRealization in
private theorem ordinary_beta_inverse (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : GeneratorReduction.Operations l E)
    {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)
    {a b c d : S}
    (gU : W a ⟶ W b) (j' : W a ⟶ W c) (j : W b ⟶ W d) (g : W c ⟶ W d)
    (h : gU ≫ j = j' ≫ g) (sq : IsPullback gU j' j g)
    (hgU : IsSeparated gU) (htgU : LocallyOfFiniteType gU) (hqgU : QuasiCompact gU)
    (hg : IsSeparated g) (htg : LocallyOfFiniteType g) (hqg : QuasiCompact g)
    [hj' : IsOpenImmersion j'] (hqj' : QuasiCompact j')
    [hj : IsOpenImmersion j] (hqj : QuasiCompact j) (B : Word W location b)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    (Word.open j' hj' hqj' (Word.pull gU hgU htgU hqgU B)).ordinaryR l E o K ≫
        (o.opens.beta gU j' j g h sq).inv.app
          (B.systemValue l E W location o (inputReduction l E W location K)) =
      (calculus l E (W c)).reduction.map
          ((o.ringedOpens.beta gU j' j g h sq).inv.app
            (B.ringedValue l E W location o K)) ≫
        (Word.pull g hg htg hqg (Word.open j hj hqj B)).ordinaryR l E o K := by
  let := hj
  let := hj'
  have hn := (o.opens.beta gU j' j g h sq).inv.naturality (B.ordinaryR l E o K)
  dsimp only [CategoryTheory.Functor.comp_map] at hn
  dsimp only [Word.ordinaryR, Word.ringedValue]
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Category.assoc]
  erw [hn]
  have hb := beta_reduction l E o gU j' j g h sq (B.ringedValue l E W location o K)
  erw [reassoc_of% hb]

/-- The coefficient square for cartesian open base change.
Source: blueprint `fix-prop-coherence.proof.md`, open-adjunction/clopen expansion
(blueprint: lem-sf-open-base-change-reduction-square).
Proof: Let theta be the square of the two restriction compositors. The inverse beta
is the open adjunct of inverse theta after inverse image of the open unit.
Expand this adjunct as open extension of that composite followed by the open
counit. Canonical pullback composition gives the restriction-square comparison,
and the open coefficient maps are the specified adjunction mates. Naturality
lets one whisker these squares through the finite contexts. Paste them to obtain
the square for inverse beta. Both beta maps are isomorphisms, and the recursive
completion maps at both endpoints are invertible on the stated short-word domain.
Cancel these maps and invert the square. The transpose normalizations of the
system and independently ringed beta identify the resulting arrows with the maps
in this statement. The ordinary mate calculation requires no amplitude hypotheses;
the given support and Tor windows enter only in the endpoint completion argument. -/
theorem openBaseChangeReductionSquare
    {D : FiniteFieldDatum.{u}} (Cf : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic Cf.l) E]
    [FiniteDimensional (Padic Cf.l) E] (o : Operations Cf.l E)
    (hStructural : StructuralSquares.{u, s, i} Cf.l E D o)
    {S : Type s} (W : S → Scheme.{u}) (hW : FiniteTypeFamily W D.k)
    {I : Type i} (location : I → S)
    {a b c d : S}
      (gU : W a ⟶ W b) (j' : W a ⟶ W c) (j : W b ⟶ W d) (g : W c ⟶ W d)
      (h : gU ≫ j = j' ≫ g) (sq : IsPullback gU j' j g)
      (hgU : IsSeparated gU) (htgU : LocallyOfFiniteType gU) (hqgU : QuasiCompact gU)
      (hg : IsSeparated g) (htg : LocallyOfFiniteType g) (hqg : QuasiCompact g)
      (hj' : IsOpenImmersion j') (hqj' : QuasiCompact j')
      (hj : IsOpenImmersion j) (hqj : QuasiCompact j) (B : Word W location b)
    (hSourceLength : (Word.pull g hg htg hqg (Word.open j hj hqj B)).length ≤ 3)
    (hTargetLength : (Word.open j' hj' hqj' (Word.pull gU hgU htgU hqgU B)).length ≤ 3)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource Cf.l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hInputs : ∀ k : I, Admissible Cf.l E
      (IntegralSystemRealization.calculus Cf.l E (W (location k))) (K k)
      lo hi torLo torHi)
    (hSource : Word.admissible Cf.l E W location o K lo hi torLo torHi
      (Word.pull g hg htg hqg
      (Word.open j hj hqj B)))
    (hTarget : Word.admissible Cf.l E W location o K lo hi torLo torHi
      (Word.open j' hj' hqj'
      (Word.pull gU hgU htgU hqgU B)))
    (hGenerator : GeneratorKind.admissible Cf.l E W location o K lo hi torLo torHi
      (GeneratorKind.openBaseChange gU j' j g h sq hgU htgU hqgU hg htg hqg hj' hqj' hj hqj B)) :
    Assertion Cf.l E W location o K
      (GeneratorKind.openBaseChange gU j' j g h sq hgU htgU hqgU hg htg hqg hj' hqj' hj hqj B) := by
  have _ := @hStructural
  have _ := @hW
  have _ := hGenerator
  let := hj
  let := hj'
  apply GeneratorReduction.assertion_of_ordinary_square Cf.l E o K lo hi torLo torHi
    hInputs (.openBaseChange gU j' j g h sq hgU htgU hqgU hg htg hqg hj' hqj' hj hqj B)
    hSourceLength hTargetLength hSource hTarget
  have hInv := ordinary_beta_inverse Cf.l E o W location gU j' j g h sq
    hgU htgU hqgU hg htg hqg hqj' hqj B K
  dsimp only [GeneratorKind.systemMap, GeneratorKind.ringedMap]
  exact forward_of_inverse_square
    (C := IntegralSystemRealization.Integral Cf.l E (W c))
    (D := IntegralSystemRealization.System Cf.l E (W c))
    (IntegralSystemRealization.calculus Cf.l E (W c)).reduction
    ((o.ringedOpens.beta gU j' j g h sq).app (B.ringedValue Cf.l E W location o K))
    ((o.opens.beta gU j' j g h sq).app
      (B.systemValue Cf.l E W location o (inputReduction Cf.l E W location K))) _ _ hInv
end WeilConjectures.OpenInterchangeReduction
