/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HorizontalDualityMateComparisons
public import WeilConjectures.AlgebraicGeometry.QCohInverseBaseChangeMate
public import WeilConjectures.AlgebraicGeometry.HorizontalOrdinaryForwardFixedPasting

/-! # Ordinary inverse geometric pasting with fixed comparisons

## References

* Stacks Project, Tags 0ATM and 0ATR
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry

private theorem inverse_pasting
    {C : Type*} [Category* C] {W V M U T : C}
    (β : U ⟶ T) (γ : W ⟶ V) (βi : T ⟶ U) (γi : V ⟶ W)
    (A : V ⟶ M) (t : M ⟶ T) (b : W ⟶ U)
    (hp : b ≫ β = γ ≫ A ≫ t)
    (hβ : β ≫ βi = 𝟙 U) (hγ : γi ≫ γ = 𝟙 V) :
    A ≫ t ≫ βi = γi ≫ b := by
  calc
    A ≫ t ≫ βi = (γi ≫ γ) ≫ A ≫ t ≫ βi := by rw [hγ, Category.id_comp]
    _ = γi ≫ (γ ≫ A ≫ t) ≫ βi := by simp only [Category.assoc]
    _ = γi ≫ (b ≫ β) ≫ βi := by rw [hp]
    _ = γi ≫ b := by simp only [Category.assoc, hβ, Category.comp_id]

private theorem id_hComp_app
    {C D P Q T : Type*}
    [Category* C] [Category* D] [Category* P] [Category* Q] [Category* T]
    {U : C ⥤ P} {F : C ⥤ D} {R : P ⥤ T} {B : D ⥤ T}
    {L : P ⥤ Q} {S : Q ⥤ T}
    (τ : TwoSquare U F R B) (k : TwoSquare L R S (𝟭 T)) (E : C) :
    (τ ≫ₕ k).app E = k.app (U.obj E) ≫ τ.app E := by
  rw [TwoSquare.hComp_app]
  rfl

private theorem cancel_inverse_squares
    {C D P Q T : Type*}
    [Category* C] [Category* D] [Category* P] [Category* Q] [Category* T]
    {U : C ⥤ P} {V : C ⥤ Q} {F : C ⥤ D}
    {R : P ⥤ T} {S : Q ⥤ T} {B H : D ⥤ T} {L : P ⥤ Q}
    (s : V ≅ U ⋙ L) (b : H ≅ B)
    (τ : TwoSquare U F R B) (σ : TwoSquare V F S H)
    (k : TwoSquare L R S (𝟭 T))
    (β : F ⋙ B ⟶ U ⋙ R) (E : C)
    (γ : H.obj (F.obj E) ⟶ S.obj (V.obj E))
    (hp : b.hom.app (F.obj E) ≫ β.app E =
      γ ≫ S.map (s.hom.app E) ≫ k.app (U.obj E))
    (hβ : β.app E ≫ τ.app E = 𝟙 _)
    (hγ : σ.app E ≫ γ = 𝟙 _) :
    S.map (s.hom.app E) ≫ (τ ≫ₕ k).app E =
      σ.app E ≫ b.hom.app (F.obj E) := by
  rw [id_hComp_app]
  exact inverse_pasting _ _ _ _ _ _ _ hp hβ hγ

private theorem qc_inverse_cancel
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : S ⟶ Y)
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj)) (E : schemeDerivedQCohCategory X) :
    (qcBaseChange f g).app E ≫ (qcInverseBaseChange f g hβ).app E = 𝟙 _ ∧
      (qcInverseBaseChange f g hβ).app E ≫ (qcBaseChange f g).app E = 𝟙 _ := by
  classical
  have : ∀ E, IsIso ((qcBaseChange f g).app E) := fun E ↦
    @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
      (schemeDerivedQCohProperty S).fullyFaithfulι _ _ ((qcBaseChange f g).app E) (hβ E)
  have : IsIso (qcBaseChange f g) := NatIso.isIso_of_isIso_app _
  simp only [qcInverseBaseChange, NatIso.isIso_inv_app]
  exact ⟨IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩

/-- The ordinary inverse geometric pasting equation, before any supplied right
adjoints to the direct images of the outer or iterated projection are introduced.
(Stacks, Tags 0ATM and 0ATR) -/
theorem horizontal_ordinary_inverse_fixed_pasting
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (h : Z ⟶ Y')
    (hβh : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f (h ≫ g)) (h ≫ g)
        (pullback.fst f (h ≫ g)) pullback.condition E.obj))
    (hβ₂ : ∀ E : schemeDerivedQCohCategory (pullback f g),
      IsIso (schemeDerivedBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) h) h
        (pullback.fst (pullback.snd f g) h) pullback.condition E.obj)) :
    letI : QuasiSeparatedSpace (pullback f (h ≫ g) : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))
    letI : QuasiSeparatedSpace (pullback (pullback.snd f g) h : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)
    let s := horizontalOrdinaryUpperComparison f g h
    let e := pullbackLeftPullbackSndIso f g h
    let q := pullback.snd f (h ≫ g)
    let p := pullback.snd (pullback.snd f g) h
    let k := horizontalOrdinaryTransfer e q p (pullbackLeftPullbackSndIso_hom_snd f g h)
    let τ := qcInverseBaseChange f (h ≫ g) hβh
    let σ := qcInverseBaseChange f g hβ ≫ₕ
      @qcInverseBaseChange _ (pullback f g) Y' Z _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _ h hβ₂
    ∀ E : schemeDerivedQCohCategory X,
      (qcDirectImage (pullback.snd (pullback.snd f g) h)).map
          (s.hom.app E) ≫ (τ ≫ₕ k).app E =
        σ.app E ≫ (horizontalOrdinaryBaseComparison g h).hom.app
          ((qcDirectImage f).obj E) := by
  set_option backward.isDefEq.respectTransparency true in
   set_option backward.isDefEq.respectTransparency.types false in
    classical
    let : QuasiSeparatedSpace (pullback f (h ≫ g) : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))
    let : QuasiSeparatedSpace (pullback (pullback.snd f g) h : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)
    let : QuasiSeparatedSpace (pullback f g : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)
    intro s e q p k τ σ E
    let γ := (qcPullback h).map ((qcBaseChange f g).app E) ≫
      (@qcBaseChange _ (pullback f g) Y' Z _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _ h).app ((qcPullback (pullback.fst f g)).obj E)
    have hb := (qc_inverse_cancel f (h ≫ g) hβh E).1
    have hg : σ.app E ≫ γ = 𝟙 _ := by
      have hs := (qc_inverse_cancel f g hβ E).2
      have hi := (qc_inverse_cancel (pullback.snd f g) h hβ₂
        ((qcPullback (pullback.fst f g)).obj E)).2
      dsimp only [σ, γ]
      rw [TwoSquare.hComp_app]
      simp only [Category.assoc]
      rw [← (qcPullback h).map_comp_assoc, hs]
      erw [(qcPullback h).map_id]
      rw [Category.id_comp]
      exact hi
    exact cancel_inverse_squares s (horizontalOrdinaryBaseComparison g h) τ σ k
      (qcBaseChange f (h ≫ g)) E γ
      (horizontal_ordinary_forward_fixed_pasting g f h s k rfl rfl E) hb hg

end AlgebraicGeometry
