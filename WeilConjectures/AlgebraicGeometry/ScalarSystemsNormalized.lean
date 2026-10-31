/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedCalculusSupplement
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Scalar extension preserves normalized semilinear systems -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

private theorem adjoint_square_isIso
    {B₀ B₁ F₀ F₁ : Type*}
    [Category B₀] [Category B₁] [Category F₀] [Category F₁]
    {T : B₀ ⥤ B₁} {U : B₁ ⥤ B₀} {T' : F₀ ⥤ F₁} {U' : F₁ ⥤ F₀}
    {H₀ : B₀ ⥤ F₀} {K₀ : F₀ ⥤ B₀} {H₁ : B₁ ⥤ F₁} {K₁ : F₁ ⥤ B₁}
    (a : T ⊣ U) (b : T' ⊣ U') (c : H₀ ⊣ K₀) (d : H₁ ⊣ K₁)
    (θ : U' ⋙ K₀ ≅ K₁ ⋙ U)
    {P : B₀} {Q : B₁} {P' : F₀} {Q' : F₁}
    (x : P ⟶ K₀.obj P') (y : Q ⟶ K₁.obj Q')
    (t : P ⟶ U.obj Q) (t' : P' ⟶ U'.obj Q')
    [IsIso ((c.homEquiv _ _).symm x)] [IsIso ((d.homEquiv _ _).symm y)]
    [IsIso ((a.homEquiv _ _).symm t)]
    (h : x ≫ K₀.map t' ≫ θ.hom.app Q' = t ≫ U.map y) :
    IsIso ((b.homEquiv _ _).symm t') := by
  -- Compare the two left adjoints to the same composite right adjoint.
  let ac := (c.comp b).ofNatIsoRight θ
  let ad := a.comp d
  let e := ac.leftAdjointUniq ad
  let f := (a.homEquiv _ _).symm t
  let f' := (b.homEquiv _ _).symm t'
  let ex := (c.homEquiv _ _).symm x
  let ey := (d.homEquiv _ _).symm y
  have he : T'.map ex ≫ f' = e.hom.app P ≫ H₁.map f ≫ ey := by
    apply (ac.homEquiv _ _).injective
    change ac.homEquiv _ _ (T'.map ex ≫ f') = _
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change c.homEquiv _ _ (b.homEquiv _ _ (T'.map ex ≫ f')) ≫ θ.hom.app Q' = _
    rw [b.homEquiv_naturality_left]
    dsimp only [f']
    rw [Equiv.apply_symm_apply, c.homEquiv_naturality_right]
    dsimp only [ex]
    rw [Equiv.apply_symm_apply]
    rw [ac.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [Category.assoc]
    change x ≫ K₀.map t' ≫ θ.hom.app Q' = ad.homEquiv _ _ (H₁.map f ≫ ey)
    rw [Adjunction.comp_homEquiv]
    change x ≫ K₀.map t' ≫ θ.hom.app Q' =
      a.homEquiv _ _ (d.homEquiv _ _ (H₁.map f ≫ ey))
    rw [d.homEquiv_naturality_left]
    dsimp only [ey]
    rw [Equiv.apply_symm_apply, a.homEquiv_naturality_right]
    dsimp only [f]
    rw [Equiv.apply_symm_apply]
    exact h
  have hi : IsIso (T'.map ex ≫ f') := by
    rw [he]
    infer_instance
  exact (isIso_comp_left_iff (T'.map ex) f').mp hi

section ModelFactor
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryFactors
universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
open CategoryTheory CategoryTheory.Limits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  (F : A ⥤ B) (G : A ⥤ C) (R : C ⥤ B)
  [F.Additive] [G.Additive] [R.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

private theorem comp_fac_inverse (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso G R).hom.app (DerivedCategory.Q.obj P) ≫
      R.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
      R.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) =
    (G ⋙ R).mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ R)) (.up ℤ)).inv.app P) := by
  change _ = _ ≫ (DerivedCategory.Q.mapIso
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ R)) (.up ℤ)).app P)).inv
  rw [Iso.eq_comp_inv]
  simpa only [Category.assoc, Functor.mapIso_hom, Iso.app_hom] using
    Functor.mapDerivedCategoryCompIso_fac G R P

private theorem localized_transition_fac (δ : F ⟶ G ⋙ R) (P : CochainComplex A ℤ) :
    (Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((G ⋙ R).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      F.mapDerivedCategory (G ⋙ R).mapDerivedCategory
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex δ (.up ℤ))
        DerivedCategory.Q)).app (DerivedCategory.Q.obj P) ≫
      (Functor.mapDerivedCategoryCompIso G R).hom.app (DerivedCategory.Q.obj P) ≫
      R.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
      R.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) =
    F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex δ (.up ℤ)).app P ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ R)) (.up ℤ)).inv.app P) := by
  have hF : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) F.mapDerivedCategory =
    F.mapDerivedCategoryFactors := rfl
  have hG : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
      ((G ⋙ R).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (G ⋙ R).mapDerivedCategory = (G ⋙ R).mapDerivedCategoryFactors := rfl
  rw [Localization.liftNatTrans_app]
  simp only [hF, hG, Functor.whiskerRight_app, Category.assoc]
  rw [comp_fac_inverse G R P]
  simp only [Iso.inv_hom_id_app_assoc, Functor.map_comp]

end ModelFactor

section LocalizationCoherence
universe u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ w₀ w₁ w₂ w₃
variable {A : Type u₀} {L : Type u₁} {M : Type u₂} {N : Type u₃}
  [Category.{v₀} A] [Category.{v₁} L] [Category.{v₂} M] [Category.{v₃} N]
  [Abelian A] [Abelian L] [Abelian M] [Abelian N]
  [HasDerivedCategory.{w₀} A] [HasDerivedCategory.{w₁} L]
  [HasDerivedCategory.{w₂} M] [HasDerivedCategory.{w₃} N]
  (F : A ⥤ L) (G : A ⥤ M) (H : A ⥤ N)
  (R : M ⥤ L) (S : N ⥤ M) (U : N ⥤ L)
  [F.Additive] [G.Additive] [H.Additive] [R.Additive] [S.Additive] [U.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

private noncomputable def localizedTransition (δ : F ⟶ G ⋙ R) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ R.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ)) _ _
    F.mapDerivedCategory (G ⋙ R).mapDerivedCategory
    (Functor.whiskerRight (δ.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q) ≫
      (Functor.mapDerivedCategoryCompIso G R).hom

private noncomputable def localizedChain (δ : F ⟶ G ⋙ R) (K : CochainComplex A ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj K ⟶
      (R.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj K) :=
  (δ.mapHomologicalComplex (.up ℤ)).app K ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ R)) (.up ℤ)).inv.app K

private theorem localizedTransition_rep (δ : F ⟶ G ⋙ R) (K : CochainComplex A ℤ) :
    (localizedTransition F G R δ).app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
    F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map (localizedChain F G R δ K) := by
  simpa only [localizedTransition, localizedChain, NatTrans.comp_app, Category.assoc] using
    localized_transition_fac F G R δ K

end LocalizationCoherence

section ExactSquareFactor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem exactSquare_fac
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {R : C ⥤ D} {G : D ⥤ F} {L : C ⥤ E} {S : E ⥤ F}
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : R ⋙ G ≅ L ⋙ S) (K : CochainComplex C ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
      S.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
      S.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  have hc := Functor.mapDerivedCategoryCompIso_hom_app_factors R G K
  have hi : (Functor.mapDerivedCategoryCompIso R G).inv.app (DerivedCategory.Q.obj K) ≫
      (R ⋙ G).mapDerivedCategoryFactors.hom.app K =
    G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply (cancel_epi
      ((Functor.mapDerivedCategoryCompIso R G).hom.app (DerivedCategory.Q.obj K))).mp
    rw [Iso.hom_inv_id_app_assoc]
    exact hc.symm
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors, Functor.mapDerivedCategoryNatIso_fac]
  rw [← Category.assoc, hi, Category.assoc]

end ExactSquareFactor

section LocalizationSquare
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

private theorem localized_transition_square
    {X Y B₀ B₁ F₀ F₁ : Type*}
    [Category X] [Category Y] [Category B₀] [Category B₁] [Category F₀] [Category F₁]
    [Abelian X] [Abelian Y] [Abelian B₀] [Abelian B₁] [Abelian F₀] [Abelian F₁]
    [HasDerivedCategory X] [HasDerivedCategory Y]
    [HasDerivedCategory B₀] [HasDerivedCategory B₁]
    [HasDerivedCategory F₀] [HasDerivedCategory F₁]
    (r : X ⥤ Y) (a₀ : Y ⥤ B₀) (a₁ : Y ⥤ B₁)
    (b₀ : X ⥤ F₀) (b₁ : X ⥤ F₁) (k₀ : F₀ ⥤ B₀) (k₁ : F₁ ⥤ B₁)
    (s : B₁ ⥤ B₀) (t : F₁ ⥤ F₀)
    [r.Additive] [a₀.Additive] [a₁.Additive] [b₀.Additive] [b₁.Additive]
    [k₀.Additive] [k₁.Additive] [s.Additive] [t.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits a₀] [PreservesFiniteColimits a₀]
    [PreservesFiniteLimits a₁] [PreservesFiniteColimits a₁]
    [PreservesFiniteLimits b₀] [PreservesFiniteColimits b₀]
    [PreservesFiniteLimits b₁] [PreservesFiniteColimits b₁]
    [PreservesFiniteLimits k₀] [PreservesFiniteColimits k₀]
    [PreservesFiniteLimits k₁] [PreservesFiniteColimits k₁]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    [PreservesFiniteLimits t] [PreservesFiniteColimits t]
    (δ₀ : r ⋙ a₀ ≅ b₀ ⋙ k₀) (δ₁ : r ⋙ a₁ ≅ b₁ ⋙ k₁)
    (θ : t ⋙ k₀ ≅ k₁ ⋙ s) (p : a₀ ⟶ a₁ ⋙ s) (q : b₀ ⟶ b₁ ⋙ t)
    (h : ∀ N, δ₀.hom.app N ≫ k₀.map (q.app N) ≫ θ.hom.app (b₁.obj N) =
      p.app (r.obj N) ≫ s.map (δ₁.hom.app N)) (N : DerivedCategory X) :
    (Functor.mapDerivedCategorySquareIso δ₀).hom.app N ≫
        k₀.mapDerivedCategory.map ((localizedTransition b₀ b₁ t q).app N) ≫
        (Functor.mapDerivedCategorySquareIso θ).hom.app (b₁.mapDerivedCategory.obj N) =
      (localizedTransition a₀ a₁ s p).app (r.mapDerivedCategory.obj N) ≫
        s.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso δ₁).hom.app N) := by
  let d₀ := Functor.mapDerivedCategorySquareIso δ₀
  let d₁ := Functor.mapDerivedCategorySquareIso δ₁
  let e := Functor.mapDerivedCategorySquareIso θ
  let pd := localizedTransition a₀ a₁ s p
  let qd := localizedTransition b₀ b₁ t q
  suffices he : d₀.hom ≫ Functor.whiskerRight qd k₀.mapDerivedCategory ≫
      Functor.whiskerLeft b₁.mapDerivedCategory e.hom =
    Functor.whiskerLeft r.mapDerivedCategory pd ≫
      Functor.whiskerRight d₁.hom s.mapDerivedCategory by
    exact congrArg (fun z ↦ z.app N) he
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso X (.up ℤ))
  intro K
  let K₁ := (b₁.mapHomologicalComplex (.up ℤ)).obj K
  let Kr := (r.mapHomologicalComplex (.up ℤ)).obj K
  let pc := localizedChain a₀ a₁ s p Kr
  let qc := localizedChain b₀ b₁ t q K
  have hc : (NatTrans.mapHomologicalComplex δ₀.hom (.up ℤ)).app K ≫
      (k₀.mapHomologicalComplex (.up ℤ)).map qc ≫
      (NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app K₁ =
    pc ≫ (s.mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex δ₁.hom (.up ℤ)).app K) := by
    apply HomologicalComplex.hom_ext
    intro i
    change δ₀.hom.app (K.X i) ≫ k₀.map (q.app (K.X i) ≫ 𝟙 _) ≫
        θ.hom.app (b₁.obj (K.X i)) =
      (p.app (r.obj (K.X i)) ≫ 𝟙 _) ≫ s.map (δ₁.hom.app (K.X i))
    simpa only [Category.comp_id] using h (K.X i)
  apply (cancel_mono
    (s.mapDerivedCategory.map
      (k₁.mapDerivedCategory.map (b₁.mapDerivedCategoryFactors.hom.app K) ≫
        k₁.mapDerivedCategoryFactors.hom.app K₁) ≫
      s.mapDerivedCategoryFactors.hom.app ((k₁.mapHomologicalComplex (.up ℤ)).obj K₁))).mp
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Functor.map_comp, Category.assoc]
  have hn := e.hom.naturality (b₁.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [exactSquare_fac θ K₁]
  simp only [← k₀.mapDerivedCategory.map_comp_assoc]
  rw [localizedTransition_rep b₀ b₁ t q K]
  simp only [k₀.mapDerivedCategory.map_comp, Category.assoc]
  have hq := k₀.mapDerivedCategoryFactors.hom.naturality qc
  dsimp only [Functor.comp_map] at hq
  rw [reassoc_of% hq, reassoc_of% (exactSquare_fac δ₀ K)]
  rw [← s.mapDerivedCategory.map_comp_assoc, ← s.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  rw [exactSquare_fac δ₁ K]
  simp only [s.mapDerivedCategory.map_comp, Category.assoc]
  have hp := pd.naturality (r.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map] at hp
  rw [← reassoc_of% hp]
  have hd := s.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex δ₁.hom (.up ℤ)).app K)
  dsimp only [Functor.comp_map] at hd
  erw [hd]
  erw [reassoc_of% (localizedTransition_rep a₀ a₁ s p Kr)]
  simp only [← DerivedCategory.Q.map_comp]
  exact congrArg (fun z ↦ a₀.mapDerivedCategory.map (r.mapDerivedCategoryFactors.hom.app K) ≫
    a₀.mapDerivedCategoryFactors.hom.app Kr ≫ DerivedCategory.Q.map z) hc

end LocalizationSquare

namespace WeilConjectures.SemilinearSections
set_option synthInstance.maxSize 4096
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section CoefficientSquare
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (B F : ℕ → Sheaf J CommRingCat.{u + 1})
  (τ : ∀ n, B (n + 1) ⟶ B n) (σ : ∀ n, F (n + 1) ⟶ F n)
  (α : ∀ n, B n ⟶ F n)
  (hα : ∀ n, α (n + 1) ≫ σ n = τ n ≫ α n)

include hα
omit [EssentiallySmall.{u + 1} C] in
private theorem coefficient_square {m n : ℕ} (h : n ≤ m) :
    α m ≫ coefficientMap.{u + 1, u, u + 1} J F σ h =
      coefficientMap.{u + 1, u, u + 1} J B τ h ≫ α n := by
  let a : rings.{u + 1, u, u + 1} J B τ ⟶ rings.{u + 1, u, u + 1} J F σ :=
    NatTrans.ofOpSequence α (fun n ↦ by
      simpa only [rings, Functor.ofOpSequence_map_homOfLE_succ] using (hα n).symm)
  exact (a.naturality (homOfLE h).op).symm

attribute [-instance] AlgebraicGeometry.Scheme.ProjectionRestriction.derived in
@[irreducible] private noncomputable def ordinaryRestrictionSquare {m n : ℕ} (h : n ≤ m) :
    res.{u + 1, u, u + 1} (coefficientMap.{u + 1, u, u + 1} J F σ h) ⋙
        res.{u + 1, u, u + 1} (α m) ≅
      res.{u + 1, u, u + 1} (α n) ⋙
        res.{u + 1, u, u + 1} (coefficientMap.{u + 1, u, u + 1} J B τ h) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App ((α m).hom.app U).hom
        ((coefficientMap.{u + 1, u, u + 1} J F σ h).hom.app U).hom
        ((α m ≫ coefficientMap.{u + 1, u, u + 1} J F σ h).hom.app U).hom
        rfl (M.val.obj U)).symm ≪≫
      ModuleCat.restrictScalarsComp'App
        ((coefficientMap.{u + 1, u, u + 1} J B τ h).hom.app U).hom
        ((α n).hom.app U).hom
        ((α m ≫ coefficientMap.{u + 1, u, u + 1} J F σ h).hom.app U).hom
        (congrArg (fun f ↦ (f.hom.app U).hom)
          (coefficient_square J B F τ σ α hα h)) (M.val.obj U))
      (by intros; ext x; rfl))) (by intros; ext U x; rfl)

attribute [-instance] AlgebraicGeometry.Scheme.ProjectionRestriction.derived in
private theorem ordinaryRestrictionSquare_section {m n : ℕ} (h : n ≤ m)
    (M : Mod.{u + 1, u, u + 1} J (F n)) (U : Cᵒᵖ) :
    (fun x ↦ ((ordinaryRestrictionSquare J B F τ σ α hα h).hom.app M).val.app U x) =
      (fun x : M.val.obj U ↦ x) := by
  unfold ordinaryRestrictionSquare
  rfl

attribute [local irreducible] systemRing ringPresheaf rings coefficientMap systemMap

attribute [-instance] AlgebraicGeometry.Scheme.ProjectionRestriction.derived in
private theorem ordinary_transition_square {m n : ℕ} (h : n ≤ m)
    (N : Systems.{u + 1, u, u + 1} J F σ) :
    (restrictionEvaluation_existsUnique.{u + 1, u, u + 1}
      J B τ F σ α hα m).exists.choose.hom.app N ≫
      (res.{u + 1, u, u + 1} (α m)).map
        ((transition.{u + 1, u, u + 1} J F σ h).app N) ≫
      (ordinaryRestrictionSquare J B F τ σ α hα h).hom.app
        ((evaluation.{u + 1, u, u + 1} J F σ n).obj N) =
    (transition.{u + 1, u, u + 1} J B τ h).app
        ((res.{u + 1, u, u + 1} (systemMap.{u + 1, u, u + 1} J B τ F σ α hα)).obj N) ≫
      (res.{u + 1, u, u + 1} (coefficientMap.{u + 1, u, u + 1} J B τ h)).map
        ((restrictionEvaluation_existsUnique.{u + 1, u, u + 1}
          J B τ F σ α hα n).exists.choose.hom.app N) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  have hm := eq_of_heq ((restrictionEvaluation_existsUnique.{u + 1, u, u + 1}
    J B τ F σ α hα m).exists.choose_spec N U)
  have hn := eq_of_heq ((restrictionEvaluation_existsUnique.{u + 1, u, u + 1}
    J B τ F σ α hα n).exists.choose_spec N U)
  have htF := eq_of_heq ((transition_exists.{u + 1, u, u + 1}
    J F σ h).exists.choose_spec N U)
  have htB := eq_of_heq ((transition_exists.{u + 1, u, u + 1} J B τ h).exists.choose_spec
    ((res.{u + 1, u, u + 1} (systemMap.{u + 1, u, u + 1} J B τ F σ α hα)).obj N) U)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change ((ordinaryRestrictionSquare J B F τ σ α hα h).hom.app
      ((evaluation.{u + 1, u, u + 1} J F σ n).obj N)).val.app U
      (((transition.{u + 1, u, u + 1} J F σ h).app N).val.app U
        (((restrictionEvaluation_existsUnique.{u + 1, u, u + 1}
          J B τ F σ α hα m).exists.choose.hom.app N).val.app U x)) =
    ((restrictionEvaluation_existsUnique.{u + 1, u, u + 1}
      J B τ F σ α hα n).exists.choose.hom.app N).val.app U
      (((transition.{u + 1, u, u + 1} J B τ h).app _).val.app U x)
  -- Isolate each conversion in a proof block to avoid elaborating the whole tower.
  calc
    _ = ((transition.{u + 1, u, u + 1} J F σ h).app N).val.app U
        (((restrictionEvaluation_existsUnique.{u + 1, u, u + 1}
          J B τ F σ α hα m).exists.choose.hom.app N).val.app U x) :=
      by
        exact congrFun (ordinaryRestrictionSquare_section J B F τ σ α hα h _ U) _
    _ = N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
        (((restrictionEvaluation_existsUnique.{u + 1, u, u + 1}
          J B τ F σ α hα m).exists.choose.hom.app N).val.app U x) := by
      exact congrFun htF _
    _ = N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x :=
      by
        exact congrArg (fun z ↦ N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op z)
          (congrFun hm x)
    _ = (((res.{u + 1, u, u + 1}
          (systemMap.{u + 1, u, u + 1} J B τ F σ α hα)).obj N).val.map
          (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op) x := by
      rfl
    _ = ((transition.{u + 1, u, u + 1} J B τ h).app _).val.app U x :=
      by
        exact (congrFun htB x).symm
    _ = _ := by
      exact (congrFun hn _).symm

attribute [-instance] AlgebraicGeometry.Scheme.ProjectionRestriction.derived in
private noncomputable def derivedRestrictionSquare {m n : ℕ} (h : n ≤ m) :
    resD.{u + 1, u, u + 1} (coefficientMap.{u + 1, u, u + 1} J F σ h) ⋙
        resD.{u + 1, u, u + 1} (α m) ≅
      resD.{u + 1, u, u + 1} (α n) ⋙
        resD.{u + 1, u, u + 1} (coefficientMap.{u + 1, u, u + 1} J B τ h) :=
  Functor.mapDerivedCategorySquareIso (ordinaryRestrictionSquare J B F τ σ α hα h)

attribute [-instance] AlgebraicGeometry.Scheme.ProjectionRestriction.derived in
private theorem derived_transition_square {m n : ℕ} (h : n ≤ m)
    (N : DS.{u + 1, u, u + 1} J F σ) :
    (restrictionEvaluation.{u + 1, u, u + 1} J B τ F σ α hα m).hom.app N ≫
      (resD.{u + 1, u, u + 1} (α m)).map
        ((derivedTransition.{u + 1, u, u + 1} J F σ h).app N) ≫
      (derivedRestrictionSquare J B F τ σ α hα h).hom.app
        ((e.{u + 1, u, u + 1} J F σ n).obj N) =
    (derivedTransition.{u + 1, u, u + 1} J B τ h).app
        ((resD.{u + 1, u, u + 1} (systemMap.{u + 1, u, u + 1} J B τ F σ α hα)).obj N) ≫
      (resD.{u + 1, u, u + 1} (coefficientMap.{u + 1, u, u + 1} J B τ h)).map
        ((restrictionEvaluation.{u + 1, u, u + 1} J B τ F σ α hα n).hom.app N) := by
  exact localized_transition_square
    (res.{u + 1, u, u + 1} (systemMap.{u + 1, u, u + 1} J B τ F σ α hα))
    (evaluation.{u + 1, u, u + 1} J B τ m)
    (evaluation.{u + 1, u, u + 1} J B τ n)
    (evaluation.{u + 1, u, u + 1} J F σ m)
    (evaluation.{u + 1, u, u + 1} J F σ n)
    (res.{u + 1, u, u + 1} (α m)) (res.{u + 1, u, u + 1} (α n))
    (res.{u + 1, u, u + 1} (coefficientMap.{u + 1, u, u + 1} J B τ h))
    (res.{u + 1, u, u + 1} (coefficientMap.{u + 1, u, u + 1} J F σ h))
    (restrictionEvaluation_existsUnique.{u + 1, u, u + 1} J B τ F σ α hα m).exists.choose
    (restrictionEvaluation_existsUnique.{u + 1, u, u + 1} J B τ F σ α hα n).exists.choose
    (ordinaryRestrictionSquare J B F τ σ α hα h)
    (transition.{u + 1, u, u + 1} J B τ h)
    (transition.{u + 1, u, u + 1} J F σ h)
    (ordinary_transition_square J B F τ σ α hα h) N
end CoefficientSquare

attribute [-instance] AlgebraicGeometry.Scheme.ProjectionRestriction.derived in
/-- Derived scalar extension along a compatible map of coefficient towers preserves
normalization, for any specified normalized scalar adjunctions on the two towers.
Source: Zheng Construction 4.1 and Lemma 4.10; parent proof step 1
(blueprint: lem-coef-scalar-systems-normalized).
Proof: for m >= n, transpose the strict output transition through the level scalar
adjunction. The transpose_evaluation identity identifies this with extension of the
input transition-adjoint, conjugated by the evaluation isomorphisms and tensor
reassociation. The two ways to extend scalars agree because the coefficient square
commutes. On ordinary pure tensors both send x tensor b to tau(x) tensor bar(b).
Compute on the normalized K-flat models of ScalarData and localize this equality;
the transpose_model equations ensure that these are the specified adjunctions.
The input transition-adjoint is invertible, tensor preserves its inverse, and all
comparison maps are isomorphisms, so the output transition-adjoint is invertible.
Changing the reduction ScalarData changes only the unique left-adjoint comparison,
so the assertion holds for the two given Data packages. This argument includes
m=n and arbitrary (possibly zero) coefficient rings and empty sites. -/
theorem scalarSystems_normalized
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    (B F : ℕ → Sheaf J CommRingCat.{u + 1})
    (τ : ∀ n, B (n + 1) ⟶ B n) (σ : ∀ n, F (n + 1) ⟶ F n)
    (α : ∀ n, B n ⟶ F n)
    (hα : ∀ n, α (n + 1) ≫ σ n = τ n ≫ α n)
    (A : Data.{u + 1, u, u + 1} J B τ)
    (A' : Data.{u + 1, u, u + 1} J F σ)
    (S : ScalarSystems.{u + 1, u, u + 1} J B τ F σ α hα)
    (M : DS.{u + 1, u, u + 1} J B τ)
    (hM : Normalized.{u + 1, u, u + 1} J B τ A.scalar M) :
    Normalized.{u + 1, u, u + 1} J F σ A'.scalar (S.scalar.T.obj M) := by
  intro m n h
  let N := S.scalar.T.obj M
  let η : M ⟶ (resD (systemMap J B τ F σ α hα)).obj N :=
    S.scalar.adjunction.homEquiv _ _ (𝟙 N)
  let x := (S.levels m).adjunction.homEquiv _ _ ((S.evaluation m).inv.app M)
  let y := (S.levels n).adjunction.homEquiv _ _ ((S.evaluation n).inv.app M)
  have hm : (e J B τ m).map η ≫
      (restrictionEvaluation J B τ F σ α hα m).hom.app N = x := by
    have H := S.transpose_evaluation m M N (𝟙 N)
    rw [(e J F σ m).map_id] at H
    erw [Category.comp_id] at H
    exact H
  have hn : (e J B τ n).map η ≫
      (restrictionEvaluation J B τ F σ α hα n).hom.app N = y := by
    have H := S.transpose_evaluation n M N (𝟙 N)
    rw [(e J F σ n).map_id] at H
    erw [Category.comp_id] at H
    exact H
  have : IsIso (((S.levels m).adjunction.homEquiv _ _).symm x) := by
    dsimp only [x]
    rw [Equiv.symm_apply_apply]
    infer_instance
  have : IsIso (((S.levels n).adjunction.homEquiv _ _).symm y) := by
    dsimp only [y]
    rw [Equiv.symm_apply_apply]
    infer_instance
  have : IsIso (((A.scalar h).adjunction.homEquiv _ _).symm
      ((derivedTransition J B τ h).app M)) := hM h
  apply adjoint_square_isIso (A.scalar h).adjunction (A'.scalar h).adjunction
    (S.levels m).adjunction (S.levels n).adjunction
    (derivedRestrictionSquare J B F τ σ α hα h) x y
    ((derivedTransition J B τ h).app M) ((derivedTransition J F σ h).app N)
  dsimp only [Functor.comp_obj]
  calc
    _ = (e J B τ m).map η ≫
        ((restrictionEvaluation J B τ F σ α hα m).hom.app N ≫
          (resD (α m)).map ((derivedTransition J F σ h).app N) ≫
            (derivedRestrictionSquare J B F τ σ α hα h).hom.app
              ((e J F σ n).obj N)) := by
      rw [← hm]
      dsimp only [N, Functor.comp_obj]
      simp only [Category.assoc]
    _ = (e J B τ m).map η ≫
        ((derivedTransition J B τ h).app
            ((resD (systemMap J B τ F σ α hα)).obj N) ≫
          (resD (coefficientMap J B τ h)).map
            ((restrictionEvaluation J B τ F σ α hα n).hom.app N)) := by
      rw [derived_transition_square]
    _ = (derivedTransition J B τ h).app M ≫
        (resD (coefficientMap J B τ h)).map
          ((e J B τ n).map η ≫
            (restrictionEvaluation J B τ F σ α hα n).hom.app N) := by
      rw [← Category.assoc, (derivedTransition J B τ h).naturality η]
      simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    _ = _ := by rw [hn]

end WeilConjectures.SemilinearSections
