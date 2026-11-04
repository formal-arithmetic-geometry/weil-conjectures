/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerDefs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitShift
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-! # Pro-étale derived base change: shifts and adjoint forms

Source: blueprint lem-pur-relative-kummer-exchange-from-conclusions (auxiliary lemmas).
-/

@[expose] public section
set_option autoImplicit false
universe u' u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {A : Type*} [AddMonoid A]
  [HasShift C A] [HasShift D A] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.CommShift A]

/-- A shift structure on a left adjoint compatible with the adjunction satisfies the unit
compatibility. -/
lemma compatibilityUnit_of_commShift [F.CommShift A] [adj.CommShift A] (a : A) :
    CommShift.CompatibilityUnit adj (F.commShiftIso a) (G.commShiftIso a) := by
  intro X
  rw [← adj.unit_app_commShiftIso_hom_app A a X, Functor.commShiftIso_comp_hom_app]

/-- Two shift structures on a left adjoint which are both compatible with the adjunction
have the same commutation isomorphisms. -/
lemma commShiftIso_eq_of_commShift (S₁ S₂ : F.CommShift A)
    (h₁ : letI := S₁; adj.CommShift A) (h₂ : letI := S₂; adj.CommShift A) (a : A) :
    @Functor.commShiftIso _ _ _ _ F A _ _ _ S₁ a =
      @Functor.commShiftIso _ _ _ _ F A _ _ _ S₂ a :=
  CommShift.compatibilityUnit_unique_left adj _ _ (G.commShiftIso a)
    (@compatibilityUnit_of_commShift _ _ _ _ _ _ _ _ _ _ adj _ S₁ h₁ a)
    (@compatibilityUnit_of_commShift _ _ _ _ _ _ _ _ _ _ adj _ S₂ h₂ a)

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

lemma derivedUpperStarLowerStarAdjunction_eq_ofNatIsoLeft {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    derivedUpperStarLowerStarAdjunction A g =
      ((ProEtale.upperStarLowerStarAdjunction A g).mapDerivedCategoryRightDerivedAdjunction
        ).ofNatIsoLeft (leftDerivedUpperStarIsoMapDerivedCategory A g).symm :=
  Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
    (leftDerivedUpperStarIsoMapDerivedCategory A g)
    ((g)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac).symm

/-- The identification `Lg^* ≅ D(g^*)` commutes with the shifts, for the shift structure of
`Lg^*` induced by the derived adjunction. -/
instance commShift_leftDerivedUpperStarIsoMapDerivedCategory_hom {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).hom ℤ := by
  have h₂ : letI := Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
      (derivedUpperStarLowerStarAdjunction A g).CommShift ℤ := by
    let := Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
    have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
      Functor.CommShift.ofIso_compatibility _ ℤ
    rw [derivedUpperStarLowerStarAdjunction_eq_ofNatIsoLeft]
    exact Adjunction.commShift_ofNatIsoLeft _ _
  have he := (derivedUpperStarLowerStarAdjunction A g).commShiftIso_eq_of_commShift
    (commShiftLeftDerivedUpperStar A g)
    (Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ)
    inferInstance h₂
  have hc : letI := Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
      NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).hom ℤ := by
    let := Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
    have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
      Functor.CommShift.ofIso_compatibility _ ℤ
    exact NatTrans.CommShift.of_iso_inv (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  refine ⟨fun a ↦ ?_⟩
  rw [he a]
  exact hc.shift_comm a

/-- The composition isomorphism of derived pullbacks commutes with the shifts. -/
instance commShift_leftDerivedUpperStarComp_hom {T S R : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ R) : NatTrans.CommShift (leftDerivedUpperStarComp A g₁ g₂).hom ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g₁).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g₂).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  have e : (leftDerivedUpperStarComp A g₁ g₂).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory A (g₁ ≫ g₂)).hom ≫
        (Functor.mapDerivedCategoryNatIso (ProEtale.upperStarComp A g₁ g₂)).hom ≫
        ((g₂)^*[A].mapDerivedCategoryCompIso (g₁)^*[A]).hom ≫
        Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g₂).inv
          D((g₁)^*[A]) ≫
        Functor.whiskerLeft L((g₂)^*[A]) (leftDerivedUpperStarIsoMapDerivedCategory A g₁).inv := by
    simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
      Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory]
  rw [e]
  infer_instance

/-- The transport of derived pullbacks along an equality commutes with the shifts. -/
instance commShift_leftDerivedUpperStarCongr_hom {X Y : Scheme.{u}} {f₁ f₂ : X ⟶ Y}
    (h : f₁ = f₂) : NatTrans.CommShift (leftDerivedUpperStarCongr A h).hom ℤ := by
  subst h
  rw [leftDerivedUpperStarCongr_rfl]
  exact inferInstanceAs (NatTrans.CommShift (𝟙 _) ℤ)

/-- The square isomorphism of derived pullbacks commutes with the shifts. -/
instance commShift_leftDerivedUpperStarSquareIso_hom {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :
    NatTrans.CommShift (leftDerivedUpperStarSquareIso A sq).hom ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarComp A f' g).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  dsimp only [leftDerivedUpperStarSquareIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

/-- The derived base change map commutes with the shifts. -/
instance commShift_derivedBaseChangeMap {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :
    NatTrans.CommShift (derivedBaseChangeMap A sq) ℤ :=
  NatTrans.CommShift.mateEquiv (derivedUpperStarLowerStarAdjunction A f)
    (derivedUpperStarLowerStarAdjunction A f')
    (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarSquareIso A sq).hom)

/-- The unit form of the derived base change map. -/
@[reassoc]
lemma map_unit_derivedBaseChangeMap_app {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (L((g)^*[A])).map ((derivedUpperStarLowerStarAdjunction A f).unit.app M) ≫
        (derivedBaseChangeMap A sq).app ((L((f)^*[A])).obj M) =
      (derivedUpperStarLowerStarAdjunction A f').unit.app ((L((g)^*[A])).obj M) ≫
        (R((f')_*[A])).map ((leftDerivedUpperStarSquareIso A sq).hom.app M) :=
  unit_mateEquiv _ _ _ M

/-- The derived base change map carries the pullback of an adjoint to the adjoint of the
pulled-back morphism. -/
lemma derivedBaseChangeMap_app_homEquiv {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    {M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (α : (L((f)^*[A])).obj M ⟶ K) :
    (L((g)^*[A])).map ((derivedUpperStarLowerStarAdjunction A f).homEquiv _ _ α) ≫
      (derivedBaseChangeMap A sq).app K =
    (derivedUpperStarLowerStarAdjunction A f').homEquiv _ _
      ((leftDerivedUpperStarSquareIso A sq).hom.app M ≫ (L((g')^*[A])).map α) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have h := (derivedBaseChangeMap A sq).naturality α
  simp only [Functor.comp_map] at h
  rw [h, ← Category.assoc, map_unit_derivedBaseChangeMap_app, Category.assoc,
    ← Functor.map_comp]

end AlgebraicGeometry.ProEtale

namespace CategoryTheory.Adjunction

/-- If the adjoint of an isomorphism `c : L M ⟶ K` becomes invertible after applying `H`, so
does the adjoint of any isomorphism `L M₂ ⟶ K₂` with `M₂ ≅ M`. -/
lemma isIso_map_homEquiv_of_isIso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {M M₂ : C} {K K₂ : D} (c : L.obj M ⟶ K)
    (e : L.obj M₂ ⟶ K₂) (d : M₂ ⟶ M) [IsIso c] [IsIso e] [IsIso d] (H : C ⥤ E)
    (hc : IsIso (H.map (adj.homEquiv _ _ c))) : IsIso (H.map (adj.homEquiv _ _ e)) := by
  have he : e = L.map d ≫ c ≫ (inv (L.map d ≫ c) ≫ e) := by simp
  rw [he, adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, H.map_comp, H.map_comp]
  infer_instance

/-- If the adjoint of an isomorphism `c : L M ⟶ K` is invertible, so is the adjoint of any
isomorphism `L M₂ ⟶ K₂` with `M₂ ≅ M`. -/
lemma isIso_homEquiv_of_isIso {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {M M₂ : C} {K K₂ : D} (c : L.obj M ⟶ K)
    (e : L.obj M₂ ⟶ K₂) (d : M₂ ⟶ M) [IsIso c] [IsIso e] [IsIso d]
    (hc : IsIso (adj.homEquiv _ _ c)) : IsIso (adj.homEquiv _ _ e) := by
  have := adj.isIso_map_homEquiv_of_isIso c e d (𝟭 C) hc
  simpa using this

/-- The mate of a square, evaluated on an adjoint. -/
lemma map_homEquiv_mateEquiv_app
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    (θ : TwoSquare G L L' H) {A : C} {K : D} (z : L.obj A ⟶ K) :
    G.map (adj.homEquiv A K z) ≫ (mateEquiv adj adj' θ).natTrans.app K =
      adj'.homEquiv (G.obj A) (H.obj K) (θ.natTrans.app A ≫ H.map z) := by
  rw [adj.homEquiv_unit, G.map_comp, Category.assoc]
  have hn := (mateEquiv adj adj' θ).natTrans.naturality z
  simp only [Functor.comp_map] at hn
  rw [hn]
  rw [← Category.assoc, unit_mateEquiv, Category.assoc, ← R'.map_comp,
    adj'.homEquiv_unit]
  rfl

/-- The mate of a square commuting with shifts, evaluated on a shifted adjoint. -/
lemma map_homEquiv_comp_commShiftIso_mateEquiv_app
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    [R.CommShift ℤ] [R'.CommShift ℤ]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    [G.CommShift ℤ] [H.CommShift ℤ] (θ : TwoSquare G L L' H)
    [NatTrans.CommShift (mateEquiv adj adj' θ).natTrans ℤ]
    {A : C} {K : D} (q : ℤ) (z : L.obj A ⟶ K⟦q⟧) :
    G.map (adj.homEquiv A (K⟦q⟧) z ≫ (R.commShiftIso q).hom.app K) ≫
        (G.commShiftIso q).hom.app (R.obj K) ≫
        (shiftFunctor E q).map ((mateEquiv adj adj' θ).natTrans.app K) =
      adj'.homEquiv (G.obj A) ((H.obj K)⟦q⟧)
        (θ.natTrans.app A ≫ H.map z ≫ (H.commShiftIso q).hom.app K) ≫
          (R'.commShiftIso q).hom.app (H.obj K) := by
  have hs := NatTrans.shift_app_comm (mateEquiv adj adj' θ).natTrans q K
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hs
  rw [Functor.map_comp, Category.assoc, hs]
  rw [← Category.assoc, map_homEquiv_mateEquiv_app]
  rw [← Category.assoc, ← adj'.homEquiv_naturality_right, Category.assoc]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived base change map carries the pullback of a shifted adjoint to the shifted
adjoint of the pulled-back morphism. -/
lemma derivedBaseChangeMap_shift_homEquiv {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    {M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (q : ℤ)
    (z : (L((f)^*[A])).obj M ⟶ K⟦q⟧) :
    (L((g)^*[A])).map ((derivedUpperStarLowerStarAdjunction A f).homEquiv _ _ z ≫
        ((R((f)_*[A])).commShiftIso q).hom.app K) ≫
      ((L((g)^*[A])).commShiftIso q).hom.app ((R((f)_*[A])).obj K) ≫
      ((derivedBaseChangeMap A sq).app K)⟦q⟧' =
    (derivedUpperStarLowerStarAdjunction A f').homEquiv _ _
        ((leftDerivedUpperStarSquareIso A sq).hom.app M ≫ (L((g')^*[A])).map z ≫
          ((L((g')^*[A])).commShiftIso q).hom.app K) ≫
      ((R((f')_*[A])).commShiftIso q).hom.app ((L((g')^*[A])).obj K) := by
  have : NatTrans.CommShift
      (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarSquareIso A sq).hom).natTrans ℤ :=
    inferInstanceAs (NatTrans.CommShift (leftDerivedUpperStarSquareIso A sq).hom ℤ)
  have := NatTrans.CommShift.mateEquiv (A := ℤ) (derivedUpperStarLowerStarAdjunction A f)
    (derivedUpperStarLowerStarAdjunction A f')
    (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarSquareIso A sq).hom)
  exact Adjunction.map_homEquiv_comp_commShiftIso_mateEquiv_app _ _ _ _ _ q z

end AlgebraicGeometry.ProEtale
