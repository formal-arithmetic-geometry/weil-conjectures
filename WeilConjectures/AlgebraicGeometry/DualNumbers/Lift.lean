/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DualNumbers

/-!
# Morphisms into dual-number thickenings

A square-zero global function `t` on a scheme `T` gives a morphism `T ⟶ T[ε]`, the identity on
points and `a + εb ↦ a + tb` on functions (`AlgebraicGeometry.Scheme.dualNumbersLift`). Every
morphism `h : T ⟶ S[ε]` with `h ≫ p = x` is of this form, followed by `x[ε] : T[ε] ⟶ S[ε]`, for
`t = h^♯(ε)` (`AlgebraicGeometry.Scheme.eq_dualNumbersLift_comp_dualNumbers`): a morphism into
`S[ε]` over `S` is a square-zero function.

We also record how the projections, the closed immersions, the functoriality and the map
`η ↦ εδ` act on sections.

## Main definitions

- `AlgebraicGeometry.Scheme.dualNumbersLift`: the morphism `T ⟶ T[ε]`, `ε ↦ t`.
- `AlgebraicGeometry.Scheme.Hom.dualNumbersParam`: the square-zero function `h^♯(ε)` attached to
  a morphism `h : T ⟶ S[ε]`.

## Main results

- `AlgebraicGeometry.Scheme.eq_dualNumbersLift_comp_dualNumbers`: a morphism `h : T ⟶ S[ε]`
  with `h ≫ p = x` is `T ⟶ T[ε] ⟶ S[ε]`, `ε ↦ h^♯(ε)` followed by `x[ε]`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace TrivSqZeroExt Opposite

theorem DualNumber.evalRingHom_mapRingHom {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (t : A) (ht : t * t = 0) (t' : B) (ht' : t' * t' = 0) (h : φ t = t') (x : DualNumber A) :
    DualNumber.evalRingHom t' ht' (DualNumber.mapRingHom φ x) =
      φ (DualNumber.evalRingHom t ht x) := by
  subst h
  simp

namespace AlgebraicGeometry

namespace Scheme

variable {X Y : Scheme.{u}}

/-! ### The thickening morphisms on sections -/

theorem dualNumbers_presheaf_map_apply {U V : X.Opens} (i : op U ⟶ op V)
    (x : Γ(X.dualNumbers, U)) :
    X.dualNumbers.presheaf.map i x = DualNumber.mapRingHom (X.presheaf.map i).hom x :=
  rfl

@[simp]
theorem fst_dualNumbers_presheaf_map {U V : X.Opens} (i : op U ⟶ op V)
    (x : Γ(X.dualNumbers, U)) :
    (X.dualNumbers.presheaf.map i x).fst = X.presheaf.map i (x.fst : Γ(X, U)) :=
  DualNumber.fst_mapRingHom _ _

@[simp]
theorem snd_dualNumbers_presheaf_map {U V : X.Opens} (i : op U ⟶ op V)
    (x : Γ(X.dualNumbers, U)) :
    (X.dualNumbers.presheaf.map i x).snd = X.presheaf.map i (x.snd : Γ(X, U)) :=
  DualNumber.snd_mapRingHom _ _

theorem dualNumbersProj_appLE (U : X.Opens) (V : X.Opens) (e : V ≤ X.dualNumbersProj ⁻¹ᵁ U)
    (a : Γ(X, U)) :
    X.dualNumbersProj.appLE U V e a = inl (X.presheaf.map (homOfLE e).op a) := by
  change DualNumber.mapRingHom (X.presheaf.map (homOfLE e).op).hom (inl a) = _
  ext <;> simp

theorem dualNumbersProj_appLE' (U : X.Opens) (V : X.Opens) (e : V ≤ X.dualNumbersProj ⁻¹ᵁ U)
    (a : Γ(X, U)) :
    X.dualNumbersProj.appLE U V e a =
      X.dualNumbers.presheaf.map (homOfLE e).op (inl a : DualNumber Γ(X, U)) := by
  rw [dualNumbersProj_appLE, dualNumbers_presheaf_map_apply]
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp

theorem dualNumbersι_appLE (U : X.Opens) (V : X.Opens) (e : V ≤ X.dualNumbersι ⁻¹ᵁ U)
    (x : Γ(X.dualNumbers, U)) :
    X.dualNumbersι.appLE U V e x = X.presheaf.map (homOfLE e).op (x.fst : Γ(X, U)) :=
  rfl

theorem Hom.dualNumbers_appLE (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f.dualNumbers ⁻¹ᵁ U) (x : Γ(Y.dualNumbers, U)) :
    f.dualNumbers.appLE U V e x = DualNumber.mapRingHom (f.appLE U V e).hom x := by
  change DualNumber.mapRingHom (X.presheaf.map (homOfLE e).op).hom
    (DualNumber.mapRingHom (f.app U).hom x) = _
  exact (RingHom.congr_fun (DualNumber.mapRingHom_comp (f.app U).hom
    (X.presheaf.map (homOfLE e).op).hom) x).symm

@[simp]
theorem fst_dualNumbers_appLE (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f.dualNumbers ⁻¹ᵁ U) (x : Γ(Y.dualNumbers, U)) :
    (f.dualNumbers.appLE U V e x).fst = f.appLE U V e (x.fst : Γ(Y, U)) := by
  rw [Hom.dualNumbers_appLE, DualNumber.fst_mapRingHom]

@[simp]
theorem snd_dualNumbers_appLE (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f.dualNumbers ⁻¹ᵁ U) (x : Γ(Y.dualNumbers, U)) :
    (f.dualNumbers.appLE U V e x).snd = f.appLE U V e (x.snd : Γ(Y, U)) := by
  rw [Hom.dualNumbers_appLE, DualNumber.snd_mapRingHom]

theorem dualNumbersMul_appLE (U : X.Opens) (V : X.Opens) (e : V ≤ X.dualNumbersMul ⁻¹ᵁ U)
    (x : Γ(X.dualNumbers, U)) :
    X.dualNumbersMul.appLE U V e x =
      DualNumber.mulRingHom (DualNumber.mapRingHom (X.presheaf.map (homOfLE e).op).hom x) := by
  change DualNumber.mapRingHom (DualNumber.mapRingHom (X.presheaf.map (homOfLE e).op).hom)
    (DualNumber.mulRingHom x) = _
  rw [← RingHom.comp_apply, DualNumber.mapRingHom_mapRingHom_comp_mulRingHom]
  rfl

/-! ### Morphisms of schemes through their actions on sections -/

/-- Two morphisms of schemes with the same underlying map are equal if they agree on sections,
in the form of `Scheme.Hom.appLE`. -/
theorem Hom.ext_appLE {f g : X ⟶ Y} (hb : f.base = g.base)
    (h : ∀ (U : Y.Opens) (V : X.Opens) (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U),
      f.appLE U V e₁ = g.appLE U V e₂) : f = g := by
  refine Scheme.Hom.ext hb fun U ↦ ?_
  rw [← Hom.appLE_eq_app, Hom.appLE_map]
  exact (h U _ _ le_rfl).trans (Hom.appLE_eq_app g)

theorem Hom.appLE_comp {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (W : Y.Opens)
    (V : X.Opens) (e₁ : W ≤ g ⁻¹ᵁ U) (e₂ : V ≤ f ⁻¹ᵁ W) (e : V ≤ (f ≫ g) ⁻¹ᵁ U) :
    (f ≫ g).appLE U V e = g.appLE U W e₁ ≫ f.appLE W V e₂ :=
  (Hom.appLE_comp_appLE f g U W V e₁ e₂).symm

theorem Hom.appLE_comp_apply {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (W : Y.Opens) (V : X.Opens) (e₁ : W ≤ g ⁻¹ᵁ U) (e₂ : V ≤ f ⁻¹ᵁ W)
    (e : V ≤ (f ≫ g) ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (f ≫ g).appLE U V e a = f.appLE W V e₂ (g.appLE U W e₁ a) := by
  rw [Hom.appLE_comp f g U W V e₁ e₂]
  rfl

@[simp]
theorem Hom.id_appLE_apply (U V : X.Opens) (e : V ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (a : Γ(X, U)) :
    (𝟙 X : X ⟶ X).appLE U V e a = X.presheaf.map (homOfLE e).op a :=
  rfl

@[simp]
theorem Hom.appLE_map_apply (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (i : op V ⟶ op V') (a : Γ(Y, U)) :
    X.presheaf.map i (f.appLE U V e a) = f.appLE U V' (i.unop.le.trans e) a := by
  rw [← CommRingCat.comp_apply, Hom.appLE_map]

@[simp]
theorem Hom.map_appLE_apply (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (i : op U' ⟶ op U) (a : Γ(Y, U')) :
    f.appLE U V e (Y.presheaf.map i a) =
      f.appLE U' V (e.trans ((Opens.map f.base).map i.unop).le) a := by
  rw [← CommRingCat.comp_apply, Hom.map_appLE]

theorem presheaf_map_map_apply (X : Scheme.{u}) {U V W : X.Opens} (i : op U ⟶ op V)
    (j : op V ⟶ op W) (k : op U ⟶ op W) (a : Γ(X, U)) :
    X.presheaf.map j (X.presheaf.map i a) = X.presheaf.map k a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-! ### The morphism `T ⟶ T[ε]`, `ε ↦ t` -/

/-- The restriction of a global function to an open. -/
abbrev restrictTop (t : Γ(X, ⊤)) (U : X.Opens) : Γ(X, U) :=
  X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op t

theorem restrictTop_mul_self {t : Γ(X, ⊤)} (ht : t * t = 0) (U : X.Opens) :
    restrictTop t U * restrictTop t U = 0 := by
  rw [← map_mul, ht, map_zero]

theorem presheaf_map_restrictTop (t : Γ(X, ⊤)) {U V : X.Opens} (i : op U ⟶ op V) :
    X.presheaf.map i (restrictTop t U) = restrictTop t V := by
  rw [restrictTop, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The morphism of presheaves `𝒪_X[ε] ⟶ 𝒪_X`, `a + εb ↦ a + tb`, for a global function `t` of
square zero. -/
noncomputable def dualNumbersEval (t : Γ(X, ⊤)) (ht : t * t = 0) :
    X.presheaf ⋙ CommRingCat.dualNumber ⟶ X.presheaf where
  app U := CommRingCat.ofHom (DualNumber.evalRingHom (restrictTop t U.unop)
    (restrictTop_mul_self ht U.unop))
  naturality U V i := by
    ext x
    exact DualNumber.evalRingHom_mapRingHom (X.presheaf.map i).hom _
      (restrictTop_mul_self ht U.unop) _ (restrictTop_mul_self ht V.unop)
      (presheaf_map_restrictTop t i) x

/-- The morphism `X ⟶ X[ε]` attached to a global function `t` of square zero: the identity on
points and `a + εb ↦ a + tb` on functions. Its composite with the projection is the identity, and
every morphism `X ⟶ S[ε]` over `S` factors through it (`eq_dualNumbersLift_comp_dualNumbers`). -/
noncomputable def dualNumbersLift (t : Γ(X, ⊤)) (ht : t * t = 0) : X ⟶ X.dualNumbers where
  base := 𝟙 _
  c := dualNumbersEval t ht ≫ (TopCat.Presheaf.Pushforward.id _).inv
  prop x := by
    constructor
    intro s hs
    obtain ⟨U, hxU, g, rfl⟩ := X.dualNumbers.presheaf.exists_germ_eq s
    rw [PresheafedSpace.stalkMap_germ_apply] at hs
    change IsUnit (X.presheaf.germ U x hxU
      ((g : DualNumber Γ(X, U)).fst + restrictTop t U * g.snd)) at hs
    refine (X.presheaf.isUnit_germ_dualNumber_iff x U hxU g).2 ?_
    rw [map_add] at hs
    have hn : IsNilpotent (-X.presheaf.germ U x hxU (restrictTop t U * g.snd)) := by
      refine ⟨2, ?_⟩
      rw [neg_sq, ← map_pow, mul_pow, sq, restrictTop_mul_self ht, zero_mul, map_zero]
    simpa using hn.isUnit_add_right_of_commute hs (Commute.all _ _)

variable (t : Γ(X, ⊤)) (ht : t * t = 0)

@[simp]
theorem dualNumbersLift_base : (X.dualNumbersLift t ht).base = 𝟙 _ :=
  rfl

theorem dualNumbersLift_appLE (U : X.Opens) (V : X.Opens) (e : V ≤ X.dualNumbersLift t ht ⁻¹ᵁ U)
    (x : Γ(X.dualNumbers, U)) :
    (X.dualNumbersLift t ht).appLE U V e x =
      X.presheaf.map (homOfLE e).op (x.fst : Γ(X, U)) +
        restrictTop t V * X.presheaf.map (homOfLE e).op (x.snd : Γ(X, U)) := by
  change X.presheaf.map (homOfLE e).op ((x : DualNumber Γ(X, U)).fst + restrictTop t U * x.snd) = _
  rw [map_add, map_mul]
  congr 2
  exact presheaf_map_restrictTop t _

@[reassoc (attr := simp)]
theorem dualNumbersLift_comp_proj : X.dualNumbersLift t ht ≫ X.dualNumbersProj = 𝟙 X := by
  refine Hom.ext_appLE rfl fun U V e₁ e₂ ↦ ?_
  ext a
  rw [Hom.appLE_comp_apply (X.dualNumbersLift t ht) X.dualNumbersProj U U V le_rfl e₁,
    dualNumbersProj_appLE, dualNumbersLift_appLE]
  simp only [fst_inl, snd_inl, map_zero, mul_zero, add_zero]
  exact presheaf_map_map_apply _ _ _ _ a

/-- The square-zero function `h^♯(ε)` on `T` attached to a morphism `h : T ⟶ S[ε]`. -/
noncomputable def Hom.dualNumbersParam (h : X ⟶ Y.dualNumbers) : Γ(X, ⊤) :=
  h.appTop (inr 1 : DualNumber Γ(Y, ⊤))

theorem Hom.dualNumbersParam_mul_self (h : X ⟶ Y.dualNumbers) :
    h.dualNumbersParam * h.dualNumbersParam = 0 := by
  rw [Hom.dualNumbersParam, ← map_mul]
  exact (congrArg _ (inr_mul_inr _ _ _)).trans (map_zero _)

/-- A morphism `h : T ⟶ S[ε]` with `h ≫ p = x` is `T ⟶ T[ε] ⟶ S[ε]`, `ε ↦ h^♯(ε)` followed by
`x[ε]`: on functions, `h^♯(a + εb) = x^♯(a) + h^♯(ε) x^♯(b)`. -/
theorem eq_dualNumbersLift_comp_dualNumbers (h : X ⟶ Y.dualNumbers) (x : X ⟶ Y)
    (hx : h ≫ Y.dualNumbersProj = x) :
    h = X.dualNumbersLift h.dualNumbersParam h.dualNumbersParam_mul_self ≫ x.dualNumbers := by
  subst hx
  refine Hom.ext_appLE rfl fun U V e₁ e₂ ↦ ?_
  ext y
  rw [Hom.appLE_comp_apply (X.dualNumbersLift _ _) (h ≫ Y.dualNumbersProj).dualNumbers U V V e₂
    le_rfl, dualNumbersLift_appLE, fst_dualNumbers_appLE, snd_dualNumbers_appLE,
    Hom.appLE_comp_apply h Y.dualNumbersProj U U V le_rfl e₁,
    Hom.appLE_comp_apply h Y.dualNumbersProj U U V le_rfl e₁, dualNumbersProj_appLE',
    dualNumbersProj_appLE']
  have hy : @Eq (DualNumber Γ(Y, U)) y
      (inl (y : DualNumber Γ(Y, U)).fst + @HMul.hMul (DualNumber Γ(Y, U)) (DualNumber Γ(Y, U))
        (DualNumber Γ(Y, U)) _ (inl y.snd) (Y.dualNumbers.presheaf.map
        (homOfLE le_top : U ⟶ ⊤).op (inr 1 : DualNumber Γ(Y, ⊤)))) := by
    rw [dualNumbers_presheaf_map_apply]
    ext <;> simp
  conv_lhs => rw [hy]
  rw [map_add, map_mul]
  simp only [Hom.dualNumbersParam, restrictTop, Hom.app_eq_appLE, Hom.map_appLE_apply]
  erw [Hom.appLE_map_apply, Hom.appLE_map_apply, Hom.appLE_map_apply]
  rw [mul_comm]
  rfl

end Scheme

end AlgebraicGeometry
