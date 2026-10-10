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

theorem presheaf_map_map_apply_of_comp (X : Scheme.{u}) {U V W : X.Opens} (i : op U ⟶ op V)
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
  exact presheaf_map_map_apply_of_comp _ _ _ _ a

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

theorem dualNumbersLift_congr {t t' : Γ(X, ⊤)} (ht : t * t = 0) (ht' : t' * t' = 0) (h : t = t') :
    X.dualNumbersLift t ht = X.dualNumbersLift t' ht' := by
  subst h
  rfl

@[simp]
theorem Hom.dualNumbers_appTop_inr_one (f : X ⟶ Y) :
    f.dualNumbers.appTop (inr 1 : DualNumber Γ(Y, ⊤)) = (inr 1 : DualNumber Γ(X, ⊤)) := by
  change DualNumber.mapRingHom (f.appTop).hom (inr 1) = inr 1
  ext <;> simp

/-- The parameter of `h ≫ f[ε]` is that of `h`. -/
theorem Hom.dualNumbersParam_comp_dualNumbers {T : Scheme.{u}} (h : T ⟶ X.dualNumbers)
    (f : X ⟶ Y) : (h ≫ f.dualNumbers).dualNumbersParam = h.dualNumbersParam := by
  rw [Hom.dualNumbersParam, Hom.comp_appTop, CommRingCat.comp_apply,
    Hom.dualNumbers_appTop_inr_one]
  rfl

open CategoryTheory.Limits in
/-- The thickening `X[ε]` of a scheme `X` over `Y` is the base change of `Y[ε] ⟶ Y`:
a morphism `T ⟶ X[ε]` is a morphism `T ⟶ X` together with a square-zero function on `T`. -/
theorem isPullback_dualNumbers (f : X ⟶ Y) :
    IsPullback f.dualNumbers X.dualNumbersProj Y.dualNumbersProj f := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (Hom.dualNumbers_comp_proj f)
    (fun s ↦ s.pt.dualNumbersLift s.fst.dualNumbersParam s.fst.dualNumbersParam_mul_self ≫
      s.snd.dualNumbers) (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_))
  · rw [Category.assoc, ← Hom.dualNumbers_comp, ← s.condition]
    exact (eq_dualNumbersLift_comp_dualNumbers s.fst _ rfl).symm
  · rw [Category.assoc, Hom.dualNumbers_comp_proj, dualNumbersLift_comp_proj_assoc]
  · rw [eq_dualNumbersLift_comp_dualNumbers m s.snd h₂]
    congr 1
    apply dualNumbersLift_congr
    rw [← h₁, Hom.dualNumbersParam_comp_dualNumbers]

/-! ### Endomorphisms of the thickening on sections -/

theorem Hom.appLE_eq_of_eq {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V e₁ = g.appLE U V e₂ := by
  subst h
  rfl

theorem Hom.appLE_apply_eq_of_eq {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) (a : Γ(Y, U)) : f.appLE U V e₁ a = g.appLE U V e₂ a := by
  subst h
  rfl

theorem Hom.appLE_heq_app (f : X ⟶ Y) (U : Y.Opens) {W : X.Opens} (hW : W = f ⁻¹ᵁ U)
    (e : W ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) : f.appLE U W e x ≍ f.app U x := by
  subst hW
  rw [Hom.app_eq_appLE]

@[simp]
theorem presheaf_map_self_apply (X : Scheme.{u}) {U : X.Opens} (i : op U ⟶ op U) (a : Γ(X, U)) :
    X.presheaf.map i a = a := by
  rw [Subsingleton.elim i (𝟙 _), CategoryTheory.Functor.map_id]
  rfl

theorem dualNumbersProj_appLE_self (U : X.Opens) (e : U ≤ X.dualNumbersProj ⁻¹ᵁ U)
    (a : Γ(X, U)) :
    (X.dualNumbersProj.appLE U U e a : DualNumber Γ(X, U)) = (inl a : DualNumber Γ(X, U)) := by
  change DualNumber.mapRingHom (X.presheaf.map (homOfLE e).op).hom (inl a) = _
  ext
  · exact (DualNumber.fst_mapRingHom _ _).trans (presheaf_map_self_apply X _ a)
  · exact (DualNumber.snd_mapRingHom _ _).trans (map_zero _)

theorem dualNumbersMul_appLE_self (U : X.Opens) (e : U ≤ X.dualNumbersMul ⁻¹ᵁ U)
    (x : Γ(X.dualNumbers, U)) :
    (X.dualNumbersMul.appLE U U e x : DualNumber (DualNumber Γ(X, U))) =
      DualNumber.mulRingHom (x : DualNumber Γ(X, U)) := by
  rw [dualNumbersMul_appLE]
  congr 1
  ext
  · exact (DualNumber.fst_mapRingHom _ _).trans (presheaf_map_self_apply X _ _)
  · exact (DualNumber.snd_mapRingHom _ _).trans (presheaf_map_self_apply X _ _)

theorem Hom.dualNumbers_appLE_self (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f.dualNumbers ⁻¹ᵁ U) (x : Γ(Y.dualNumbers, U)) :
    f.dualNumbers.appLE U V e x =
      DualNumber.mapRingHom (f.appLE U V e).hom (x : DualNumber Γ(Y, U)) :=
  Hom.dualNumbers_appLE f U V e x

/-- A morphism `h : X[ε] ⟶ Y` restricting to `g : X ⟶ Y` along `ε ↦ 0` has the same underlying
map as `g`, so it maps an open `V` with `V ≤ g⁻¹U` into `U`. -/
theorem le_preimage_of_dualNumbersι_comp {h : X.dualNumbers ⟶ Y} {g : X ⟶ Y}
    (hh : X.dualNumbersι ≫ h = g) {U : Y.Opens} {V : X.Opens} (e : V ≤ g ⁻¹ᵁ U) :
    V ≤ h ⁻¹ᵁ U := by
  intro x hx
  have := e hx
  rw [← hh] at this
  exact this

theorem le_preimage_of_comp_dualNumbersProj {h : Y ⟶ X.dualNumbers} {g : Y ⟶ X}
    (hh : h ≫ X.dualNumbersProj = g) {U : X.Opens} {V : Y.Opens} (e : V ≤ g ⁻¹ᵁ U) :
    V ≤ h ⁻¹ᵁ U := by
  intro x hx
  have := e hx
  rw [← hh] at this
  exact this

/-- An endomorphism `Λ` of `X[ε]` fixing the global function `ε` fixes its restrictions. -/
theorem appLE_inr_one (Λ : X.dualNumbers ⟶ X.dualNumbers)
    (hε : Λ.appTop (inr 1 : DualNumber Γ(X, ⊤)) = (inr 1 : DualNumber Γ(X, ⊤))) (U : X.Opens)
    (V : X.Opens) (e : V ≤ Λ ⁻¹ᵁ U) :
    (Λ.appLE U V e (inr 1 : DualNumber Γ(X, U)) : DualNumber Γ(X, V)) = inr 1 := by
  have h : (inr 1 : DualNumber Γ(X, U)) = X.dualNumbers.presheaf.map
      (homOfLE (le_top : (U : X.dualNumbers.Opens) ≤ ⊤)).op (inr 1 : DualNumber Γ(X, ⊤)) := by
    change _ = DualNumber.mapRingHom _ _
    ext <;> simp
  have h2 : Λ.appLE U V e (X.dualNumbers.presheaf.map
      (homOfLE (le_top : (U : X.dualNumbers.Opens) ≤ ⊤)).op (inr 1 : DualNumber Γ(X, ⊤))) =
        X.dualNumbers.presheaf.map (homOfLE (le_top : (V : X.dualNumbers.Opens) ≤ ⊤)).op
          (Λ.appTop (inr 1 : DualNumber Γ(X, ⊤))) := by
    rw [Hom.map_appLE_apply, Hom.appTop, Hom.app_eq_appLE]
    exact (Hom.appLE_map_apply Λ _ _ _).symm
  refine (congrArg (Λ.appLE U V e) h).trans (h2.trans ?_)
  change DualNumber.mapRingHom _ (Λ.appTop _) = _
  rw [hε]
  ext <;> simp

/-- An endomorphism `Λ` of `X[ε]` fixing `ε` acts on a function `a + εb` through the morphism
`Λ ≫ p : X[ε] ⟶ X`: `Λ^♯(a + εb) = (Λ ≫ p)^♯(a) + ε (Λ ≫ p)^♯(b)`. -/
theorem appLE_dualNumbers_self (Λ : X.dualNumbers ⟶ X.dualNumbers)
    (hε : Λ.appTop (inr 1 : DualNumber Γ(X, ⊤)) = (inr 1 : DualNumber Γ(X, ⊤))) (U : X.Opens)
    (e : U ≤ Λ ⁻¹ᵁ U) (e' : U ≤ (Λ ≫ X.dualNumbersProj) ⁻¹ᵁ U) (z : Γ(X.dualNumbers, U)) :
    (Λ.appLE U U e z).fst = ((Λ ≫ X.dualNumbersProj).appLE U U e' z.fst).fst ∧
    (Λ.appLE U U e z).snd = ((Λ ≫ X.dualNumbersProj).appLE U U e' z.fst).snd +
      ((Λ ≫ X.dualNumbersProj).appLE U U e' z.snd).fst := by
  let φ : DualNumber Γ(X, U) →+* DualNumber Γ(X, U) := (Λ.appLE U U e).hom
  let ψ : Γ(X, U) →+* DualNumber Γ(X, U) := ((Λ ≫ X.dualNumbersProj).appLE U U e').hom
  have hinl (b : Γ(X, U)) : φ (inl b) = ψ b := by
    rw [← dualNumbersProj_appLE_self U le_rfl b]
    exact (Hom.appLE_comp_apply Λ X.dualNumbersProj U U U le_rfl e e' b).symm
  have hinr : φ (inr 1) = inr 1 := appLE_inr_one Λ hε U U e
  let z' : DualNumber Γ(X, U) := z
  have hz : z' = inl z'.fst + inr 1 * inl z'.snd := by ext <;> simp
  have key : φ z' = ψ z'.fst + inr 1 * ψ z'.snd := by
    conv_lhs => rw [hz]
    rw [map_add, map_mul, hinl, hinl, hinr]
  have h1 := congrArg TrivSqZeroExt.fst key
  have h2 := congrArg TrivSqZeroExt.snd key
  simp only [fst_add, fst_mul, fst_inr, zero_mul, add_zero] at h1
  simp only [snd_add, snd_mul, snd_inr, fst_inr, smul_eq_mul, op_smul_eq_mul, one_mul,
    zero_mul, zero_add] at h2
  exact ⟨h1, h2⟩

/-- A morphism fixing a global function fixes its restrictions. -/
theorem appLE_presheaf_map_top (f : X ⟶ Y) {t : Γ(Y, ⊤)} {t' : Γ(X, ⊤)} (ht : f.appTop t = t')
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e (Y.presheaf.map (homOfLE le_top : U ⟶ ⊤).op t) =
      X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op t' := by
  rw [Hom.map_appLE_apply, ← ht, Hom.appTop, Hom.app_eq_appLE]
  exact (Hom.appLE_map_apply f _ _ _).symm

theorem dualNumbers_dualNumbers_presheaf_map_top_inr (U : X.Opens) :
    X.dualNumbers.dualNumbers.presheaf.map
      (homOfLE (le_top : (U : X.dualNumbers.dualNumbers.Opens) ≤ ⊤)).op
      (inr 1 : DualNumber (DualNumber Γ(X, ⊤))) =
        (inr 1 : DualNumber (DualNumber Γ(X, U))) := by
  change DualNumber.mapRingHom _ _ = _
  ext <;> simp

theorem dualNumbers_dualNumbers_presheaf_map_top_inl_inr (U : X.Opens) :
    X.dualNumbers.dualNumbers.presheaf.map
      (homOfLE (le_top : (U : X.dualNumbers.dualNumbers.Opens) ≤ ⊤)).op
      (inl (inr 1) : DualNumber (DualNumber Γ(X, ⊤))) =
        (inl (inr 1) : DualNumber (DualNumber Γ(X, U))) := by
  change DualNumber.mapRingHom _ _ = _
  have : (X.dualNumbers.presheaf.map
      (homOfLE (le_top : (U : X.dualNumbers.Opens) ≤ ⊤)).op).hom DualNumber.eps =
        DualNumber.eps := by
    change DualNumber.mapRingHom _ _ = _
    ext <;> simp
  ext <;> simp [this]


theorem dualNumbers_dualNumbersProj_comp_appLE_self (U : X.Opens)
    (e : U ≤ (X.dualNumbers.dualNumbersProj ≫ X.dualNumbersProj) ⁻¹ᵁ U) (a : Γ(X, U)) :
    ((X.dualNumbers.dualNumbersProj ≫ X.dualNumbersProj).appLE U U e a :
      DualNumber (DualNumber Γ(X, U))) = inl (inl a) := by
  refine (Hom.appLE_comp_apply X.dualNumbers.dualNumbersProj X.dualNumbersProj U U U le_rfl le_rfl
    e a).trans ?_
  have h1 : X.dualNumbersProj.appLE U U le_rfl a = (inl a : DualNumber Γ(X, U)) :=
    dualNumbersProj_appLE_self U le_rfl a
  rw [h1]
  exact dualNumbersProj_appLE_self (X := X.dualNumbers) U le_rfl _

/-- An endomorphism `Λ` of `X[ε][δ]` fixing `ε` and `δ` acts on a function
`a + εb + δc + εδd` through the morphism `Λ ≫ p ≫ p : X[ε][δ] ⟶ X`. -/
theorem appLE_dualNumbers_dualNumbers_self
    (Λ : X.dualNumbers.dualNumbers ⟶ X.dualNumbers.dualNumbers)
    (hδ : Λ.appTop (inr 1 : DualNumber (DualNumber Γ(X, ⊤))) = inr 1)
    (hε : Λ.appTop (inl (inr 1) : DualNumber (DualNumber Γ(X, ⊤))) = inl (inr 1)) (U : X.Opens)
    (e : U ≤ Λ ⁻¹ᵁ U)
    (e' : U ≤ (Λ ≫ X.dualNumbers.dualNumbersProj ≫ X.dualNumbersProj) ⁻¹ᵁ U)
    (z : Γ(X.dualNumbers.dualNumbers, U)) :
    let A := (Λ ≫ X.dualNumbers.dualNumbersProj ≫ X.dualNumbersProj).appLE U U e'
    (Λ.appLE U U e z).fst.fst = (A z.fst.fst).fst.fst ∧
    (Λ.appLE U U e z).fst.snd = (A z.fst.fst).fst.snd + (A z.fst.snd).fst.fst ∧
    (Λ.appLE U U e z).snd.fst = (A z.fst.fst).snd.fst + (A z.snd.fst).fst.fst ∧
    (Λ.appLE U U e z).snd.snd = (A z.fst.fst).snd.snd + (A z.fst.snd).snd.fst +
      (A z.snd.fst).fst.snd + (A z.snd.snd).fst.fst := by
  intro A
  let φ : DualNumber (DualNumber Γ(X, U)) →+* DualNumber (DualNumber Γ(X, U)) :=
    (Λ.appLE U U e).hom
  let ψ : Γ(X, U) →+* DualNumber (DualNumber Γ(X, U)) := A.hom
  have hinl (b : Γ(X, U)) : φ (inl (inl b)) = ψ b := by
    rw [← dualNumbers_dualNumbersProj_comp_appLE_self U le_rfl b]
    exact (Hom.appLE_comp_apply Λ _ U U U le_rfl e e' b).symm
  have hinr : φ (inr 1) = inr 1 := by
    have := appLE_presheaf_map_top Λ hδ U U e
    rw [dualNumbers_dualNumbers_presheaf_map_top_inr] at this
    exact this
  have hinlr : φ (inl (inr 1)) = inl (inr 1) := by
    have := appLE_presheaf_map_top Λ hε U U e
    rw [dualNumbers_dualNumbers_presheaf_map_top_inl_inr] at this
    exact this
  let z' : DualNumber (DualNumber Γ(X, U)) := z
  have hz : z' = inl (inl z'.fst.fst) + inl (inr 1) * inl (inl z'.fst.snd) +
      inr 1 * inl (inl z'.snd.fst) + inl (inr 1) * inr 1 * inl (inl z'.snd.snd) := by
    ext <;> simp
  have key : φ z' = ψ z'.fst.fst + inl (inr 1) * ψ z'.fst.snd + inr 1 * ψ z'.snd.fst +
      inl (inr 1) * inr 1 * ψ z'.snd.snd := by
    conv_lhs => rw [hz]
    simp only [map_add, map_mul, hinl, hinr, hinlr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun x ↦ x.fst.fst) key
    simp only [fst_add, fst_mul, fst_inl, fst_inr,
      mul_zero, zero_mul, add_zero] at h
    exact h
  · have h := congrArg (fun x ↦ x.fst.snd) key
    simp only [fst_add, snd_add, fst_mul, snd_mul, fst_inl, fst_inr, snd_inr,
      smul_eq_mul, op_smul_eq_mul, mul_zero, zero_mul, add_zero, zero_add, one_mul] at h
    exact h
  · have h := congrArg (fun x ↦ x.snd.fst) key
    simp only [fst_add, snd_add, fst_mul, snd_mul, fst_inl, snd_inl, fst_inr, snd_inr,
      smul_eq_mul, op_smul_eq_mul, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] at h
    exact h
  · have h := congrArg (fun x ↦ x.snd.snd) key
    simp only [snd_add, fst_mul, snd_mul, fst_inl, snd_inl, fst_inr, snd_inr,
      smul_eq_mul, op_smul_eq_mul, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] at h
    exact h

end Scheme

end AlgebraicGeometry
