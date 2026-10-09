/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.AlgebraicGeometry.DualNumbers.Retraction

/-!
# Infinitesimal right translations of a group scheme

Let `G` be a group scheme over `S`. A point `x : S[ε] ⟶ G` over `S` gives the *right translation*
`ρ_x : G[ε] ⟶ G`, `(g, t) ↦ g · x(t)` (`AlgebraicGeometry.GrpObj.rightTranslation`). If `x`
reduces to the identity along `ε ↦ 0`, then `ρ_x` restricts to the identity of `G`, so it acts on
functions by `ρ_x^♯(a) = a + ε D_x(a)` for an operator `D_x` on the sections of `𝒪_G`
(`AlgebraicGeometry.GrpObj.rightTranslationDeriv`), the left-invariant vector field extending the
tangent vector `x`. Since `G[ε] = G ×_S S[ε]`, the translation `ρ_x` lifts to an automorphism
`(g, t) ↦ (g · x(t), t)` of `G[ε]` over `S[ε]`, and `ρ_{xy}` is this lift followed by `ρ_y`; on
functions this gives `D_{xy} = D_x + D_y` (`AlgebraicGeometry.GrpObj.rightTranslationDeriv_mul`).

Similarly a point `z : S[ε][δ] ⟶ G` reducing to the identity along `ε, δ ↦ 0` acts on functions
through an operator `1 + ε D₁ + δ D₂ + εδ D₁₂`, multiplicatively in `z`
(`AlgebraicGeometry.GrpObj.rightTranslationOp₂_mul`). For the commutator of `x_ε` and `y_δ` this
operator is `1 + εδ (D_x D_y - D_y D_x)`: the Lie bracket of left-invariant vector fields.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt Opposite MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

namespace Scheme

/-! ### Thickenings of schemes over `S` -/

section Thickening

variable {X Y : Scheme.{u}}

@[simp]
theorem dualNumbersMul_base : X.dualNumbersMul.base = 𝟙 _ :=
  rfl

@[simp]
theorem Hom.dualNumbers_base (f : X ⟶ Y) : f.dualNumbers.base = f.base :=
  rfl

/-- The map `η ↦ εδ` is natural. -/
@[reassoc]
theorem dualNumbersMul_comp_dualNumbers (f : X ⟶ Y) :
    X.dualNumbersMul ≫ f.dualNumbers = f.dualNumbers.dualNumbers ≫ Y.dualNumbersMul := by
  refine Hom.ext_appLE (by simp) fun U V e₁ e₂ ↦ ?_
  ext x
  rw [Hom.appLE_comp_apply X.dualNumbersMul f.dualNumbers U V V e₁ le_rfl,
    Hom.appLE_comp_apply f.dualNumbers.dualNumbers Y.dualNumbersMul U U V le_rfl e₂]
  have h1 := dualNumbersMul_appLE_self (X := X) V le_rfl (f.dualNumbers.appLE U V e₁ x)
  have h2 := Hom.dualNumbers_appLE f U V e₁ x
  have h3 := dualNumbersMul_appLE_self (X := Y) U le_rfl x
  have h4 := Hom.dualNumbers_appLE f.dualNumbers U V e₂ (Y.dualNumbersMul.appLE U U le_rfl x)
  refine h1.trans (Eq.trans ?_ h4.symm)
  rw [h2, h3]
  have h5 (y : DualNumber Γ(Y, U)) :
      (f.dualNumbers.appLE U V e₂).hom y = DualNumber.mapRingHom (f.appLE U V e₁).hom y :=
    Hom.dualNumbers_appLE f U V e₂ y
  have h6 : (f.dualNumbers.appLE U V e₂).hom = DualNumber.mapRingHom (f.appLE U V e₁).hom :=
    RingHom.ext h5
  rw [h6]
  exact (RingHom.congr_fun (DualNumber.mapRingHom_mapRingHom_comp_mulRingHom
    (f.appLE U V e₁).hom) x).symm

variable {S : Scheme.{u}} (Y : Over S)

/-- The thickening `Y[ε]` of a scheme `Y` over `S`, as a scheme over `S`. -/
noncomputable def overDualNumbers : Over S :=
  Over.mk (Y.left.dualNumbersProj ≫ Y.hom)

/-- The projection `Y[ε] ⟶ Y` over `S`. -/
noncomputable def overDualNumbersProj : overDualNumbers Y ⟶ Y :=
  Over.homMk Y.left.dualNumbersProj rfl

/-- The morphism `Y[ε] ⟶ S[ε]` over `S`. -/
noncomputable def overDualNumbersMap : overDualNumbers Y ⟶ dualNumbersOver S :=
  Over.homMk Y.hom.dualNumbers (Hom.dualNumbers_comp_proj Y.hom)

/-- The closed immersion `Y ⟶ Y[ε]`, `ε ↦ 0`, over `S`. -/
noncomputable def overDualNumbersι : Y ⟶ overDualNumbers Y :=
  Over.homMk Y.left.dualNumbersι (by simp [overDualNumbers])

theorem isPullback_overDualNumbers :
    IsPullback (overDualNumbersMap Y).left (overDualNumbersProj Y).left
      (dualNumbersOver S).hom Y.hom :=
  isPullback_dualNumbers Y.hom

theorem overDualNumbersι_comp_overDualNumbersMap :
    overDualNumbersι Y ≫ overDualNumbersMap Y = toUnit Y ≫ dualNumbersιOver S := by
  ext1
  simp [overDualNumbersι, overDualNumbersMap, Over.toUnit_left]

/-- The thickening `Y[ε][δ]` of a scheme `Y` over `S`, as a scheme over `S`. -/
noncomputable def overDualNumbers₂ : Over S :=
  Over.mk (Y.left.dualNumbers.dualNumbersProj ≫ Y.left.dualNumbersProj ≫ Y.hom)

/-- The projection `Y[ε][δ] ⟶ Y` over `S`. -/
noncomputable def overDualNumbers₂Proj : overDualNumbers₂ Y ⟶ Y :=
  Over.homMk (Y.left.dualNumbers.dualNumbersProj ≫ Y.left.dualNumbersProj) (Category.assoc _ _ _)

/-- The morphism `Y[ε][δ] ⟶ S[ε][δ]` over `S`. -/
noncomputable def overDualNumbers₂Map : overDualNumbers₂ Y ⟶ dualNumbers₂Over S :=
  Over.homMk Y.hom.dualNumbers.dualNumbers (by
    simp [overDualNumbers₂, dualNumbers₂Over, Hom.dualNumbers_comp_proj_assoc])

/-- The closed immersion `Y ⟶ Y[ε][δ]`, `ε, δ ↦ 0`, over `S`. -/
noncomputable def overDualNumbers₂ι : Y ⟶ overDualNumbers₂ Y :=
  Over.homMk (Y.left.dualNumbersι ≫ Y.left.dualNumbers.dualNumbersι)
    (by simp [overDualNumbers₂])

/-- The projection `Y[ε][δ] ⟶ Y[ε]` forgetting `δ`, over `S`. -/
noncomputable def overDualNumbers₂ProjFst : overDualNumbers₂ Y ⟶ overDualNumbers Y :=
  Over.homMk Y.left.dualNumbers.dualNumbersProj (by simp [overDualNumbers₂, overDualNumbers])

/-- The projection `Y[ε][δ] ⟶ Y[δ]` forgetting `ε`, over `S`. -/
noncomputable def overDualNumbers₂ProjSnd : overDualNumbers₂ Y ⟶ overDualNumbers Y :=
  Over.homMk Y.left.dualNumbersProj.dualNumbers
    (by simp [overDualNumbers₂, overDualNumbers, Hom.dualNumbers_comp_proj_assoc])

/-- The map `Y[ε][δ] ⟶ Y[η]`, `η ↦ εδ`, over `S`. -/
noncomputable def overDualNumbersMul : overDualNumbers₂ Y ⟶ overDualNumbers Y :=
  Over.homMk Y.left.dualNumbersMul (by simp [overDualNumbers₂, overDualNumbers])

theorem isPullback_overDualNumbers₂ :
    IsPullback (overDualNumbers₂Map Y).left (overDualNumbers₂Proj Y).left
      (dualNumbers₂Over S).hom Y.hom :=
  (isPullback_dualNumbers Y.hom.dualNumbers).paste_vert (isPullback_dualNumbers Y.hom)

theorem overDualNumbers₂ι_comp_overDualNumbers₂Map :
    overDualNumbers₂ι Y ≫ overDualNumbers₂Map Y =
      toUnit Y ≫ dualNumbersιOver S ≫ dualNumbersιεOver S := by
  ext1
  simp [overDualNumbers₂ι, overDualNumbers₂Map, Over.toUnit_left, dualNumbersιεOver]

theorem overDualNumbers₂ProjFst_comp_overDualNumbersProj :
    overDualNumbers₂ProjFst Y ≫ overDualNumbersProj Y = overDualNumbers₂Proj Y :=
  rfl

@[reassoc]
theorem overDualNumbers₂ProjFst_comp_overDualNumbersMap :
    overDualNumbers₂ProjFst Y ≫ overDualNumbersMap Y =
      overDualNumbers₂Map Y ≫ dualNumbersProjεOver S := by
  ext1
  simp [overDualNumbers₂ProjFst, overDualNumbersMap, overDualNumbers₂Map, dualNumbersProjεOver]

theorem overDualNumbers₂ProjSnd_comp_overDualNumbersProj :
    overDualNumbers₂ProjSnd Y ≫ overDualNumbersProj Y = overDualNumbers₂Proj Y := by
  ext1
  simp [overDualNumbers₂ProjSnd, overDualNumbersProj, overDualNumbers₂Proj]

@[reassoc]
theorem overDualNumbers₂ProjSnd_comp_overDualNumbersMap :
    overDualNumbers₂ProjSnd Y ≫ overDualNumbersMap Y =
      overDualNumbers₂Map Y ≫ dualNumbersProjδOver S := by
  ext1
  simp [overDualNumbers₂ProjSnd, overDualNumbersMap, overDualNumbers₂Map, dualNumbersProjδOver,
    ← Hom.dualNumbers_comp]

theorem overDualNumbersMul_comp_overDualNumbersProj :
    overDualNumbersMul Y ≫ overDualNumbersProj Y = overDualNumbers₂Proj Y := by
  ext1
  simp [overDualNumbersMul, overDualNumbersProj, overDualNumbers₂Proj]

@[reassoc]
theorem overDualNumbersMul_comp_overDualNumbersMap :
    overDualNumbersMul Y ≫ overDualNumbersMap Y =
      overDualNumbers₂Map Y ≫ dualNumbersMulOver S := by
  ext1
  simp [overDualNumbersMul, overDualNumbersMap, overDualNumbers₂Map, dualNumbersMulOver,
    dualNumbersMul_comp_dualNumbers]

theorem overDualNumbersι_comp_overDualNumbersProj :
    overDualNumbersι Y ≫ overDualNumbersProj Y = 𝟙 Y := by
  ext1
  simp [overDualNumbersι, overDualNumbersProj]

theorem overDualNumbers₂ι_comp_overDualNumbers₂Proj :
    overDualNumbers₂ι Y ≫ overDualNumbers₂Proj Y = 𝟙 Y := by
  ext1
  simp [overDualNumbers₂ι, overDualNumbers₂Proj]

end Thickening

/-- An endomorphism of `Y[ε]` over `S[ε]` fixes the function `ε`. -/
theorem appTop_inr_one_of_comp_dualNumbers {Y S : Scheme.{u}} (Λ : Y.dualNumbers ⟶ Y.dualNumbers)
    (f : Y ⟶ S) (h : Λ ≫ f.dualNumbers = f.dualNumbers) :
    Λ.appTop (inr 1 : DualNumber Γ(Y, ⊤)) = (inr 1 : DualNumber Γ(Y, ⊤)) := by
  have h1 := Hom.dualNumbers_appTop_inr_one f
  calc Λ.appTop (inr 1 : DualNumber Γ(Y, ⊤))
      = Λ.appTop (f.dualNumbers.appTop (inr 1 : DualNumber Γ(S, ⊤))) := by rw [h1]
    _ = (Λ ≫ f.dualNumbers).appTop (inr 1 : DualNumber Γ(S, ⊤)) := by
      rw [Hom.comp_appTop]
      rfl
    _ = inr 1 := by rw [h, h1]

/-- An endomorphism of `Y[ε][δ]` over `S[ε][δ]` fixes the function `δ`. -/
theorem appTop_inr_one_of_comp_dualNumbers_dualNumbers {Y S : Scheme.{u}}
    (Λ : Y.dualNumbers.dualNumbers ⟶ Y.dualNumbers.dualNumbers)
    (f : Y ⟶ S) (h : Λ ≫ f.dualNumbers.dualNumbers = f.dualNumbers.dualNumbers) :
    Λ.appTop (inr 1 : DualNumber (DualNumber Γ(Y, ⊤))) = inr 1 :=
  appTop_inr_one_of_comp_dualNumbers Λ f.dualNumbers h

/-- An endomorphism of `Y[ε][δ]` over `S[ε][δ]` fixes the function `ε`. -/
theorem appTop_inl_inr_one_of_comp_dualNumbers_dualNumbers {Y S : Scheme.{u}}
    (Λ : Y.dualNumbers.dualNumbers ⟶ Y.dualNumbers.dualNumbers)
    (f : Y ⟶ S) (h : Λ ≫ f.dualNumbers.dualNumbers = f.dualNumbers.dualNumbers) :
    Λ.appTop (inl (inr 1) : DualNumber (DualNumber Γ(Y, ⊤))) = inl (inr 1) := by
  have h1 : f.dualNumbers.dualNumbers.appTop (inl (inr 1) : DualNumber (DualNumber Γ(S, ⊤))) =
      (inl (inr 1) : DualNumber (DualNumber Γ(Y, ⊤))) := by
    change DualNumber.mapRingHom (f.dualNumbers.appTop).hom (inl (inr 1)) = _
    have := Hom.dualNumbers_appTop_inr_one f
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [DualNumber.fst_mapRingHom, fst_inl, fst_inl]
      exact this
    · simp
  calc Λ.appTop (inl (inr 1) : DualNumber (DualNumber Γ(Y, ⊤)))
      = Λ.appTop (f.dualNumbers.dualNumbers.appTop
          (inl (inr 1) : DualNumber (DualNumber Γ(S, ⊤)))) := by rw [h1]
    _ = (Λ ≫ f.dualNumbers.dualNumbers).appTop
          (inl (inr 1) : DualNumber (DualNumber Γ(S, ⊤))) := by
      rw [Hom.comp_appTop]
      rfl
    _ = inl (inr 1) := by rw [h, h1]


theorem dualNumbersScale_appLE_self {X : Scheme.{u}} (c : Γ(X, ⊤)) (U : X.Opens)
    (e : U ≤ X.dualNumbersScale c ⁻¹ᵁ U) (x : Γ(X.dualNumbers, U)) :
    (X.dualNumbersScale c).appLE U U e x =
      DualNumber.scale (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op c) (x : DualNumber Γ(X, U)) :=
  presheaf_map_self_apply X.dualNumbers _ _

/-- Scaling the infinitesimal is natural. -/
theorem dualNumbersScale_comp_dualNumbers {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, ⊤)) :
    X.dualNumbersScale (f.appTop r) ≫ f.dualNumbers = f.dualNumbers ≫ Y.dualNumbersScale r := by
  refine Hom.ext_appLE (by simp [dualNumbersScale]) fun U V e₁ e₂ ↦ ?_
  ext x
  rw [Hom.appLE_comp_apply (X.dualNumbersScale (f.appTop r)) f.dualNumbers U V V e₁ le_rfl,
    Hom.appLE_comp_apply f.dualNumbers (Y.dualNumbersScale r) U U V le_rfl e₂]
  let φ : DualNumber Γ(Y, U) →+* DualNumber Γ(X, V) := (f.dualNumbers.appLE U V e₂).hom
  have hφ (y : DualNumber Γ(Y, U)) : φ y = DualNumber.mapRingHom (f.appLE U V e₂).hom y :=
    Hom.dualNumbers_appLE f U V e₂ y
  have h1 := dualNumbersScale_appLE_self (f.appTop r) V le_rfl (f.dualNumbers.appLE U V e₁ x)
  have h2 := dualNumbersScale_appLE_self r U le_rfl x
  have hr : f.appLE U V e₂ (Y.presheaf.map (homOfLE le_top : U ⟶ ⊤).op r) =
      X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (f.appTop r) :=
    appLE_presheaf_map_top f rfl U V e₂
  refine h1.trans (Eq.trans ?_ (congrArg φ h2).symm)
  rw [hφ, Hom.dualNumbers_appLE f U V e₁]
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [DualNumber.fst_scale]
  · simp only [DualNumber.snd_scale, DualNumber.snd_mapRingHom, map_mul]
    rw [← hr]

end Scheme

/-! ### Right translations -/

namespace GrpObj

variable {S : Scheme.{u}} {G : Over S} [GrpObj G]

section PullbackLift

variable {X Z : Over S} (π : Z ⟶ G) (F : Z ⟶ X) (hZ : IsPullback F.left π.left X.hom G.hom)

/-- For `Z = G ×_S X`, the endomorphism `(g, t) ↦ (a(g, t), t)` of `Z`, for `a : Z ⟶ G`. -/
noncomputable def pullbackLift (a : Z ⟶ G) : Z ⟶ Z :=
  Over.homMk (hZ.lift F.left a.left (by rw [Over.w F, Over.w a])) (by
    rw [← Over.w F, ← Category.assoc, hZ.lift_fst])

omit [GrpObj G] in
@[reassoc (attr := simp)]
theorem pullbackLift_comp_snd (a : Z ⟶ G) : pullbackLift π F hZ a ≫ π = a := by
  ext1
  exact hZ.lift_snd _ _ _

omit [GrpObj G] in
@[reassoc (attr := simp)]
theorem pullbackLift_comp_fst (a : Z ⟶ G) : pullbackLift π F hZ a ≫ F = F := by
  ext1
  exact hZ.lift_fst _ _ _

/-- Right translation by `x * y` is right translation by `x`, lifted to `Z`, followed by right
translation by `y`. -/
theorem pullbackLift_comp_mul (x y : X ⟶ G) :
    pullbackLift π F hZ (π * (F ≫ x)) ≫ (π * (F ≫ y)) = π * (F ≫ (x * y)) := by
  rw [MonObj.comp_mul, pullbackLift_comp_snd, pullbackLift_comp_fst_assoc, MonObj.comp_mul,
    mul_assoc]

end PullbackLift

/-! ### One parameter -/

section One

/-- The right translation `ρ_x : G[ε] ⟶ G`, `(g, t) ↦ g · x(t)`, by a point `x : S[ε] ⟶ G`. -/
noncomputable def rightTranslation (x : Scheme.dualNumbersOver S ⟶ G) :
    Scheme.overDualNumbers G ⟶ G :=
  Scheme.overDualNumbersProj G * (Scheme.overDualNumbersMap G ≫ x)

/-- The automorphism `(g, t) ↦ (g · x(t), t)` of `G[ε]` over `S[ε]`. -/
noncomputable def rightTranslationLift (x : Scheme.dualNumbersOver S ⟶ G) :
    Scheme.overDualNumbers G ⟶ Scheme.overDualNumbers G :=
  pullbackLift _ _ (Scheme.isPullback_overDualNumbers G) (rightTranslation x)

theorem rightTranslation_mul (x y : Scheme.dualNumbersOver S ⟶ G) :
    rightTranslation (x * y) = rightTranslationLift x ≫ rightTranslation y :=
  (pullbackLift_comp_mul _ _ _ _ _).symm

theorem rightTranslationLift_comp_overDualNumbersProj (x : Scheme.dualNumbersOver S ⟶ G) :
    rightTranslationLift x ≫ Scheme.overDualNumbersProj G = rightTranslation x :=
  pullbackLift_comp_snd _ _ _ _

theorem rightTranslationLift_comp_overDualNumbersMap (x : Scheme.dualNumbersOver S ⟶ G) :
    rightTranslationLift x ≫ Scheme.overDualNumbersMap G = Scheme.overDualNumbersMap G :=
  pullbackLift_comp_fst _ _ _ _

theorem overDualNumbersι_comp_rightTranslation {x : Scheme.dualNumbersOver S ⟶ G}
    (hx : Scheme.dualNumbersιOver S ≫ x = 1) :
    Scheme.overDualNumbersι G ≫ rightTranslation x = 𝟙 G := by
  rw [rightTranslation, MonObj.comp_mul, ← Category.assoc,
    Scheme.overDualNumbersι_comp_overDualNumbersMap, Category.assoc, hx, MonObj.comp_one,
    Scheme.overDualNumbersι_comp_overDualNumbersProj, mul_one]

theorem dualNumbersι_comp_rightTranslation_left {x : Scheme.dualNumbersOver S ⟶ G}
    (hx : Scheme.dualNumbersιOver S ≫ x = 1) :
    G.left.dualNumbersι ≫ (rightTranslation x).left = 𝟙 G.left :=
  congrArg CommaMorphism.left (overDualNumbersι_comp_rightTranslation hx)

/-- The operator `D_x` on the sections of `𝒪_G` of a point `x : S[ε] ⟶ G` reducing to the
identity: `ρ_x^♯(a) = a + ε D_x(a)`. It is the left-invariant vector field extending `x`. -/
noncomputable def rightTranslationDeriv {x : Scheme.dualNumbersOver S ⟶ G}
    (hx : Scheme.dualNumbersιOver S ≫ x = 1) (U : G.left.Opens) : AddMonoid.End Γ(G.left, U) :=
  Scheme.Hom.dualNumbersDeriv (dualNumbersι_comp_rightTranslation_left hx) U

theorem rightTranslationDeriv_mul {x y : Scheme.dualNumbersOver S ⟶ G}
    (hx : Scheme.dualNumbersιOver S ≫ x = 1) (hy : Scheme.dualNumbersιOver S ≫ y = 1)
    (hxy : Scheme.dualNumbersιOver S ≫ (x * y) = 1) (U : G.left.Opens) :
    rightTranslationDeriv hxy U = rightTranslationDeriv hx U + rightTranslationDeriv hy U := by
  have e := congrArg CommaMorphism.left (rightTranslation_mul x y)
  have hh₃ : G.left.dualNumbersι ≫ (rightTranslationLift x).left ≫ (rightTranslation y).left =
      𝟙 G.left := by
    exact (congrArg (fun φ : Scheme.overDualNumbers G ⟶ G ↦ G.left.dualNumbersι ≫ φ.left)
      (rightTranslation_mul x y)).symm.trans (dualNumbersι_comp_rightTranslation_left hxy)
  have hΛ : (rightTranslationLift x).left ≫ G.left.dualNumbersProj = (rightTranslation x).left :=
    congrArg CommaMorphism.left (rightTranslationLift_comp_overDualNumbersProj x)
  have hε := Scheme.appTop_inr_one_of_comp_dualNumbers (rightTranslationLift x).left G.hom
    (congrArg CommaMorphism.left (rightTranslationLift_comp_overDualNumbersMap x))
  rw [rightTranslationDeriv, Scheme.Hom.dualNumbersDeriv_congr _ hh₃ e,
    Scheme.Hom.dualNumbersDeriv_comp _ hε hΛ (dualNumbersι_comp_rightTranslation_left hx)
      (dualNumbersι_comp_rightTranslation_left hy)]
  rfl

theorem rightTranslation_one :
    rightTranslation (1 : Scheme.dualNumbersOver S ⟶ G) = Scheme.overDualNumbersProj G := by
  rw [rightTranslation, MonObj.comp_one, mul_one]

theorem rightTranslationDeriv_one (h1 : Scheme.dualNumbersιOver S ≫ (1 : _ ⟶ G) = 1)
    (U : G.left.Opens) : rightTranslationDeriv h1 U = 0 := by
  ext a
  have e : U ≤ (rightTranslation (1 : Scheme.dualNumbersOver S ⟶ G)).left ⁻¹ᵁ U :=
    Scheme.le_preimage_self_of_dualNumbersι_comp_eq_id
      (dualNumbersι_comp_rightTranslation_left h1) U
  rw [rightTranslationDeriv, Scheme.Hom.dualNumbersDeriv_apply _ U e]
  exact (congrArg TrivSqZeroExt.snd (Scheme.Hom.appLE_apply_eq_of_eq
    (congrArg CommaMorphism.left rightTranslation_one) U U e le_rfl a)).trans
    ((congrArg TrivSqZeroExt.snd (Scheme.dualNumbersProj_appLE_self (X := G.left) U le_rfl a)).trans
      (TrivSqZeroExt.snd_inl _ a))

theorem rightTranslationDeriv_apply {x : Scheme.dualNumbersOver S ⟶ G}
    (hx : Scheme.dualNumbersιOver S ≫ x = 1) (U : G.left.Opens)
    (e : U ≤ (rightTranslation x).left ⁻¹ᵁ U) (a : Γ(G.left, U)) :
    rightTranslationDeriv hx U a = ((rightTranslation x).left.appLE U U e a).snd :=
  rfl

theorem fst_rightTranslation_appLE {x : Scheme.dualNumbersOver S ⟶ G}
    (hx : Scheme.dualNumbersιOver S ≫ x = 1) (U : G.left.Opens)
    (e : U ≤ (rightTranslation x).left ⁻¹ᵁ U) (a : Γ(G.left, U)) :
    ((rightTranslation x).left.appLE U U e a).fst = a :=
  Scheme.fst_appLE_of_dualNumbersι_comp_eq_id (dualNumbersι_comp_rightTranslation_left hx) U e a

/-- `D_x` is a derivation. -/
theorem rightTranslationDeriv_mul_apply {x : Scheme.dualNumbersOver S ⟶ G}
    (hx : Scheme.dualNumbersιOver S ≫ x = 1) (U : G.left.Opens) (a b : Γ(G.left, U)) :
    rightTranslationDeriv hx U (a * b) =
      a * rightTranslationDeriv hx U b + b * rightTranslationDeriv hx U a := by
  have e := Scheme.le_preimage_self_of_dualNumbersι_comp_eq_id
    (dualNumbersι_comp_rightTranslation_left hx) U
  let φ : Γ(G.left, U) →+* DualNumber Γ(G.left, U) := ((rightTranslation x).left.appLE U U e).hom
  have h1 (c : Γ(G.left, U)) : (φ c).fst = c := fst_rightTranslation_appLE hx U e c
  rw [rightTranslationDeriv_apply hx U e, rightTranslationDeriv_apply hx U e,
    rightTranslationDeriv_apply hx U e]
  change (φ (a * b)).snd = a * (φ b).snd + b * (φ a).snd
  rw [map_mul, snd_mul, h1, h1, smul_eq_mul, op_smul_eq_mul, mul_comm (φ a).snd]

/-- `D_x` kills the functions pulled back from the base. -/
theorem rightTranslationDeriv_appLE {x : Scheme.dualNumbersOver S ⟶ G}
    (hx : Scheme.dualNumbersιOver S ≫ x = 1) (U : G.left.Opens) (W : S.Opens)
    (e : U ≤ G.hom ⁻¹ᵁ W) (r : Γ(S, W)) :
    rightTranslationDeriv hx U (G.hom.appLE W U e r) = 0 := by
  have e₁ := Scheme.le_preimage_self_of_dualNumbersι_comp_eq_id
    (dualNumbersι_comp_rightTranslation_left hx) U
  rw [rightTranslationDeriv_apply hx U e₁]
  have hw : (rightTranslation x).left ≫ G.hom = G.left.dualNumbersProj ≫ G.hom := Over.w _
  have := Scheme.Hom.appLE_apply_eq_of_eq hw W U (fun y hy ↦ e (e₁ hy)) (fun y hy ↦ e hy) r
  rw [Scheme.Hom.appLE_comp_apply (rightTranslation x).left G.hom W U U e e₁] at this
  exact (congrArg TrivSqZeroExt.snd (this.trans (Scheme.Hom.appLE_comp_apply
    G.left.dualNumbersProj G.hom W U U e le_rfl _ r))).trans ((congrArg TrivSqZeroExt.snd
    (Scheme.dualNumbersProj_appLE_self (X := G.left) U le_rfl _)).trans (snd_inl _ _))

/-- Multiplication by a function from the base commutes with `D_x`. -/
theorem rightTranslationDeriv_appLE_mul {x : Scheme.dualNumbersOver S ⟶ G}
    (hx : Scheme.dualNumbersιOver S ≫ x = 1) (U : G.left.Opens) (W : S.Opens)
    (e : U ≤ G.hom ⁻¹ᵁ W) (r : Γ(S, W)) (b : Γ(G.left, U)) :
    rightTranslationDeriv hx U (G.hom.appLE W U e r * b) =
      G.hom.appLE W U e r * rightTranslationDeriv hx U b := by
  rw [rightTranslationDeriv_mul_apply, rightTranslationDeriv_appLE, mul_zero, add_zero]

/-- The endomorphism `ε ↦ rε` of `G[ε]` over `S`. -/
noncomputable def overDualNumbersScale (r : Γ(S, ⊤)) :
    Scheme.overDualNumbers G ⟶ Scheme.overDualNumbers G :=
  Over.homMk (G.left.dualNumbersScale (G.hom.appTop r))
    (by simp [Scheme.overDualNumbers, Scheme.dualNumbersScale_comp_proj_assoc])

theorem rightTranslation_scale (r : Γ(S, ⊤)) (x : Scheme.dualNumbersOver S ⟶ G) :
    rightTranslation (Scheme.dualNumbersScaleOver S r ≫ x) =
      overDualNumbersScale r ≫ rightTranslation x := by
  have h1 : overDualNumbersScale r ≫ Scheme.overDualNumbersProj G =
      Scheme.overDualNumbersProj G := by
    ext1
    simp [overDualNumbersScale, Scheme.overDualNumbersProj]
  have h2 : overDualNumbersScale r ≫ Scheme.overDualNumbersMap G =
      Scheme.overDualNumbersMap G ≫ Scheme.dualNumbersScaleOver S r := by
    ext1
    simp [overDualNumbersScale, Scheme.overDualNumbersMap,
      Scheme.dualNumbersScale_comp_dualNumbers]
  rw [rightTranslation, rightTranslation, MonObj.comp_mul, h1, reassoc_of% h2]

/-- Rescaling a point by `r` multiplies its operator by `r`. -/
theorem rightTranslationDeriv_scale {x : Scheme.dualNumbersOver S ⟶ G}
    (hx : Scheme.dualNumbersιOver S ≫ x = 1) (r : Γ(S, ⊤))
    (hrx : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersScaleOver S r ≫ x = 1)
    (U : G.left.Opens) (b : Γ(G.left, U)) :
    rightTranslationDeriv hrx U b =
      G.left.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (G.hom.appTop r) *
        rightTranslationDeriv hx U b := by
  have e₁ := Scheme.le_preimage_self_of_dualNumbersι_comp_eq_id
    (dualNumbersι_comp_rightTranslation_left hx) U
  have e₂ := Scheme.le_preimage_self_of_dualNumbersι_comp_eq_id
    (dualNumbersι_comp_rightTranslation_left hrx) U
  have hL : (rightTranslation (Scheme.dualNumbersScaleOver S r ≫ x)).left =
      (overDualNumbersScale r).left ≫ (rightTranslation x).left := by
    rw [rightTranslation_scale]
    rfl
  rw [rightTranslationDeriv_apply hrx U e₂, rightTranslationDeriv_apply hx U e₁,
    Scheme.Hom.appLE_apply_eq_of_eq hL U U e₂ (fun y hy ↦ e₁ hy),
    Scheme.Hom.appLE_comp_apply (overDualNumbersScale r).left (rightTranslation x).left U U U e₁
      le_rfl]
  exact (congrArg TrivSqZeroExt.snd (Scheme.dualNumbersScale_appLE_self (X := G.left)
    (G.hom.appTop r) U le_rfl ((rightTranslation x).left.appLE U U e₁ b))).trans
    (DualNumber.snd_scale _ _)

/-- The thickening `e[ε] : S[ε] ⟶ G[ε]` of the identity section, over `S`. -/
noncomputable def unitDualNumbers : Scheme.dualNumbersOver S ⟶ Scheme.overDualNumbers G :=
  Over.homMk η[G].left.dualNumbers (by
    simp [Scheme.overDualNumbers, Scheme.Hom.dualNumbers_comp_proj_assoc, Over.w η[G]])

/-- A point `x` is recovered from its right translation `ρ_x` along the identity section. -/
theorem unitDualNumbers_comp_rightTranslation (x : Scheme.dualNumbersOver S ⟶ G) :
    unitDualNumbers ≫ rightTranslation x = x := by
  have h1 : unitDualNumbers ≫ Scheme.overDualNumbersProj G = 1 := by
    ext1
    simp [unitDualNumbers, Scheme.overDualNumbersProj, Hom.one_def, Over.toUnit_left]
  have h2 : unitDualNumbers ≫ Scheme.overDualNumbersMap G = 𝟙 _ := by
    ext1
    simp [unitDualNumbers, Scheme.overDualNumbersMap, ← Scheme.Hom.dualNumbers_comp,
      Over.w η[G], Scheme.Hom.dualNumbers_id]
  rw [rightTranslation, MonObj.comp_mul, h1, reassoc_of% h2, one_mul]

/-- The functions of a point `x` reducing to the identity: `x^♯(a) = e^♯(a) + ε e^♯(D_x a)`. -/
theorem snd_appLE_eq {x : Scheme.dualNumbersOver S ⟶ G} (hx : Scheme.dualNumbersιOver S ≫ x = 1)
    (U : G.left.Opens) (V : S.Opens) (e : V ≤ x.left ⁻¹ᵁ U) (e' : V ≤ η[G].left ⁻¹ᵁ U)
    (a : Γ(G.left, U)) :
    (x.left.appLE U V e a).snd = η[G].left.appLE U V e' (rightTranslationDeriv hx U a) := by
  have e₁ := Scheme.le_preimage_self_of_dualNumbersι_comp_eq_id
    (dualNumbersι_comp_rightTranslation_left hx) U
  have hL : unitDualNumbers.left ≫ (rightTranslation x).left = x.left :=
    congrArg CommaMorphism.left (unitDualNumbers_comp_rightTranslation x)
  have h := Scheme.Hom.appLE_apply_eq_of_eq hL U V (fun y hy ↦ e₁ (e' hy)) e a
  rw [Scheme.Hom.appLE_comp_apply unitDualNumbers.left (rightTranslation x).left U U V e₁ e'] at h
  rw [← h, rightTranslationDeriv_apply hx U e₁]
  exact (congrArg TrivSqZeroExt.snd (Scheme.Hom.dualNumbers_appLE η[G].left U V e'
    ((rightTranslation x).left.appLE U U e₁ a))).trans (DualNumber.snd_mapRingHom _ _)

theorem fst_appLE_eq {x : Scheme.dualNumbersOver S ⟶ G} (hx : Scheme.dualNumbersιOver S ≫ x = 1)
    (U : G.left.Opens) (V : S.Opens) (e : V ≤ x.left ⁻¹ᵁ U) (e' : V ≤ η[G].left ⁻¹ᵁ U)
    (a : Γ(G.left, U)) :
    (x.left.appLE U V e a).fst = η[G].left.appLE U V e' a := by
  have e₁ := Scheme.le_preimage_self_of_dualNumbersι_comp_eq_id
    (dualNumbersι_comp_rightTranslation_left hx) U
  have hL : unitDualNumbers.left ≫ (rightTranslation x).left = x.left :=
    congrArg CommaMorphism.left (unitDualNumbers_comp_rightTranslation x)
  have h := Scheme.Hom.appLE_apply_eq_of_eq hL U V (fun y hy ↦ e₁ (e' hy)) e a
  rw [Scheme.Hom.appLE_comp_apply unitDualNumbers.left (rightTranslation x).left U U V e₁ e'] at h
  rw [← h]
  exact (congrArg TrivSqZeroExt.fst (Scheme.Hom.dualNumbers_appLE η[G].left U V e'
    ((rightTranslation x).left.appLE U U e₁ a))).trans ((DualNumber.fst_mapRingHom _ _).trans
      (congrArg _ (fst_rightTranslation_appLE hx U e₁ a)))

end One

/-! ### Two parameters -/

section Two

/-- The right translation `ρ_z : G[ε][δ] ⟶ G`, `(g, t) ↦ g · z(t)`, by a point
`z : S[ε][δ] ⟶ G`. -/
noncomputable def rightTranslation₂ (z : Scheme.dualNumbers₂Over S ⟶ G) :
    Scheme.overDualNumbers₂ G ⟶ G :=
  Scheme.overDualNumbers₂Proj G * (Scheme.overDualNumbers₂Map G ≫ z)

/-- The automorphism `(g, t) ↦ (g · z(t), t)` of `G[ε][δ]` over `S[ε][δ]`. -/
noncomputable def rightTranslationLift₂ (z : Scheme.dualNumbers₂Over S ⟶ G) :
    Scheme.overDualNumbers₂ G ⟶ Scheme.overDualNumbers₂ G :=
  pullbackLift _ _ (Scheme.isPullback_overDualNumbers₂ G) (rightTranslation₂ z)

theorem rightTranslation₂_mul (z w : Scheme.dualNumbers₂Over S ⟶ G) :
    rightTranslation₂ (z * w) = rightTranslationLift₂ z ≫ rightTranslation₂ w :=
  (pullbackLift_comp_mul _ _ _ _ _).symm

theorem overDualNumbers₂ι_comp_rightTranslation₂ {z : Scheme.dualNumbers₂Over S ⟶ G}
    (hz : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫ z = 1) :
    Scheme.overDualNumbers₂ι G ≫ rightTranslation₂ z = 𝟙 G := by
  rw [rightTranslation₂, MonObj.comp_mul, ← Category.assoc,
    Scheme.overDualNumbers₂ι_comp_overDualNumbers₂Map, Category.assoc, Category.assoc, hz,
    MonObj.comp_one, Scheme.overDualNumbers₂ι_comp_overDualNumbers₂Proj, mul_one]

theorem dualNumbersι₂_comp_rightTranslation₂_left {z : Scheme.dualNumbers₂Over S ⟶ G}
    (hz : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫ z = 1) :
    G.left.dualNumbersι ≫ G.left.dualNumbers.dualNumbersι ≫ (rightTranslation₂ z).left =
      𝟙 G.left := by
  rw [← Category.assoc]
  exact congrArg CommaMorphism.left (overDualNumbers₂ι_comp_rightTranslation₂ hz)

/-- The operator `1 + ε D₁ + δ D₂ + εδ D₁₂` on the sections of `𝒪_G` of a point
`z : S[ε][δ] ⟶ G` reducing to the identity: `ρ_z^♯(a) = a + ε D₁(a) + δ D₂(a) + εδ D₁₂(a)`. -/
noncomputable def rightTranslationOp₂ {z : Scheme.dualNumbers₂Over S ⟶ G}
    (hz : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫ z = 1) (U : G.left.Opens) :
    DualNumber (DualNumber (AddMonoid.End Γ(G.left, U))) :=
  Scheme.Hom.dualNumbers₂Op (dualNumbersι₂_comp_rightTranslation₂_left hz) U

theorem rightTranslationOp₂_mul {z w : Scheme.dualNumbers₂Over S ⟶ G}
    (hz : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫ z = 1)
    (hw : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫ w = 1)
    (hzw : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫ (z * w) = 1)
    (U : G.left.Opens) :
    rightTranslationOp₂ hzw U = rightTranslationOp₂ hz U * rightTranslationOp₂ hw U := by
  have e := congrArg CommaMorphism.left (rightTranslation₂_mul z w)
  have hh₃ : G.left.dualNumbersι ≫ G.left.dualNumbers.dualNumbersι ≫
      (rightTranslationLift₂ z).left ≫ (rightTranslation₂ w).left = 𝟙 G.left :=
    (congrArg (fun φ : Scheme.overDualNumbers₂ G ⟶ G ↦
      G.left.dualNumbersι ≫ G.left.dualNumbers.dualNumbersι ≫ φ.left)
      (rightTranslation₂_mul z w)).symm.trans (dualNumbersι₂_comp_rightTranslation₂_left hzw)
  have hΛ : (rightTranslationLift₂ z).left ≫ G.left.dualNumbers.dualNumbersProj ≫
      G.left.dualNumbersProj = (rightTranslation₂ z).left :=
    congrArg CommaMorphism.left (pullbackLift_comp_snd _ _ _ _)
  have hF : (rightTranslationLift₂ z).left ≫ G.hom.dualNumbers.dualNumbers =
      G.hom.dualNumbers.dualNumbers :=
    congrArg CommaMorphism.left (pullbackLift_comp_fst _ _ _ _)
  rw [rightTranslationOp₂, Scheme.Hom.dualNumbers₂Op_congr _ hh₃ e,
    Scheme.Hom.dualNumbers₂Op_comp _ _
      (Scheme.appTop_inr_one_of_comp_dualNumbers_dualNumbers _ _ hF)
      (Scheme.appTop_inl_inr_one_of_comp_dualNumbers_dualNumbers _ _ hF) hΛ
      (dualNumbersι₂_comp_rightTranslation₂_left hz)
      (dualNumbersι₂_comp_rightTranslation₂_left hw)]
  rfl

theorem rightTranslation₂_projε (v : Scheme.dualNumbersOver S ⟶ G) :
    rightTranslation₂ (Scheme.dualNumbersProjεOver S ≫ v) =
      Scheme.overDualNumbers₂ProjFst G ≫ rightTranslation v := by
  rw [rightTranslation₂, rightTranslation, MonObj.comp_mul,
    Scheme.overDualNumbers₂ProjFst_comp_overDualNumbersProj,
    Scheme.overDualNumbers₂ProjFst_comp_overDualNumbersMap_assoc]

theorem rightTranslation₂_projδ (v : Scheme.dualNumbersOver S ⟶ G) :
    rightTranslation₂ (Scheme.dualNumbersProjδOver S ≫ v) =
      Scheme.overDualNumbers₂ProjSnd G ≫ rightTranslation v := by
  rw [rightTranslation₂, rightTranslation, MonObj.comp_mul,
    Scheme.overDualNumbers₂ProjSnd_comp_overDualNumbersProj,
    Scheme.overDualNumbers₂ProjSnd_comp_overDualNumbersMap_assoc]

theorem rightTranslation₂_mul_over (v : Scheme.dualNumbersOver S ⟶ G) :
    rightTranslation₂ (Scheme.dualNumbersMulOver S ≫ v) =
      Scheme.overDualNumbersMul G ≫ rightTranslation v := by
  rw [rightTranslation₂, rightTranslation, MonObj.comp_mul,
    Scheme.overDualNumbersMul_comp_overDualNumbersProj,
    Scheme.overDualNumbersMul_comp_overDualNumbersMap_assoc]

theorem rightTranslationOp₂_projε {v : Scheme.dualNumbersOver S ⟶ G}
    (hv : Scheme.dualNumbersιOver S ≫ v = 1)
    (hz : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫
      (Scheme.dualNumbersProjεOver S ≫ v) = 1) (U : G.left.Opens) :
    rightTranslationOp₂ hz U = inl (inl 1 + inr (rightTranslationDeriv hv U)) := by
  have e := Scheme.le_preimage_self_of_dualNumbersι₂_comp_eq_id
    (dualNumbersι₂_comp_rightTranslation₂_left hz) U
  have eρ := Scheme.le_preimage_self_of_dualNumbersι_comp_eq_id
    (dualNumbersι_comp_rightTranslation_left hv) U
  have key (a : Γ(G.left, U)) : ((rightTranslation₂ (Scheme.dualNumbersProjεOver S ≫ v)).left.appLE
      U U e a : DualNumber (DualNumber Γ(G.left, U))) =
        inl ((rightTranslation v).left.appLE U U eρ a) := by
    refine (Scheme.Hom.appLE_apply_eq_of_eq (congrArg CommaMorphism.left
      (rightTranslation₂_projε v)) U U e (fun x hx ↦ eρ hx) a).trans ?_
    refine (Scheme.Hom.appLE_comp_apply (Scheme.overDualNumbers₂ProjFst G).left
      (rightTranslation v).left U U U eρ le_rfl _ a).trans ?_
    exact Scheme.dualNumbersProj_appLE_self (X := G.left.dualNumbers) U le_rfl _
  refine TrivSqZeroExt.ext (TrivSqZeroExt.ext ?_ ?_) (TrivSqZeroExt.ext ?_ ?_)
  · simp [rightTranslationOp₂]
  · ext a
    rw [rightTranslationOp₂, Scheme.Hom.fst_snd_dualNumbers₂Op_apply _ U e]
    have := congrArg (fun y : DualNumber (DualNumber Γ(G.left, U)) ↦ y.fst.snd) (key a)
    simp only [fst_inl] at this
    exact this.trans (by simp; rfl)
  · ext a
    rw [rightTranslationOp₂, Scheme.Hom.snd_fst_dualNumbers₂Op_apply _ U e]
    have := congrArg (fun y : DualNumber (DualNumber Γ(G.left, U)) ↦ y.snd.fst) (key a)
    simp only [snd_inl, fst_zero] at this
    exact this.trans (by simp)
  · ext a
    rw [rightTranslationOp₂, Scheme.Hom.snd_snd_dualNumbers₂Op_apply _ U e]
    have := congrArg (fun y : DualNumber (DualNumber Γ(G.left, U)) ↦ y.snd.snd) (key a)
    simp only [snd_inl, snd_zero] at this
    exact this.trans (by simp)

theorem rightTranslationOp₂_projδ {v : Scheme.dualNumbersOver S ⟶ G}
    (hv : Scheme.dualNumbersιOver S ≫ v = 1)
    (hz : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫
      (Scheme.dualNumbersProjδOver S ≫ v) = 1) (U : G.left.Opens) :
    rightTranslationOp₂ hz U = inl (inl 1) + inr (inl (rightTranslationDeriv hv U)) := by
  have e := Scheme.le_preimage_self_of_dualNumbersι₂_comp_eq_id
    (dualNumbersι₂_comp_rightTranslation₂_left hz) U
  have eρ := Scheme.le_preimage_self_of_dualNumbersι_comp_eq_id
    (dualNumbersι_comp_rightTranslation_left hv) U
  let φ : Γ(G.left, U) →+* DualNumber Γ(G.left, U) := (G.left.dualNumbersProj.appLE U U le_rfl).hom
  have hp (b : Γ(G.left, U)) : φ b = inl b := Scheme.dualNumbersProj_appLE_self U le_rfl b
  have key (a : Γ(G.left, U)) : ((rightTranslation₂ (Scheme.dualNumbersProjδOver S ≫ v)).left.appLE
      U U e a : DualNumber (DualNumber Γ(G.left, U))) =
        DualNumber.mapRingHom φ ((rightTranslation v).left.appLE U U eρ a) := by
    refine (Scheme.Hom.appLE_apply_eq_of_eq (congrArg CommaMorphism.left
      (rightTranslation₂_projδ v)) U U e (fun x hx ↦ eρ hx) a).trans ?_
    refine (Scheme.Hom.appLE_comp_apply (Scheme.overDualNumbers₂ProjSnd G).left
      (rightTranslation v).left U U U eρ le_rfl _ a).trans ?_
    exact Scheme.Hom.dualNumbers_appLE G.left.dualNumbersProj U U le_rfl _
  refine TrivSqZeroExt.ext (TrivSqZeroExt.ext ?_ ?_) (TrivSqZeroExt.ext ?_ ?_)
  · simp [rightTranslationOp₂]
  · ext a
    rw [rightTranslationOp₂, Scheme.Hom.fst_snd_dualNumbers₂Op_apply _ U e]
    have := congrArg (fun y : DualNumber (DualNumber Γ(G.left, U)) ↦ y.fst.snd) (key a)
    simp only [DualNumber.fst_mapRingHom] at this
    rw [hp] at this
    exact this.trans (by simp)
  · ext a
    rw [rightTranslationOp₂, Scheme.Hom.snd_fst_dualNumbers₂Op_apply _ U e]
    have := congrArg (fun y : DualNumber (DualNumber Γ(G.left, U)) ↦ y.snd.fst) (key a)
    simp only [DualNumber.snd_mapRingHom] at this
    rw [hp] at this
    exact this.trans (by simp; rfl)
  · ext a
    rw [rightTranslationOp₂, Scheme.Hom.snd_snd_dualNumbers₂Op_apply _ U e]
    have := congrArg (fun y : DualNumber (DualNumber Γ(G.left, U)) ↦ y.snd.snd) (key a)
    simp only [DualNumber.snd_mapRingHom] at this
    rw [hp] at this
    exact this.trans (by simp)

theorem rightTranslationOp₂_mul_over {v : Scheme.dualNumbersOver S ⟶ G}
    (hv : Scheme.dualNumbersιOver S ≫ v = 1)
    (hz : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫
      (Scheme.dualNumbersMulOver S ≫ v) = 1) (U : G.left.Opens) :
    rightTranslationOp₂ hz U = inl (inl 1) + inr (inr (rightTranslationDeriv hv U)) := by
  have e := Scheme.le_preimage_self_of_dualNumbersι₂_comp_eq_id
    (dualNumbersι₂_comp_rightTranslation₂_left hz) U
  have eρ := Scheme.le_preimage_self_of_dualNumbersι_comp_eq_id
    (dualNumbersι_comp_rightTranslation_left hv) U
  have key (a : Γ(G.left, U)) : ((rightTranslation₂ (Scheme.dualNumbersMulOver S ≫ v)).left.appLE
      U U e a : DualNumber (DualNumber Γ(G.left, U))) =
        DualNumber.mulRingHom ((rightTranslation v).left.appLE U U eρ a :
          DualNumber Γ(G.left, U)) := by
    refine (Scheme.Hom.appLE_apply_eq_of_eq (congrArg CommaMorphism.left
      (rightTranslation₂_mul_over v)) U U e (fun x hx ↦ eρ hx) a).trans ?_
    refine (Scheme.Hom.appLE_comp_apply (Scheme.overDualNumbersMul G).left
      (rightTranslation v).left U U U eρ le_rfl _ a).trans ?_
    exact Scheme.dualNumbersMul_appLE_self (X := G.left) U le_rfl _
  refine TrivSqZeroExt.ext (TrivSqZeroExt.ext ?_ ?_) (TrivSqZeroExt.ext ?_ ?_)
  · simp [rightTranslationOp₂]
  · ext a
    rw [rightTranslationOp₂, Scheme.Hom.fst_snd_dualNumbers₂Op_apply _ U e]
    have := congrArg (fun y : DualNumber (DualNumber Γ(G.left, U)) ↦ y.fst.snd) (key a)
    simp only [DualNumber.fst_mulRingHom, snd_inl] at this
    exact this.trans (by simp)
  · ext a
    rw [rightTranslationOp₂, Scheme.Hom.snd_fst_dualNumbers₂Op_apply _ U e]
    have := congrArg (fun y : DualNumber (DualNumber Γ(G.left, U)) ↦ y.snd.fst) (key a)
    simp only [DualNumber.snd_mulRingHom, fst_inr] at this
    exact this.trans (by simp)
  · ext a
    rw [rightTranslationOp₂, Scheme.Hom.snd_snd_dualNumbers₂Op_apply _ U e]
    have := congrArg (fun y : DualNumber (DualNumber Γ(G.left, U)) ↦ y.snd.snd) (key a)
    simp only [DualNumber.snd_mulRingHom, snd_inr] at this
    exact this.trans (by simp; rfl)

theorem rightTranslationDeriv_inv {v : Scheme.dualNumbersOver S ⟶ G}
    (hv : Scheme.dualNumbersιOver S ≫ v = 1) (hv' : Scheme.dualNumbersιOver S ≫ v⁻¹ = 1)
    (U : G.left.Opens) : rightTranslationDeriv hv' U = -rightTranslationDeriv hv U := by
  have h1 : Scheme.dualNumbersιOver S ≫ (v * v⁻¹) = 1 := by rw [mul_inv_cancel, MonObj.comp_one]
  have := rightTranslationDeriv_mul hv hv' h1 U
  have h0 : rightTranslationDeriv h1 U = 0 := by
    rw [← rightTranslationDeriv_one (S := S) (G := G) (MonObj.comp_one _) U]
    exact Scheme.Hom.dualNumbersDeriv_congr _ _ (by rw [mul_inv_cancel]) U
  rw [h0] at this
  exact eq_neg_of_add_eq_zero_right this.symm

/-- The operator of the commutator `v_ε w_δ v_ε⁻¹ w_δ⁻¹`, the mixed term `εδ` of which is the
point `u`, is the commutator `D_v D_w - D_w D_v` of the operators of `v` and `w`: the bracket of
infinitesimal points is the bracket of left-invariant vector fields. -/
theorem rightTranslationDeriv_eq_of_mul_eq_commutator {v w u : Scheme.dualNumbersOver S ⟶ G}
    (hv : Scheme.dualNumbersιOver S ≫ v = 1) (hw : Scheme.dualNumbersιOver S ≫ w = 1)
    (hu : Scheme.dualNumbersιOver S ≫ u = 1)
    (h : Scheme.dualNumbersMulOver S ≫ u = (Scheme.dualNumbersProjεOver S ≫ v) *
      (Scheme.dualNumbersProjδOver S ≫ w) * (Scheme.dualNumbersProjεOver S ≫ v)⁻¹ *
        (Scheme.dualNumbersProjδOver S ≫ w)⁻¹) (U : G.left.Opens) :
    rightTranslationDeriv hu U = rightTranslationDeriv hv U * rightTranslationDeriv hw U -
      rightTranslationDeriv hw U * rightTranslationDeriv hv U := by
  have hιε : Scheme.dualNumbersιεOver S ≫ Scheme.dualNumbersProjεOver S = 𝟙 _ := by
    ext1
    simp [Scheme.dualNumbersιεOver, Scheme.dualNumbersProjεOver]
  have hιδ : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫
      Scheme.dualNumbersProjδOver S = Scheme.dualNumbersιOver S := by
    ext1
    simp [Scheme.dualNumbersιεOver, Scheme.dualNumbersProjδOver, Scheme.dualNumbersιOver]
  have hιμ : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫
      Scheme.dualNumbersMulOver S = Scheme.dualNumbersιOver S := by
    rw [Scheme.dualNumbersιεOver_comp_dualNumbersMulOver, ← Category.assoc]
    congr 1
  have hvε : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫
      (Scheme.dualNumbersProjεOver S ≫ v) = 1 := by
    rw [reassoc_of% hιε, hv]
  have hwδ : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫
      (Scheme.dualNumbersProjδOver S ≫ w) = 1 := by
    rw [reassoc_of% hιδ, hw]
  have hv' : Scheme.dualNumbersιOver S ≫ v⁻¹ = 1 := by rw [GrpObj.comp_inv, hv, inv_one]
  have hw' : Scheme.dualNumbersιOver S ≫ w⁻¹ = 1 := by rw [GrpObj.comp_inv, hw, inv_one]
  have hvε' : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫
      (Scheme.dualNumbersProjεOver S ≫ v⁻¹) = 1 := by
    rw [reassoc_of% hιε, hv']
  have hwδ' : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫
      (Scheme.dualNumbersProjδOver S ≫ w⁻¹) = 1 := by
    rw [reassoc_of% hιδ, hw']
  have hι (z : Scheme.dualNumbers₂Over S ⟶ G) (hz : Scheme.dualNumbersιOver S ≫
      Scheme.dualNumbersιεOver S ≫ z = 1) (z' : Scheme.dualNumbers₂Over S ⟶ G)
      (hz' : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫ z' = 1) :
      Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫ (z * z') = 1 := by
    rw [MonObj.comp_mul, MonObj.comp_mul, hz, hz', mul_one]
  have hμ : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫
      (Scheme.dualNumbersMulOver S ≫ u) = 1 := by
    rw [reassoc_of% hιμ, hu]
  have h₁ := hι _ hvε _ hwδ
  have h₂ := hι _ h₁ _ hvε'
  have h₃ := hι _ h₂ _ hwδ'
  have hT : rightTranslationOp₂ hμ U = rightTranslationOp₂ hvε U * rightTranslationOp₂ hwδ U *
      rightTranslationOp₂ hvε' U * rightTranslationOp₂ hwδ' U := by
    rw [← rightTranslationOp₂_mul hvε hwδ h₁, ← rightTranslationOp₂_mul h₁ hvε' h₂,
      ← rightTranslationOp₂_mul h₂ hwδ' h₃]
    exact Scheme.Hom.dualNumbers₂Op_congr _ _ (by
      rw [h, GrpObj.comp_inv, GrpObj.comp_inv]) U
  rw [rightTranslationOp₂_mul_over hu, rightTranslationOp₂_projε hv, rightTranslationOp₂_projδ hw,
    rightTranslationOp₂_projε hv', rightTranslationOp₂_projδ hw', rightTranslationDeriv_inv hv hv',
    rightTranslationDeriv_inv hw hw'] at hT
  have := congrArg (fun y : DualNumber (DualNumber (AddMonoid.End Γ(G.left, U))) ↦ y.snd.snd) hT
  simp at this
  rw [this]
  abel

end Two

end GrpObj

end AlgebraicGeometry
