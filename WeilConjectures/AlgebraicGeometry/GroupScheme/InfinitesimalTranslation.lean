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

theorem overDualNumbers₂ProjFst_comp_overDualNumbersMap :
    overDualNumbers₂ProjFst Y ≫ overDualNumbersMap Y =
      overDualNumbers₂Map Y ≫ dualNumbersProjεOver S := by
  ext1
  simp [overDualNumbers₂ProjFst, overDualNumbersMap, overDualNumbers₂Map, dualNumbersProjεOver]

theorem overDualNumbers₂ProjSnd_comp_overDualNumbersProj :
    overDualNumbers₂ProjSnd Y ≫ overDualNumbersProj Y = overDualNumbers₂Proj Y := by
  ext1
  simp [overDualNumbers₂ProjSnd, overDualNumbersProj, overDualNumbers₂Proj]

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

end One

end GrpObj

end AlgebraicGeometry
