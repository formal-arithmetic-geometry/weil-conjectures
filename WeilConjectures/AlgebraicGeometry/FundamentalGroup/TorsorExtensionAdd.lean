/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorExtensionMap

/-!
# Additivity of the cup product with the class of a `ℤ/m`-torsor

Let `T` be a `ℤ/m × ℤ/m`-torsor over `Y`, with total space `π : Q ⟶ Y`, and let `D₁`, `D₂` be the
differences `τ - 𝟙` of the translations by the two generators on `π_* μ_m`. With `N` the
invariants (`D₁ = D₂ = 0`) and `V` the sections with `D₁ v, D₂ v ∈ N`, there is a short exact
sequence `0 ⟶ N ⟶ V ⟶ N ⊞ N ⟶ 0` (`AlgebraicGeometry.Scheme.EtaleTorsor.pairSeq_shortExact`),
and `N ≅ μ_m` (`AlgebraicGeometry.Scheme.EtaleTorsor.isIso_pairUnit`). Locally `V` consists of
the functions `(a, b) ↦ x + a c₁ + b c₂`.

If `t` is a `ℤ/m`-torsor with a morphism `h : Q ⟶ P` over `Y` under which the generators act as
`c₁` and `c₂`, pulling back functions along `h` maps the extension
`0 ⟶ μ_m ⟶ K₂ ⟶ μ_m ⟶ 0` of `t` to this sequence, by `(c₁, c₂)` on the quotient. Applied to the
three torsors `t₁`, `t₂`, `t₃` obtained from `T` along the projections and the sum, this gives
`t₃.cupMu = t₁.cupMu + t₂.cupMu` (`AlgebraicGeometry.Scheme.EtaleTorsor.cupMu_eq_add`): the
cup product is additive in the class of the torsor.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleTorsor

section Algebra

variable {m : ℕ} [NeZero m] {A : Type*} [AddCommGroup A]

/-- A function on `ℤ/m × ℤ/m` invariant under the shifts by `-e₁` and `-e₂` is constant. -/
lemma apply_eq_apply_zero_of_forall_sub_pair
    {F : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m) → A}
    (h₁ : ∀ a, F (a - (1, 0)) = F a) (h₂ : ∀ a, F (a - (0, 1)) = F a)
    (a : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) : F a = F 0 := by
  have e₁ (x y : ULift.{u + 1} (ZMod m)) : F (x, y) = F (0, y) :=
    apply_eq_apply_zero_of_forall_sub_one (F := fun x ↦ F (x, y)) (fun x ↦ by
      simpa using h₁ (x, y)) x
  have e₂ (y : ULift.{u + 1} (ZMod m)) : F (0, y) = F (0, 0) :=
    apply_eq_apply_zero_of_forall_sub_one (F := fun y ↦ F (0, y)) (fun y ↦ by
      simpa using h₂ (0, y)) y
  obtain ⟨x, y⟩ := a
  exact (e₁ x y).trans (e₂ y)


lemma zmodChar_neg_sub_one (c : A) (hc : m • c = 0) (x : ZMod m) :
    zmodChar c hc (-(x - 1)) - zmodChar c hc (-x) = c := by
  rw [← map_sub]
  convert zmodChar_one c hc using 2
  ring
end Algebra

variable {Y : Scheme.{u}} {m : ℕ} [NeZero m]
  (T : EtaleTorsor (ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) Y)

/-! ### The sequence `0 ⟶ N ⟶ V ⟶ N ⊞ N ⟶ 0` -/

/-- `τ_b - 𝟙` on `π_* 𝔾ₘ`. -/
noncomputable def pairDiff (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) :
    T.pushforwardGm ⟶ T.pushforwardGm :=
  T.pushforwardGmTranslate b - 𝟙 _

/-- The sheaf `π_* μ_m`. -/
noncomputable abbrev pairMu : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel (m • 𝟙 T.pushforwardGm)

/-- `τ_b - 𝟙` on `π_* μ_m`. -/
noncomputable def pairMuDiff (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) :
    T.pairMu ⟶ T.pairMu :=
  kernel.lift _ (kernel.ι _ ≫ T.pairDiff b) (by
    rw [Category.assoc, comp_nsmul_id, ← Category.assoc, kernel.condition, zero_comp])

@[reassoc (attr := simp)]
lemma pairMuDiff_ι (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) :
    T.pairMuDiff b ≫ kernel.ι _ = kernel.ι _ ≫ T.pairDiff b :=
  kernel.lift_ι _ _ _

/-- `(D₁, D₂) : π_* μ_m ⟶ π_* μ_m ⊞ π_* μ_m`. -/
noncomputable def pairPhi : T.pairMu ⟶ T.pairMu ⊞ T.pairMu :=
  biprod.lift (T.pairMuDiff (1, 0)) (T.pairMuDiff (0, 1))

/-- The invariants `N = ker (D₁, D₂)`. -/
noncomputable abbrev pairN : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel T.pairPhi

/-- The sections `v` with `D₁ v, D₂ v ∈ N`. -/
noncomputable abbrev pairV : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi)

lemma ιV_pairMuDiff_pairPhi (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m))
    (hb : b = (1, 0) ∨ b = (0, 1)) :
    kernel.ι (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi) ≫ T.pairMuDiff b ≫ T.pairPhi = 0 := by
  rcases hb with rfl | rfl
  · calc _ = kernel.ι (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi) ≫
          (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi) ≫ biprod.fst := by
          rw [Category.assoc, biprod.map_fst, pairPhi, biprod.lift_fst_assoc]
      _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]
  · calc _ = kernel.ι (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi) ≫
          (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi) ≫ biprod.snd := by
          rw [Category.assoc, biprod.map_snd, pairPhi, biprod.lift_snd_assoc]
      _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]

lemma ιN_pairMuDiff (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m))
    (hb : b = (1, 0) ∨ b = (0, 1)) : kernel.ι T.pairPhi ≫ T.pairMuDiff b = 0 := by
  rcases hb with rfl | rfl
  · calc _ = kernel.ι T.pairPhi ≫ T.pairPhi ≫ biprod.fst := by rw [pairPhi, biprod.lift_fst]
      _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]
  · calc _ = kernel.ι T.pairPhi ≫ T.pairPhi ≫ biprod.snd := by rw [pairPhi, biprod.lift_snd]
      _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]

/-- The map `V ⟶ N`, `v ↦ D_b v`. -/
noncomputable def pairQ (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m))
    (hb : b = (1, 0) ∨ b = (0, 1)) : T.pairV ⟶ T.pairN :=
  kernel.lift _ (kernel.ι _ ≫ T.pairMuDiff b) (by
    rw [Category.assoc, T.ιV_pairMuDiff_pairPhi b hb])

@[reassoc (attr := simp)]
lemma pairQ_ι (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m))
    (hb : b = (1, 0) ∨ b = (0, 1)) :
    T.pairQ b hb ≫ kernel.ι _ = kernel.ι _ ≫ T.pairMuDiff b :=
  kernel.lift_ι _ _ _

/-- The inclusion `N ⟶ V`. -/
noncomputable def pairI : T.pairN ⟶ T.pairV :=
  kernel.lift _ (kernel.ι _) (by rw [← Category.assoc, kernel.condition, zero_comp])

@[reassoc (attr := simp)]
lemma pairI_ι : T.pairI ≫ kernel.ι _ = kernel.ι T.pairPhi :=
  kernel.lift_ι _ _ _

/-- The short complex `N ⟶ V ⟶ N ⊞ N`. -/
noncomputable def pairSeq : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk T.pairI (biprod.lift (T.pairQ (1, 0) (.inl rfl)) (T.pairQ (0, 1) (.inr rfl)))
    (by
      apply biprod.hom_ext
      · rw [← cancel_mono (kernel.ι T.pairPhi)]
        simp only [Category.assoc, biprod.lift_fst_assoc, pairQ_ι, pairI_ι_assoc, zero_comp]
        exact T.ιN_pairMuDiff _ (.inl rfl)
      · rw [← cancel_mono (kernel.ι T.pairPhi)]
        simp only [Category.assoc, biprod.lift_snd_assoc, pairQ_ι, pairI_ι_assoc, zero_comp]
        exact T.ιN_pairMuDiff _ (.inr rfl))

lemma pairSeq_g_comp :
    T.pairSeq.g ≫ biprod.map (kernel.ι T.pairPhi) (kernel.ι T.pairPhi) =
      kernel.ι _ ≫ T.pairPhi := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, pairPhi, biprod.lift_fst, pairSeq]
    exact (biprod.lift_fst_assoc _ _ _).trans (T.pairQ_ι (1, 0) (.inl rfl))
  · simp only [Category.assoc, biprod.map_snd, pairPhi, biprod.lift_snd, pairSeq]
    exact (biprod.lift_snd_assoc _ _ _).trans (T.pairQ_ι (0, 1) (.inr rfl))

instance : Mono T.pairSeq.f :=
  mono_of_mono_fac (T.pairI_ι)

lemma pairSeq_exact : T.pairSeq.Exact := by
  refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι _ _
    (fun w hw ↦ kernel.lift T.pairPhi (w ≫ kernel.ι _) (by
      rw [Category.assoc, ← T.pairSeq_g_comp, ← Category.assoc, hw, zero_comp]))
    (fun w hw ↦ ?_) (fun w hw g hg ↦ ?_))
  · rw [← cancel_mono (kernel.ι (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi))]
    simp [pairSeq]
  · rw [← cancel_mono (kernel.ι T.pairPhi)]
    simp only [kernel.lift_ι, ← hg]
    simp [pairSeq]

/-! ### Local computations -/

lemma pairDiff_app (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) (U : Y.Etaleᵒᵖ)
    (x : T.pushforwardGm.obj.obj U) :
    (T.pairDiff b).hom.app U x = (T.pushforwardGmTranslate b).hom.app U x - x :=
  map_sub (homAppAddHom U x) _ _

/-- Sections of a biproduct of abelian sheaves are determined by their components. -/
lemma biprod_app_ext {X : Scheme.{u}} {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {U : X.Etaleᵒᵖ} (x y : (F ⊞ G).obj.obj U)
    (h₁ : (biprod.fst : F ⊞ G ⟶ F).hom.app U x = (biprod.fst : F ⊞ G ⟶ F).hom.app U y)
    (h₂ : (biprod.snd : F ⊞ G ⟶ G).hom.app U x = (biprod.snd : F ⊞ G ⟶ G).hom.app U y) :
    x = y := by
  have e (z : (F ⊞ G).obj.obj U) : z = (biprod.inl : F ⟶ F ⊞ G).hom.app U
      ((biprod.fst : F ⊞ G ⟶ F).hom.app U z) +
        (biprod.inr : G ⟶ F ⊞ G).hom.app U ((biprod.snd : F ⊞ G ⟶ G).hom.app U z) := by
    have := congrArg (fun φ : F ⊞ G ⟶ F ⊞ G ↦ homAppAddHom U z φ) (biprod.total (X := F) (Y := G))
    exact (this.symm.trans (map_add (homAppAddHom U z) _ _))
  rw [e x, e y, h₁, h₂]

section LocalTrivialization

variable {U : Y.Etale} (σ : U.left ⟶ T.P) (hσ : σ ≫ T.π = U.hom)

lemma localUnits_pairDiff (a b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m))
    (x : T.pushforwardGm.obj.obj (op U)) :
    T.localUnits σ hσ a ((T.pairDiff b).hom.app (op U) x) =
      T.localUnits σ hσ (a - b) x - T.localUnits σ hσ a x := by
  rw [pairDiff_app, map_sub, localUnits_translate]

include σ hσ in
/-- Over an étale `U` with a section of the torsor, an invariant section of `π_* 𝔾ₘ` comes from
the base. -/
lemma exists_of_pairDiff_eq_zero (x : T.pushforwardGm.obj.obj (op U)) (hx : m • x = 0)
    (h₁ : (T.pairDiff (1, 0)).hom.app (op U) x = 0)
    (h₂ : (T.pairDiff (0, 1)).hom.app (op U) x = 0) :
    ∃ c : Y.gmSheaf.obj.obj (op U), m • c = 0 ∧ T.pushforwardGmUnit.hom.app (op U) c = x := by
  set F := fun a ↦ T.localUnits σ hσ a x
  have hF (a) : F a = F 0 := by
    refine apply_eq_apply_zero_of_forall_sub_pair (fun a ↦ ?_) (fun a ↦ ?_) a
    · have := T.localUnits_pairDiff σ hσ a (1, 0) x
      rw [h₁, map_zero] at this
      exact sub_eq_zero.1 this.symm
    · have := T.localUnits_pairDiff σ hσ a (0, 1) x
      rw [h₂, map_zero] at this
      exact sub_eq_zero.1 this.symm
  refine ⟨ULift.up (F 0), ULift.ext _ _ ?_, T.localUnits_injective σ hσ fun a ↦ ?_⟩
  · change m • T.localUnits σ hσ 0 x = 0
    rw [← map_nsmul, hx, map_zero]
  · rw [localUnits_unit]
    exact (hF a).symm

include σ hσ in
/-- Over an étale `U` with a section of the torsor, every pair of `m`-torsion units of the base is
`(D₁ y, D₂ y)` for an `m`-torsion section `y` of `π_* 𝔾ₘ`. -/
lemma exists_pairDiff_eq (c₁ c₂ : Y.gmSheaf.obj.obj (op U)) (hc₁ : m • c₁.down = 0)
    (hc₂ : m • c₂.down = 0) :
    ∃ y : T.pushforwardGm.obj.obj (op U), m • y = 0 ∧
      (T.pairDiff (1, 0)).hom.app (op U) y = T.pushforwardGmUnit.hom.app (op U) c₁ ∧
      (T.pairDiff (0, 1)).hom.app (op U) y = T.pushforwardGmUnit.hom.app (op U) c₂ := by
  obtain ⟨y, hy⟩ := T.exists_localUnits σ hσ
    (fun a ↦ zmodChar c₁.down hc₁ (-a.1.down) + zmodChar c₂.down hc₂ (-a.2.down))
  refine ⟨y, T.localUnits_injective σ hσ fun a ↦ ?_, T.localUnits_injective σ hσ fun a ↦ ?_,
    T.localUnits_injective σ hσ fun a ↦ ?_⟩
  · rw [map_nsmul, hy, map_zero, smul_add]
    exact (congrArg₂ (· + ·) (nsmul_zmodChar _ _ _) (nsmul_zmodChar _ _ _)).trans (add_zero 0)
  · rw [localUnits_pairDiff, hy, hy, localUnits_unit]
    have h1 : (a - (1, 0)).1.down = a.1.down - 1 := rfl
    have h2 : (a - (1, 0)).2 = a.2 := by simp
    rw [h1, h2, add_sub_add_right_eq_sub]
    exact zmodChar_neg_sub_one _ _ _
  · rw [localUnits_pairDiff, hy, hy, localUnits_unit]
    have h1 : (a - (0, 1)).2.down = a.2.down - 1 := rfl
    have h2 : (a - (0, 1)).1 = a.1 := by simp
    rw [h1, h2, add_sub_add_left_eq_sub]
    exact zmodChar_neg_sub_one _ _ _
end LocalTrivialization

end AlgebraicGeometry.Scheme.EtaleTorsor
