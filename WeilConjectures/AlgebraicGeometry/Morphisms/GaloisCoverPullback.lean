/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Extensive
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

/-!
# Base change of Galois covers

The base change `P ×_Y X` of a finite étale Galois cover `P ⟶ Y` with group `G` along an
arbitrary morphism `f : X ⟶ Y` is a finite étale Galois cover of `X` with group `G`
(`AlgebraicGeometry.Scheme.GaloisCover.pullback`), the action being on the first factor.

Simple transitivity is the base change of the one for `P`: since finite coproducts of schemes
are universal, `∐_{g ∈ G} (P ×_Y X)` is the base change of `∐_{g ∈ G} P` along `f`, and
`(P ×_Y X) ×_X (P ×_Y X)` is the base change of `P ×_Y P` along `f`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.GaloisCover

variable {G : Type (u + 1)} [Group G] [Finite G] {X Y : Scheme.{u}}

/-- The square `(P ×_Y X) ×_X (P ×_Y X) ⟶ P ×_Y P` over `X ⟶ Y` is cartesian. -/
lemma isPullback_pullbackMap_pullback {P : Scheme.{u}} (π : P ⟶ Y) (f : X ⟶ Y) :
    IsPullback
      (pullback.map (pullback.snd π f) (pullback.snd π f) π π (pullback.fst π f)
        (pullback.fst π f) f pullback.condition.symm pullback.condition.symm)
      (pullback.fst (pullback.snd π f) (pullback.snd π f) ≫ pullback.snd π f)
      (pullback.fst π π ≫ π) f := by
  -- `(P ×_Y X) ×_X (P ×_Y X)` is the pullback of `P ×_Y X ⟶ Y` and `π`.
  have h₁ : IsPullback (pullback.fst (pullback.snd π f) (pullback.snd π f))
      (pullback.snd (pullback.snd π f) (pullback.snd π f) ≫ pullback.fst π f)
      (pullback.snd π f ≫ f) π :=
    IsPullback.paste_vert (IsPullback.of_hasPullback _ _)
      (IsPullback.of_hasPullback π f).flip
  -- hence the square over `P ×_Y P ⟶ P` is cartesian.
  have h₂ : IsPullback
      (pullback.map (pullback.snd π f) (pullback.snd π f) π π (pullback.fst π f)
        (pullback.fst π f) f pullback.condition.symm pullback.condition.symm)
      (pullback.fst (pullback.snd π f) (pullback.snd π f))
      (pullback.fst π π) (pullback.fst π f) := by
    refine IsPullback.of_right (h₁₂ := pullback.snd π π) (v₁₃ := π) ?_ (by simp)
      (IsPullback.of_hasPullback π π).flip
    convert h₁.flip using 1
    · simp
    · simp [pullback.condition]
  exact IsPullback.paste_vert h₂ (IsPullback.of_hasPullback π f)

/-- The action of `g` on the base change `P ×_Y X`: the base change of the action on `P`. -/
noncomputable abbrev pullbackSMul {P : Scheme.{u}} (π : P ⟶ Y) (f : X ⟶ Y) (a : P ⟶ P)
    (ha : a ≫ π = π) : Limits.pullback π f ⟶ Limits.pullback π f :=
  pullback.map π f π f a (𝟙 X) (𝟙 Y) (by simp [ha]) (by simp)

omit [Group G] in
/-- Simple transitivity of a group action over `Y` is stable under base change: if
`∐_{g ∈ G} P ⟶ P ×_Y P`, `(g • -, id)` on the `g`-th summand, is an isomorphism, then so is the
corresponding morphism for the base change `P ×_Y X`. -/
lemma isIso_sigmaDesc_pullback {P : Scheme.{u}} (π : P ⟶ Y) (f : X ⟶ Y) (smul : G → (P ⟶ P))
    (hsmul : ∀ g, smul g ≫ π = π)
    [IsIso (Sigma.desc fun g : G ↦ pullback.lift (f := π) (g := π) (smul g) (𝟙 P)
      (by simp [hsmul]))] :
    IsIso (Sigma.desc fun g : G ↦ pullback.lift (f := pullback.snd π f) (g := pullback.snd π f)
      (pullbackSMul π f (smul g) (hsmul g)) (𝟙 _) (by simp)) := by
  set D := Sigma.desc fun g : G ↦ pullback.lift (f := π) (g := π) (smul g) (𝟙 P)
    (by simp [hsmul])
  set D' := Sigma.desc fun g : G ↦ pullback.lift (f := pullback.snd π f) (g := pullback.snd π f)
    (pullbackSMul π f (smul g) (hsmul g)) (𝟙 _) (by simp)
  set m := pullback.map (pullback.snd π f) (pullback.snd π f) π π (pullback.fst π f)
    (pullback.fst π f) f pullback.condition.symm pullback.condition.symm
  set q := pullback.fst (pullback.snd π f) (pullback.snd π f) ≫ pullback.snd π f
  set k : ∐ (fun _ : G ↦ Limits.pullback π f) ⟶ ∐ (fun _ : G ↦ P) :=
    Sigma.desc fun g ↦ pullback.fst π f ≫ Sigma.ι (fun _ : G ↦ P) g
  set s : ∐ (fun _ : G ↦ Limits.pullback π f) ⟶ X := Sigma.desc fun _ ↦ pullback.snd π f
  set v : ∐ (fun _ : G ↦ P) ⟶ Y := Sigma.desc fun _ ↦ π
  have hA : IsPullback m q (pullback.fst π π ≫ π) f := isPullback_pullbackMap_pullback π f
  have hB : IsPullback k s v f := by
    have hau := FinitaryPreExtensive.isUniversal_finiteCoproducts
      (coproductIsCoproduct fun _ : G ↦ P)
    have hd := coproductIsCoproduct fun _ : G ↦ Limits.pullback π f
    have := hau.isPullback_of_isColimit_right (fun _ ↦ π) v f
      (fun _ ↦ pullback.fst π f) (fun _ ↦ pullback.snd π f)
      (fun _ ↦ IsPullback.of_hasPullback π f) hd (fun g ↦ Sigma.ι_desc _ g)
    have e₁ : k = Cofan.IsColimit.desc hd
        (fun g ↦ pullback.fst π f ≫ (Cofan.mk _ (Sigma.ι fun _ : G ↦ P)).inj g) :=
      Sigma.hom_ext _ _ fun g ↦ (Sigma.ι_desc _ g).trans (Cofan.IsColimit.fac hd
        (fun g ↦ pullback.fst π f ≫ (Cofan.mk _ (Sigma.ι fun _ : G ↦ P)).inj g) g).symm
    have e₂ : s = Cofan.IsColimit.desc hd (fun _ ↦ pullback.snd π f) :=
      Sigma.hom_ext _ _ fun g ↦ (Sigma.ι_desc _ g).trans
        (Cofan.IsColimit.fac hd (fun _ ↦ pullback.snd π f) g).symm
    rw [e₁, e₂]
    exact this
  have hD : D ≫ pullback.fst π π ≫ π = v := Sigma.hom_ext _ _ fun g ↦ by simp [D, v, hsmul]
  have hm : D' ≫ m = k ≫ D := Sigma.hom_ext _ _ fun g ↦ by
    apply pullback.hom_ext
    · simp [D', D, m, k]
    · simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app,
        Category.assoc, limit.lift_π, PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_right,
        colimit.ι_desc, Category.comp_id, D', m, k, D]
      exact Category.id_comp _
  have hq : D' ≫ q = s := Sigma.hom_ext _ _ fun g ↦ by simp [D', q, s]
  let E : Limits.pullback (pullback.snd π f) (pullback.snd π f) ⟶
      ∐ (fun _ : G ↦ Limits.pullback π f) :=
    hB.lift (m ≫ inv D) q (by rw [Category.assoc, ← hD, IsIso.inv_hom_id_assoc, hA.w])
  refine ⟨E, hB.hom_ext ?_ ?_, hA.hom_ext ?_ ?_⟩
  · simp [E, reassoc_of% hm]
  · rw [Category.assoc, hB.lift_snd, hq, Category.id_comp]
  · simp [E, hm]
  · simp [E, hq]

/-- The base change of a finite étale Galois cover with group `G` along `f : X ⟶ Y`: the
`X`-scheme `P ×_Y X`, with `G` acting on the first factor. -/
@[simps P π]
noncomputable def pullback (c : GaloisCover G Y) (f : X ⟶ Y) : GaloisCover G X where
  P := Limits.pullback c.π f
  π := Limits.pullback.snd c.π f
  isFinite := by have := c.isFinite; infer_instance
  etale := by have := c.etale; infer_instance
  surjective := by have := c.surjective; infer_instance
  smul g := pullbackSMul c.π f (c.smul g) (c.smul_π g)
  smul_π g := by simp
  one_smul := by apply pullback.hom_ext <;> simp [c.one_smul]
  mul_smul g h := by apply pullback.hom_ext <;> simp [c.mul_smul]
  isIso_sigmaDesc := by
    have := c.isIso_sigmaDesc
    exact isIso_sigmaDesc_pullback c.π f c.smul c.smul_π

end AlgebraicGeometry.Scheme.GaloisCover
