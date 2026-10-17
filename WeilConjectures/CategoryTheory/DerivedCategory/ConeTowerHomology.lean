/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ProZeroHomology
public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.ConeTower
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Homology of towers of mapping cones of modules

Let `u : X ⟶ Y` be a morphism of towers of cochain complexes of `R`-modules and let
`Zₘ = cone(uₘ)` be the tower of mapping cones (`CochainComplex.mappingConeFunctor`). The long
exact homology sequences of the distinguished triangles `Xₘ ⟶ Yₘ ⟶ Zₘ ⟶ Xₘ[1]` in the derived
category give a criterion for the homology towers `Hᵖ(Z)` to be pro-zero
(`DerivedCategory.exists_homologyFunctor_map_mappingConeFunctor_eq_zero`): it suffices that

* the transition maps of `Hᵖ⁺¹(X)` eventually kill the kernel of `Hᵖ⁺¹(u)`, and
* the transition maps of `Hᵖ(Y)` eventually land in the image of `Hᵖ(u)`.

We also record that `Hᵖ(Z)` vanishes when `Hᵖ(Y)` and `Hᵖ⁺¹(X)` do
(`DerivedCategory.isZero_homologyFunctor_obj_mappingCone`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite Pretriangulated CochainComplex

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The connecting morphisms of the homology sequences are natural with respect to morphisms of
triangles. -/
lemma HomologySequence.δ_naturality {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {T T' : Triangle (DerivedCategory C)} (φ : T ⟶ T') (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor C n₀).map φ.hom₃ ≫ HomologySequence.δ T' n₀ n₁ h =
      HomologySequence.δ T n₀ n₁ h ≫ (homologyFunctor C n₁).map φ.hom₁ :=
  (homologyFunctor C 0).homologySequenceδ_naturality T T' φ n₀ n₁ h

variable {X Y : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ} (u : X ⟶ Y)

/-- The distinguished triangle `Xₘ ⟶ Yₘ ⟶ cone(uₘ) ⟶ Xₘ[1]` in the derived category. -/
noncomputable abbrev coneTriangle (m : ℕᵒᵖ) : Triangle (DerivedCategory (ModuleCat.{u} R)) :=
  Q.mapTriangle.obj (mappingCone.triangle (u.app m))

/-- The transition morphisms of the triangles `coneTriangle u m`. -/
noncomputable abbrev coneTriangleMap {m m' : ℕᵒᵖ} (h : m ⟶ m') :
    coneTriangle u m ⟶ coneTriangle u m' :=
  Q.mapTriangle.map (mappingCone.triangleMap (u.app m) (u.app m') (X.map h) (Y.map h)
    (u.naturality h).symm)

lemma coneTriangle_distinguished (m : ℕᵒᵖ) : coneTriangle u m ∈ distTriang _ :=
  mappingCone_triangle_distinguished _

/-- The `p`-th homology of `cone(uₘ)` vanishes when those of `Hᵖ(Yₘ)` and `Hᵖ⁺¹(Xₘ)` do. -/
lemma isZero_homologyFunctor_obj_mappingCone (m : ℕᵒᵖ) (p q : ℤ) (hpq : p + 1 = q)
    (hY : IsZero ((homologyFunctor _ p).obj (Q.obj (Y.obj m))))
    (hX : IsZero ((homologyFunctor _ q).obj (Q.obj (X.obj m)))) :
    IsZero ((homologyFunctor _ p).obj (Q.obj (mappingCone (u.app m)))) :=
  ((HomologySequence.exact₃ _ (coneTriangle_distinguished u m) p q hpq).isZero_X₂_iff).2
    ⟨hY.eq_of_src _ _, hX.eq_of_tgt _ _⟩

/-- **Pro-vanishing of the homology of a tower of cones.** If the transition maps of `Hᵖ⁺¹(X)`
eventually kill the kernel of `Hᵖ⁺¹(u)` and those of `Hᵖ(Y)` eventually land in the image of
`Hᵖ(u)`, then the homology tower `Hᵖ(cone u)` is pro-zero. -/
theorem exists_homologyFunctor_map_mappingConeFunctor_eq_zero (p q : ℤ) (hpq : p + 1 = q)
    (hA : ∀ a : ℕ, ∃ (b : ℕ) (hab : a ≤ b),
      ∀ x : (homologyFunctor _ q).obj (Q.obj (X.obj (op b))),
        (homologyFunctor _ q).map (Q.map (u.app (op b))) x = 0 →
          (homologyFunctor _ q).map (Q.map (X.map (homOfLE hab).op)) x = 0)
    (hB : ∀ a : ℕ, ∃ (b : ℕ) (hab : a ≤ b),
      ∀ y : (homologyFunctor _ p).obj (Q.obj (Y.obj (op b))),
        ∃ x : (homologyFunctor _ p).obj (Q.obj (X.obj (op a))),
          (homologyFunctor _ p).map (Q.map (u.app (op a))) x =
            (homologyFunctor _ p).map (Q.map (Y.map (homOfLE hab).op)) y)
    (a : ℕ) : ∃ (c : ℕ) (hac : a ≤ c),
      (homologyFunctor _ p).map ((mappingConeFunctor u ⋙ Q).map (homOfLE hac).op) = 0 := by
  obtain ⟨b, hab, hb⟩ := hB a
  obtain ⟨c, hbc, hc⟩ := hA b
  refine ⟨c, hab.trans hbc, ?_⟩
  ext z
  have hTc := coneTriangle_distinguished u (op c)
  have hTb := coneTriangle_distinguished u (op b)
  -- `δ z` is killed by `Hᵖ⁺¹(u_c)`, hence by the transition to level `b`
  have h₁ : (homologyFunctor _ q).map (Q.map (u.app (op c)))
      (HomologySequence.δ _ p q hpq z) = 0 := by
    have := HomologySequence.δ_comp _ hTc p q hpq
    exact congr($this z)
  have h₂ := hc _ h₁
  -- so the transition of `z` to level `b` comes from `Hᵖ(Y_b)`
  have h₃ : HomologySequence.δ (coneTriangle u (op b)) p q hpq
      ((homologyFunctor _ p).map ((coneTriangleMap u (homOfLE hbc).op).hom₃) z) = 0 := by
    have := HomologySequence.δ_naturality (coneTriangleMap u (homOfLE hbc).op) p q hpq
    have := congr($this z)
    simp only [ModuleCat.comp_apply] at this
    rw [this]
    exact h₂
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (HomologySequence.exact₃ _ hTb p q hpq) _ h₃
  obtain ⟨x, hx⟩ := hb y
  have hcomp : (homOfLE (hab.trans hbc)).op = (homOfLE hbc).op ≫ (homOfLE hab).op := rfl
  have e₁ : (homologyFunctor _ p).map ((mappingConeFunctor u ⋙ Q).map (homOfLE (hab.trans hbc)).op)
      z = (homologyFunctor _ p).map ((coneTriangleMap u (homOfLE hab).op).hom₃)
        ((homologyFunctor _ p).map ((coneTriangleMap u (homOfLE hbc).op).hom₃) z) := by
    rw [hcomp, Functor.map_comp, Functor.map_comp, ModuleCat.comp_apply]
    rfl
  rw [e₁]
  dsimp only at hy
  rw [← hy]
  have e₂ : (homologyFunctor _ p).map (coneTriangleMap u (homOfLE hab).op).hom₃
      ((homologyFunctor _ p).map (coneTriangle u (op b)).mor₂ y) =
      (homologyFunctor _ p).map (coneTriangle u (op a)).mor₂
        ((homologyFunctor _ p).map (coneTriangleMap u (homOfLE hab).op).hom₂ y) := by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← (coneTriangleMap u (homOfLE hab).op).comm₂,
      Functor.map_comp, ModuleCat.comp_apply]
  rw [e₂]
  change (homologyFunctor _ p).map (coneTriangle u (op a)).mor₂
    ((homologyFunctor _ p).map (Q.map (Y.map (homOfLE hab).op)) y) = _
  rw [← hx, ← ModuleCat.comp_apply, ← Functor.map_comp]
  change (homologyFunctor _ p).map ((coneTriangle u (op a)).mor₁ ≫
    (coneTriangle u (op a)).mor₂) x = _
  rw [comp_distTriang_mor_zero₁₂ _ (coneTriangle_distinguished u (op a)), Functor.map_zero]
  simp

end DerivedCategory
