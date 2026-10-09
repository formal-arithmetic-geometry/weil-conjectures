/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# Torsors with the same transition functions are isomorphic

Let `P` and `P'` be torsors under a sheaf of abelian groups `G` on a site with a terminal object.
If both have sections `t V`, `t' V` over the objects `V` of a covering, whose differences on
common refinements agree, then `P` and `P'` are isomorphic: a section `s` of `P` is sent to the
section of `P'` which is `(s - t V) + t' V` over each `V`.

## Main statements

- `CategoryTheory.Sheaf.Torsor.equiv_of_sub_eq`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Sheaf.Torsor

open Opposite Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Sheaf J AddCommGrpCat.{w}}

lemma vadd_sub_eq_vadd_sub (P P' : Torsor G) {U : Cᵒᵖ} (a b y : P.sheaf.obj.obj U)
    (a' b' : P'.sheaf.obj.obj U) (h : P.sub a b = P'.sub a' b') :
    P'.vadd U (P.sub a y) a' = P'.vadd U (P.sub b y) b' := by
  rw [← P'.sub_vadd a' b', ← P'.add_vadd, ← h, ← P.sub_sub_sub a b y, sub_add_cancel]

variable {T : C} (hT : IsTerminal T)

include hT in
/-- **Torsors with the same transition functions are isomorphic.** Let `R` be a covering sieve
of the terminal object, and `t V`, `t' V` sections of `P` and `P'` over the objects `V` of `R`.
If `t V₁ - t V₂ = t' V₁ - t' V₂` after restriction to any `Z` mapping to `V₁` and `V₂`, then `P`
and `P'` are isomorphic. -/
theorem equiv_of_sub_eq (P P' : Torsor G) (R : Sieve T) (hR : R ∈ J T)
    (t : ∀ V : C, R (hT.from V) → P.sheaf.obj.obj (op V))
    (t' : ∀ V : C, R (hT.from V) → P'.sheaf.obj.obj (op V))
    (h : ∀ ⦃V₁ V₂ Z : C⦄ (h₁ : R (hT.from V₁)) (h₂ : R (hT.from V₂)) (a : Z ⟶ V₁) (b : Z ⟶ V₂),
      P.sub (P.sheaf.obj.map a.op (t V₁ h₁)) (P.sheaf.obj.map b.op (t V₂ h₂)) =
        P'.sub (P'.sheaf.obj.map a.op (t' V₁ h₁)) (P'.sheaf.obj.map b.op (t' V₂ h₂))) :
    P ≈ P' := by
  have hP' := (isSheaf_iff_isSheaf_of_type J P'.sheaf.obj).1 P'.sheaf.property
  have mem {V U : C} (k : V ⟶ U) (hk : R.pullback (hT.from U) k) : R (hT.from V) := by
    rwa [Sieve.pullback_apply, hT.hom_ext (k ≫ hT.from U) (hT.from V)] at hk
  -- the local values `(s - t V) + t' V`
  let x (U : C) (s : P.sheaf.obj.obj (op U)) :
      Presieve.FamilyOfElements P'.sheaf.obj (R.pullback (hT.from U)).arrows :=
    fun V k hk ↦ P'.vadd _ (P.sub (t V (mem k hk)) (P.sheaf.obj.map k.op s)) (t' V (mem k hk))
  have hx (U : C) (s : P.sheaf.obj.obj (op U)) : (x U s).Compatible := by
    intro V₁ V₂ Z g₁ g₂ k₁ k₂ hk₁ hk₂ fac
    simp only [x]
    rw [P'.map_vadd, P'.map_vadd, P.map_sub_apply, P.map_sub_apply, P.map_map_apply,
      P.map_map_apply, fac]
    exact vadd_sub_eq_vadd_sub P P' _ _ _ _ _ (h _ _ g₁ g₂)
  have hcov (U : C) : R.pullback (hT.from U) ∈ J U := J.pullback_stable _ hR
  let φ (U : C) (s : P.sheaf.obj.obj (op U)) : P'.sheaf.obj.obj (op U) :=
    (hP' _ (hcov U)).amalgamate (x U s) (hx U s)
  have hφ (U : C) (s : P.sheaf.obj.obj (op U)) {V : C} (k : V ⟶ U)
      (hk : R.pullback (hT.from U) k) : P'.sheaf.obj.map k.op (φ U s) = x U s k hk :=
    (hP' _ (hcov U)).valid_glue (hx U s) k hk
  let f : P.sheaf ⟶ P'.sheaf := ⟨{
    app U := TypeCat.ofHom (φ U.unop)
    naturality U U' g := by
      ext s
      refine (hP' _ (hcov U'.unop)).isSeparatedFor.ext fun V k hk ↦ ?_
      change P'.sheaf.obj.map k.op (φ U'.unop (P.sheaf.obj.map g.unop.op s)) =
        P'.sheaf.obj.map k.op (P'.sheaf.obj.map g.unop.op (φ U.unop s))
      have hk' : R.pullback (hT.from U.unop) (k ≫ g.unop) := by
        rw [Sieve.pullback_apply, hT.hom_ext ((k ≫ g.unop) ≫ hT.from _) (hT.from V)]
        exact mem k hk
      rw [hφ _ _ k hk, P'.map_map_apply (U := U.unop) g.unop k, hφ _ _ _ hk']
      simp only [x]
      congr 2
      rw [P.map_map_apply (U := U.unop) g.unop k] }⟩
  refine ⟨Iso.ofHom f fun U a s ↦ ?_⟩
  refine (hP' _ (hcov U.unop)).isSeparatedFor.ext fun V k hk ↦ ?_
  change P'.sheaf.obj.map k.op (φ U.unop (P.vadd U a s)) =
    P'.sheaf.obj.map k.op (P'.vadd U a (φ U.unop s))
  rw [hφ _ _ k hk, P'.map_vadd, hφ _ _ k hk]
  simp only [x]
  rw [P.map_vadd, P.sub_vadd_right, P'.add_vadd]

end CategoryTheory.Sheaf.Torsor
