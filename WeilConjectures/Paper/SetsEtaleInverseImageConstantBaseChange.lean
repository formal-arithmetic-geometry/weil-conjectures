/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits

/-! # Base change of an indexed coproduct of copies of a scheme

Source: literature/stacks-project/schemes.tex, Tags 01JB and 01JC; Section 26.17
(blueprint: lem-weil-pbc-sets-etale-inverse-image-constant-base-change)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/--
Base change preserves an indexed coproduct of copies of a scheme.

Source: literature/stacks-project/schemes.tex, Tags 01JB and 01JC; Section 26.17
(blueprint: lem-weil-pbc-sets-etale-inverse-image-constant-base-change).
Proof:
1. By `lem-weil-pbc-scheme-coproduct-family`, coprojections are open immersions
   with pairwise disjoint images covering the coproduct. Use `def-pc-fibre-product`
   to form the maps with projections identity and v followed by the coprojection;
   assemble them using `Sigma.desc`.
2. By `lem-weil-pbc-open-fibre-product`, the inverse image of each summand is an
   open subscheme isomorphic to V. These opens are disjoint and cover the pullback.
   By `lem-weil-pbc-scheme-morphism-gluing`, glue their inverse maps into the
   coproduct of copies of V. Both composites are identities by uniqueness of
   coproduct maps and gluing. The displayed restriction formula identifies each
   coprojection with its base change.
-/
theorem baseChange_sigmaScheme_iso
    (U V : Scheme.{u}) (v : V ⟶ U) (E : Type u) :
    IsIso (Sigma.desc (fun e ↦
      pullback.lift (f := v) (g := Sigma.desc (fun _ : E ↦ 𝟙 U))
          (𝟙 V) (v ≫ Sigma.ι (fun _ : E ↦ U) e) (by simp))) ∧
      ∀ e : E,
        Sigma.ι (fun _ : E ↦ V) e ≫
            Sigma.desc (fun e ↦
              pullback.lift (f := v) (g := Sigma.desc (fun _ : E ↦ 𝟙 U))
          (𝟙 V) (v ≫ Sigma.ι (fun _ : E ↦ U) e) (by simp)) =
          pullback.lift (f := v) (g := Sigma.desc (fun _ : E ↦ 𝟙 U))
          (𝟙 V) (v ≫ Sigma.ι (fun _ : E ↦ U) e) (by simp) := by
  classical
  let c : (∐ fun _ : E ↦ U) ⟶ U := Sigma.desc fun _ ↦ 𝟙 U
  let j (e : E) : V ⟶ pullback v c :=
    pullback.lift (𝟙 V) (v ≫ Sigma.ι (fun _ : E ↦ U) e) (by simp [c])
  let 𝒰 := Scheme.Pullback.openCoverOfRight (sigmaOpenCover (fun _ : E ↦ U)) v c
  let a (e : E) : V ≅ pullback v (Sigma.ι (fun _ : E ↦ U) e ≫ c) :=
    { hom := pullback.lift (𝟙 V) v (by simp [c])
      inv := pullback.fst _ _
      hom_inv_id := by simp
      inv_hom_id := by
        apply pullback.hom_ext
        · simp
        · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
          simpa [c] using (pullback.condition (f := v)
            (g := Sigma.ι (fun _ : E ↦ U) e ≫ c)) }
  have hj (e : E) : j e = (a e).hom ≫ 𝒰.f e := by
    change j e = (a e).hom ≫ pullback.map _ _ v c
      (𝟙 V) (Sigma.ι (fun _ : E ↦ U) e) (𝟙 U) (by simp) (by simp)
    apply pullback.hom_ext <;> simp [j, a]
  have (e : E) : IsOpenImmersion (j e) := by
    rw [hj]
    have : IsIso (a e).hom := (a e).isIso_hom
    have : IsOpenImmersion (𝒰.f e) := 𝒰.map_prop e
    exact IsOpenImmersion.comp _ _
  have hdisj : Pairwise (Function.onFun Disjoint fun e ↦ Set.range (j e)) := by
    intro e e' hne
    rw [Function.onFun_apply, Set.disjoint_left]
    rintro x ⟨y, rfl⟩ ⟨y', hy'⟩
    have h := congrArg (pullback.snd v c) hy'
    change (j e' ≫ pullback.snd v c) y' = (j e ≫ pullback.snd v c) y at h
    have h' : Sigma.ι (fun _ : E ↦ U) e' (v y') =
        Sigma.ι (fun _ : E ↦ U) e (v y) := by
      simpa only [j, pullback.lift_snd,
        Scheme.Hom.comp_apply] using h
    have heq := (sigmaι_eq_iff (fun _ : E ↦ U) e' e _ _).mp h'
    exact hne (congrArg (fun z : Σ _ : E, U ↦ z.1) heq).symm
  have : IsOpenImmersion (Sigma.desc j) :=
    isOpenImmersion_sigmaDesc (fun _ : E ↦ V) j hdisj
  constructor
  · apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [eq_top_iff]
    intro x _
    obtain ⟨e, y, rfl⟩ := 𝒰.exists_eq x
    refine ⟨Sigma.ι (fun _ : E ↦ V) e ((a e).inv y), ?_⟩
    have hcomp : (a e).inv ≫ j e = 𝒰.f e := by rw [hj]; simp
    change (Sigma.ι (fun _ : E ↦ V) e ≫ Sigma.desc j) ((a e).inv y) = 𝒰.f e y
    rw [Sigma.ι_desc]
    exact congrArg (fun f : pullback v (Sigma.ι (fun _ : E ↦ U) e ≫ c) ⟶
      pullback v c ↦ f y) hcomp
  · intro e
    exact Sigma.ι_desc _ _

end AlgebraicGeometry
