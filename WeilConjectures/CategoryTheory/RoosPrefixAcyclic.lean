/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.RoosFinitePrefixes
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.CategoryTheory.InjectiveTowerEmbedding
import WeilConjectures.CategoryTheory.InjectiveSplitTower
import WeilConjectures.CategoryTheory.MittagLefflerLimitExact
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Acyclicity of finite-prefix towers

Source: Stacks Project, Tag 07KW, Lemma 15.88.1 (3).
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

/-- A finite-prefix tower is acyclic for inverse limits.

Source: Stacks Project, Tag 07KW, Lemma 15.88.1 (3). -/
theorem roosPrefixAcyclic
    [EnoughInjectives (ℕᵒᵖ ⥤ AddCommGrpCat.{u})]
    [(lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).Additive]
    (s : ℕ) (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ∀ q : ℕ, 1 ≤ q → IsZero ((lim.rightDerived q).obj ((roosPrefixFunctor s).obj A)) := by
  classical
  let F := (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u})
  have ml_of_surj (B : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
      (hB : ∀ n : ℕ,
        Function.Surjective (B.map (homOfLE (Nat.le_succ n)).op)) :
      (B ⋙ forget AddCommGrpCat).IsMittagLeffler := by
    apply Functor.isMittagLeffler_of_surjective
    intro i j f
    have hs (n m : ℕ) (h : n ≤ m) :
        Function.Surjective (B.map (homOfLE h).op) := by
      induction m, h using Nat.le_induction with
      | base => simpa using (Function.surjective_id : Function.Surjective
          (fun x : B.obj (Opposite.op n) ↦ x))
      | succ m h ih =>
        have he : (homOfLE (Nat.le_succ_of_le h)).op =
            (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
        rw [he, B.map_comp]
        exact ih.comp (hB m)
    exact hs j.unop i.unop (leOfHom f.unop)
  obtain ⟨⟨G, hadd, δ, hmono, hmid, hright, hleft, hnat⟩, hG, _⟩ :=
    exists_horseshoe_rightDerived_deltaFunctor F
  dsimp only at hG
  subst G
  have vanishing (q : ℕ) : ∀ B : ℕᵒᵖ ⥤ AddCommGrpCat.{u},
      (B ⋙ forget AddCommGrpCat).IsMittagLeffler →
      IsZero ((F.rightDerived (q + 1)).obj B) := by
    induction q with
    | zero =>
      intro B hB
      obtain ⟨I, i, hi, hI, hp⟩ := tower_injective_embedding B
      let :=  hi
      let :=  injective_of_injective_split_tower I hI hp
      let S := ShortComplex.cokernelSequence i
      have hS : S.ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i)
          (by change Mono i; exact hi) (by change Epi (cokernel.π i); infer_instance)
      have hlevels : ∀ n : ℕᵒᵖ,
          (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).ShortExact :=
        fun n ↦ hS.map_of_exact _
      have hl := (ShortComplex.mittagLeffler_quotient_and_limit_exact S hlevels).2 hB
      have : Epi (F.map S.g) := hl.epi_g
      have : Epi ((F.rightDerived 0).map S.g) := by
        apply (epi_comp_iff_of_isIso _ (F.rightDerivedZeroIsoSelf.hom.app S.X₃)).mp
        rw [F.rightDerivedZeroIsoSelf.hom.naturality S.g]
        infer_instance
      obtain ⟨hz, hex⟩ := hright S hS 0
      have hd : δ S hS 0 = 0 := hex.epi_f_iff.mp inferInstance
      obtain ⟨hz', hex'⟩ := hleft S hS 0
      exact hex'.isZero_X₂ hd
        ((F.isZero_rightDerived_obj_injective_succ 0 I).eq_of_tgt _ _)
    | succ q ih =>
      intro B hB
      obtain ⟨I, i, hi, hI, hp⟩ := tower_injective_embedding B
      let :=  hi
      let :=  injective_of_injective_split_tower I hI hp
      let S := ShortComplex.cokernelSequence i
      have hS : S.ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i)
          (by change Mono i; exact hi) (by change Epi (cokernel.π i); infer_instance)
      have hlevels : ∀ n : ℕᵒᵖ,
          (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).ShortExact :=
        fun n ↦ hS.map_of_exact _
      have hIML := ml_of_surj I (fun n ↦ by
        let :=  hp n
        exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance)
      have hQ := (ShortComplex.mittagLeffler_quotient_and_limit_exact S hlevels).1 hIML
      obtain ⟨hz, hex⟩ := hleft S hS (q + 1)
      exact hex.isZero_X₂ ((ih S.X₃ hQ).eq_of_src _ _)
        ((F.isZero_rightDerived_obj_injective_succ (q + 1) I).eq_of_tgt _ _)
  intro q hq
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  exact vanishing n ((roosPrefixFunctor s).obj A)
    (ml_of_surj _ (roosPrefix_transition_surjective s A))

end CategoryTheory
