/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Galois.StacksGaloisCategory
import WeilConjectures.CategoryTheory.Galois.StacksGaloisAxioms

/-!
# Coproduct complements of monomorphisms under the Stacks Galois axioms

Source: Stacks Project, Fundamental Groups of Schemes, Definition 0BMY,
Lemma 0BN0 and the component argument in Proposition 0BN4
(blueprint: lem-galois-stacks-mono-complement).
-/

@[expose] public section

universe u v w

open CategoryTheory.Limits

namespace CategoryTheory

set_option linter.style.haveILetI false in
/-- Under the Stacks Galois axioms, every monomorphism is a coproduct inclusion.
Source: Stacks Project, Definition 0BMY, Lemma 0BN0 and the component argument
in Proposition 0BN4 (blueprint: lem-galois-stacks-mono-complement).

Proof:
1. By `IsStacksGaloisCategory.exists_finite_coproduct_isConnected`
   (blueprint: def-galois-category), decompose `Y` into finitely many connected
   objects `Y_a`. Pull back `i` along each coprojection. The projection
   `P_a ⟶ Y_a` is mono, so connectedness says that it is an isomorphism or
   `P_a` is initial. Exactness sends the decomposition to a coproduct of fibres;
   `stacksGaloisCategory_axioms` (blueprint: lem-galois-axioms) detects initial
   objects by empty fibres.
2. Form `Z` as the coproduct of the `Y_a` for which `P_a` is initial, and let
   `j` be induced by the corresponding coprojections into `Y`. Preservation of
   pullbacks shows that these summands have fibres disjoint from the image of
   `F.map i`. For every remaining summand the projection from `P_a` is an
   isomorphism, so its entire fibre belongs to that image. The coproduct
   descriptions of the fibres show that `F.map j` is injective with image the
   complement of the image of `F.map i`. The latter map is injective by
   `stacksGaloisCategory_axioms` (blueprint: lem-galois-axioms).
3. The two injective maps with complementary images form a colimit binary
   cofan in sets, by `Types.binaryCofan_isColimit_iff`. Preservation of finite
   colimits and reflection of isomorphisms imply reflection of finite colimits
   (`reflectsFiniteColimitsOfReflectsIsomorphisms`). Reflect this binary
   colimit using `isColimitOfReflectsOfMapIsColimit`; its legs are `i` and `j`.
-/
theorem stacksGalois_mono_complement
    {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
    (hG : IsStacksGaloisCategory F) {X Y : C} (i : X ⟶ Y) [Mono i] :
    ∃ (Z : C) (j : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i j)) := by
  classical
  letI : HasFiniteLimits C := hG.hasFiniteLimits
  letI : HasFiniteColimits C := hG.hasFiniteColimits
  letI : PreservesFiniteLimits F := hG.preservesFiniteLimits
  letI : PreservesFiniteColimits F := hG.preservesFiniteColimits
  letI : F.ReflectsIsomorphisms := hG.reflectsIsomorphisms
  obtain ⟨ι, _, Yι, κ, ⟨hY⟩, hconn⟩ :=
    hG.exists_finite_coproduct_isConnected Y
  let hA := stacksGaloisCategory_axioms.{0, 0, w, v, u} F hG
  let P : ι → C := fun a => pullback i (κ a)
  let p : ∀ a, P a ⟶ Yι a := fun a => pullback.snd i (κ a)
  have p_mono (a : ι) : Mono (p a) := by
    dsimp [p]
    infer_instance
  let J : Type := {a : ι // Nonempty (IsInitial (P a))}
  letI : Finite J := Finite.of_injective Subtype.val Subtype.val_injective
  let Z : C := ∐ fun a : J => Yι a.1
  let j : Z ⟶ Y := Sigma.desc (fun a : J => κ a.1)
  have hYF : IsColimit (Cofan.mk (F.obj Y) (fun a => F.map (κ a))) :=
    isColimitCofanMkObjOfIsColimit F Yι κ hY
  have hZF : IsColimit (Cofan.mk (F.obj Z)
      (fun a : J => F.map (Sigma.ι (fun a : J => Yι a.1) a))) := by
    exact isColimitCofanMkObjOfIsColimit F _ _ (coproductIsCoproduct _)
  have initial_iff (T : C) : Nonempty (IsInitial T) ↔ IsEmpty (F.obj T) := by
    exact (hA.2.2.1 T).1
  have mono_iff_inj {A B : C} (f : A ⟶ B) :
      Mono f ↔ Function.Injective (F.map f) :=
    hA.2.1 f |>.1
  have hFi : Function.Injective (F.map i) := mono_iff_inj i |>.1 inferInstance
  have p_iso (a : ι) (ha : ¬ Nonempty (IsInitial (P a))) : IsIso (p a) := by
    apply (hconn a).noTrivialComponent _ _
    intro hi
    exact ha ⟨hi⟩
  have p_empty (a : ι) (ha : Nonempty (IsInitial (P a))) :
      IsEmpty (F.obj (P a)) := (initial_iff _).1 ha
  have j_fac (a : J) : Sigma.ι (fun a : J => Yι a.1) a ≫ j = κ a.1 := by
    dsimp [j]
    exact Sigma.ι_desc _ _
  have hFj_inj : Function.Injective (F.map j) := by
    intro z z' hzz'
    obtain ⟨a, za, hza⟩ := Cofan.inj_jointly_surjective_of_isColimit hZF z
    obtain ⟨a', za', hza'⟩ := Cofan.inj_jointly_surjective_of_isColimit hZF z'
    have hza0 : F.map (Sigma.ι (fun a : J => Yι a.1) a) za = z := by
      simpa only [Cofan.inj, Cofan.mk_pt, Cofan.mk_ι_app] using hza
    have hza1 : F.map (Sigma.ι (fun a : J => Yι a.1) a') za' = z' := by
      simpa only [Cofan.inj, Cofan.mk_pt, Cofan.mk_ι_app] using hza'
    rw [← hza0, ← hza1] at hzz'
    have hj (b : J) (zb : F.obj (Yι b.1)) :
        F.map j (F.map (Sigma.ι (fun a : J => Yι a.1) b) zb) =
          F.map (κ b.1) zb := by
      rw [← types_comp_apply, ← F.map_comp, j_fac]
    have ha : F.map (κ a.1) za = F.map (κ a'.1) za' := by
      rw [hj a za, hj a' za'] at hzz'
      exact hzz'
    have ha' : (Cofan.mk (F.obj Y) (fun a => F.map (κ a))).inj a.1 za =
        (Cofan.mk (F.obj Y) (fun a => F.map (κ a))).inj a'.1 za' := by
      simpa only [Cofan.inj, Cofan.mk_pt, Cofan.mk_ι_app] using ha
    have haa : a.1 = a'.1 := Cofan.eq_of_inj_apply_eq_of_isColimit hYF _ _ ha'
    cases a with
    | mk a haJ =>
      cases a' with
      | mk a' haJ' =>
        dsimp at haa
        cases haa
        have hza0 : F.map (Sigma.ι (fun a : J => Yι a.1) ⟨a, haJ⟩) za = z := by
          simpa only [Cofan.inj, Cofan.mk_pt, Cofan.mk_ι_app] using hza
        have hza1 : F.map (Sigma.ι (fun a : J => Yι a.1) ⟨a, haJ'⟩) za' = z' := by
          simpa only [Cofan.inj, Cofan.mk_pt, Cofan.mk_ι_app] using hza'
        have hzaa : F.map (Sigma.ι (fun a : J => Yι a.1) ⟨a, haJ⟩) za =
            F.map (Sigma.ι (fun a : J => Yι a.1) ⟨a, haJ'⟩) za' := by
          have hz : za = za' := Cofan.inj_injective_of_isColimit hYF a ha
          simp only [hz]
        exact hza0.symm.trans (hzaa.trans hza1)
  have hdisj : Disjoint (Set.range (F.map i)) (Set.range (F.map j)) := by
    rw [Set.disjoint_left]
    rintro y ⟨x, hx⟩ ⟨z, hz⟩
    obtain ⟨a, za, hza⟩ := Cofan.inj_jointly_surjective_of_isColimit hZF z
    have hza0 : F.map (Sigma.ι (fun a : J => Yι a.1) a) za = z := by
      simpa only [Cofan.inj, Cofan.mk_pt, Cofan.mk_ι_app] using hza
    have hEq : F.map i x = F.map j z := hx.trans hz.symm
    rw [← hza0] at hEq
    have hEq' : F.map i x = F.map (κ a.1) za := by
      rw [← types_comp_apply, ← F.map_comp, j_fac] at hEq
      exact hEq
    have hpb := (IsPullback.of_hasPullback i (κ a.1)).map F
    obtain ⟨e, _, _⟩ := Types.exists_of_isPullback hpb x za hEq'
    exact (p_empty a.1 a.2).false e
  have hcov : Set.range (F.map i) ∪ Set.range (F.map j) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨a, ya, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hYF y
    by_cases ha : Nonempty (IsInitial (P a))
    · right
      refine ⟨F.map (Sigma.ι (fun a : J => Yι a.1) ⟨a, ha⟩) ya, ?_⟩
      have hj : F.map j (F.map (Sigma.ι (fun a : J => Yι a.1) ⟨a, ha⟩) ya) =
          F.map (κ a) ya := by
        rw [← types_comp_apply, ← F.map_comp, j_fac]
      simpa only [Cofan.inj, Cofan.mk_pt, Cofan.mk_ι_app] using hj
    · left
      have hpi : IsIso (p a) := p_iso a ha
      letI : IsIso (p a) := hpi
      letI : IsIso (F.map (p a)) := inferInstance
      let x' := F.map (pullback.fst i (κ a)) (inv (F.map (p a)) ya)
      refine ⟨x', ?_⟩
      change F.map i
        (F.map (pullback.fst i (κ a)) (inv (F.map (p a)) ya)) =
        F.map (κ a) ya
      have hcomp : F.map (pullback.fst i (κ a)) ≫ F.map i =
          F.map (p a) ≫ F.map (κ a) := by
        rw [← F.map_comp, pullback.condition, F.map_comp]
      have hcomp' := congrArg (fun f => f (inv (F.map (p a)) ya)) hcomp
      have hcanc : F.map (p a) (inv (F.map (p a)) ya) = ya := by
        exact Iso.inv_hom_id_apply (asIso (F.map (p a))) ya
      simp only [types_comp_apply] at hcomp'
      rw [hcanc] at hcomp'
      exact hcomp'
  have htypes : Nonempty (IsColimit (BinaryCofan.mk (F.map i) (F.map j))) := by
    have hFi' : Function.Injective (BinaryCofan.mk (F.map i) (F.map j)).inl := by
      change Function.Injective (F.map i)
      exact hFi
    have hFj' : Function.Injective (BinaryCofan.mk (F.map i) (F.map j)).inr := by
      change Function.Injective (F.map j)
      exact hFj_inj
    refine (Types.binaryCofan_isColimit_iff _).2 ⟨hFi', hFj', ?_⟩
    rw [isCompl_iff]
    refine ⟨?_, ?_⟩
    · change Disjoint (Set.range (F.map i)) (Set.range (F.map j))
      exact hdisj
    · change Codisjoint (Set.range (F.map i)) (Set.range (F.map j))
      rw [codisjoint_iff]
      exact hcov
  letI : ReflectsColimit (pair X Z) F :=
    reflectsColimit_of_reflectsIsomorphisms (pair X Z) F
  obtain ⟨htypes⟩ := htypes
  have hc := isColimitOfReflectsOfMapIsColimit (X := X) (Y := Z)
    (f := i) (g := j) (G := F) htypes
  exact ⟨Z, j, ⟨hc⟩⟩

end CategoryTheory
