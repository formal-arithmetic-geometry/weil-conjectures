/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.CategoryTheory.Galois.StacksGaloisCategory
import Sheaf.CategoryTheory.Galois.StacksGaloisAxioms
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Complements of monomorphisms in Stacks Galois categories

Source: Stacks Project, Definition 0BMY, Lemma 0BN0, and the component argument in
Proposition 0BN4 (blueprint: lem-galois-stacks-mono-complement).
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace CategoryTheory

/-- Every monomorphism in a Stacks Galois category is a coproduct summand inclusion.
Source: Stacks Project, Definition 0BMY and Lemma 0BN0; the component argument of
Proposition 0BN4 (blueprint: lem-galois-stacks-mono-complement).

Proof: Decompose the target into finitely many connected objects. Pull back the
monomorphism to each component. The resulting monomorphism into a connected object
is an isomorphism if its source is noninitial, by the definition of connectedness;
otherwise its source is initial. Let Z be the coproduct of precisely the components
with initial pullback, with its canonical map to the target. Exactness of the fibre
functor identifies the target fibre with the disjoint union of the component fibres,
and identifies each pullback fibre with the inverse image of that component. Thus
on each component the image of the original mono is either the whole component or
empty. Mono detection (Lemma 0BN0(2)) makes the original fibre map injective, so the
two fibre maps are injective with complementary ranges. The explicit binary
coproduct criterion in `Type` gives a colimit cofan. Since an exact conservative
functor reflects finite colimits, this yields the claimed colimit in the category.
Empty decompositions,
the initial source, and an isomorphism are included: the required complementary
coproduct may be empty. -/
theorem stacksGalois_mono_complement {C : Type u} [Category.{v} C]
    (F : C ⥤ Type w) (hG : IsStacksGaloisCategory F)
    {X Y : C} (i : X ⟶ Y) [Mono i] :
    ∃ (Z : C) (j : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i j)) := by
  classical
  let := hG.hasFiniteLimits
  let := hG.hasFiniteColimits
  let := hG.preservesFiniteLimits
  let := hG.preservesFiniteColimits
  let := hG.reflectsIsomorphisms
  have haxioms := stacksGaloisCategory_axioms.{0, 0, w, v, u} F hG
  obtain ⟨ι, hι, Yj, κ, ⟨hY⟩, hconn⟩ := hG.exists_finite_coproduct_isConnected Y
  let := hι
  have hFY := isColimitCofanMkObjOfIsColimit F Yj κ hY
  let P (a : ι) := pullback i (κ a)
  let p (a : ι) : P a ⟶ Yj a := pullback.snd i (κ a)
  have hp (a : ι) : Mono (p a) := by dsimp [p]; infer_instance
  have hempty (a : ι) : Nonempty (IsInitial (P a)) ↔ IsEmpty (F.obj (P a)) :=
    (haxioms.2.2.1 (P a)).1
  have hiso (a : ι) (h : ¬ Nonempty (IsInitial (P a))) : IsIso (p a) := by
    let := hconn a
    let := hp a
    exact IsConnected.noTrivialComponent (P a) (p a) (fun hi ↦ h ⟨hi⟩)
  let J := {a : ι // Nonempty (IsInitial (P a))}
  let Z := ∐ (fun a : J ↦ Yj a.1)
  let j : Z ⟶ Y := Sigma.desc (fun a : J ↦ κ a.1)
  have hFZ := isColimitCofanMkObjOfIsColimit F (fun a : J ↦ Yj a.1)
    (Sigma.ι (fun a : J ↦ Yj a.1)) (coproductIsCoproduct _)
  have hfac (a : J) (z : F.obj (Yj a.1)) :
      F.map j (F.map (Sigma.ι (fun a : J ↦ Yj a.1) a) z) = F.map (κ a.1) z := by
    have h := F.congr_map (Sigma.ι_desc (fun a : J ↦ κ a.1) a)
    simpa only [F.map_comp, types_comp, Function.comp_apply, j] using
      ConcreteCategory.congr_hom h z
  have hnot (a : J) (z : F.obj (Yj a.1)) :
      F.map (κ a.1) z ∉ Set.range (F.map i) := by
    rintro ⟨x, hx⟩
    let e := (PreservesPullback.iso F i (κ a.1) ≪≫
      Types.pullbackIsoPullback (F.map i) (F.map (κ a.1))).toEquiv
    have h := hempty a.1 |>.mp a.2
    exact h.false (e.symm ⟨(x, z), hx⟩)
  have hj : Function.Injective (F.map j) := by
    intro z₁ z₂ hz
    obtain ⟨a, x, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hFZ z₁
    obtain ⟨b, y, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hFZ z₂
    change F.map j (F.map (Sigma.ι (fun a : J ↦ Yj a.1) a) x) =
      F.map j (F.map (Sigma.ι (fun a : J ↦ Yj a.1) b) y) at hz
    rw [hfac, hfac] at hz
    have hab := Cofan.eq_of_inj_apply_eq_of_isColimit hFY x y hz
    have hab' : a = b := Subtype.ext hab
    subst b
    have hxy := Cofan.inj_injective_of_isColimit hFY a.1 hz
    subst y
    rfl
  have hrange : Set.range (F.map j) = (Set.range (F.map i))ᶜ := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨a, x, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hFZ z
      change F.map j (F.map (Sigma.ι (fun a : J ↦ Yj a.1) a) x) ∉ _
      rw [hfac]
      exact hnot a x
    · intro hy
      obtain ⟨a, z, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hFY y
      have ha : Nonempty (IsInitial (P a)) := by
        by_contra hn
        let := hiso a hn
        have hpF : Function.Surjective (F.map (p a)) := by
          exact (ConcreteCategory.isIso_iff_bijective (F.map (p a))).mp inferInstance |>.2
        obtain ⟨t, ht⟩ := hpF z
        apply hy
        refine ⟨F.map (pullback.fst i (κ a)) t, ?_⟩
        have hc := ConcreteCategory.congr_hom
          (F.congr_map (pullback.condition (f := i) (g := κ a))) t
        simp only [F.map_comp, types_comp, Function.comp_apply] at hc
        change F.map i (F.map (pullback.fst i (κ a)) t) =
          F.map (κ a) (F.map (p a) t) at hc
        rw [ht] at hc
        exact hc
      refine ⟨F.map (Sigma.ι (fun a : J ↦ Yj a.1) ⟨a, ha⟩) z, ?_⟩
      exact hfac ⟨a, ha⟩ z
  have hcol : Nonempty (IsColimit (BinaryCofan.mk (F.map i) (F.map j))) := by
    apply (Types.binaryCofan_isColimit_iff _).mpr
    refine ⟨(haxioms.2.1 i).1.mp inferInstance, hj, ?_⟩
    change IsCompl (Set.range (F.map i)) (Set.range (F.map j))
    rw [hrange]
    exact isCompl_compl
  exact ⟨Z, j, ⟨isColimitOfReflectsOfMapIsColimit F i j hcol.some⟩⟩

end CategoryTheory
