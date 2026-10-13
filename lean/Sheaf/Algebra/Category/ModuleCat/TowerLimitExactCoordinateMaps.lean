module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Exact.Basic

/-!
# Exactness of coordinate maps on tower limits

Source: Stacks Project, Algebra Lemma 03CA and Homology Lemma 02N1.
The proof uses uniqueness of kernel preimages and recursive correction of quotient lifts.
(blueprint: new-tower-limit-exact-coordinate-maps).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v w t

private theorem limit_succ_apply
    {R : Type u} [CommRing R] (K : ℕᵒᵖ ⥤ ModuleCat.{v} R)
    (n : ℕ) (x : ↑(limit K)) :
    K.map (homOfLE (Nat.le_succ n)).op (limit.π K (Opposite.op (n + 1)) x) =
      limit.π K (Opposite.op n) x :=
  ConcreteCategory.congr_hom (limit.w K (homOfLE (Nat.le_succ n)).op) x

private theorem exists_limit_of_succ
    {R : Type u} [CommRing R] (F : ℕᵒᵖ ⥤ ModuleCat.{v} R)
    (x : ∀ n : ℕ, F.obj (Opposite.op n))
    (hx : ∀ n, F.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n) :
    ∃ y : ↑(limit F), ∀ n, limit.π F (Opposite.op n) y = x n := by
  have hmap : ∀ n m (h : n ≤ m), F.map (homOfLE h).op (x m) = x n := by
    intro n m h
    induction h with
    | refl => simp
    | @step m h ih =>
      have he : (homOfLE (Nat.le_succ_of_le h)).op =
          (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
      rw [he, F.map_comp]
      change F.map (homOfLE h).op (F.map (homOfLE (Nat.le_succ m)).op (x (m + 1))) = _
      rw [hx, ih]
  let s : (F ⋙ forget (ModuleCat R)).sections := ⟨fun j ↦ x j.unop, by
    intro j j' f
    change F.map f (x j.unop) = x j'.unop
    have he : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
    rw [he]
    exact hmap _ _ _⟩
  let e := Types.isLimitEquivSections
    (isLimitOfPreserves (forget (ModuleCat R)) (limit.isLimit F))
  refine ⟨e.symm s, ?_⟩
  intro n
  exact congrArg (fun s : (F ⋙ forget (ModuleCat R)).sections ↦ s.val (Opposite.op n))
    (e.apply_symm_apply s)

-- The original signature omitted compatibility of α and β with transitions.
-- This is corrected below; see coord/changes/tower-limit-coordinate-naturality.md.
/-- Coordinatewise exactness implies exactness of the induced maps on inverse limits;
with surjective kernel transitions the second induced map is surjective.
Source: Stacks Project, Algebra Lemma 03CA and Homology Lemma 02N1.
(blueprint: new-tower-limit-exact-coordinate-maps).
-/
theorem tower_limit_exact_of_coordinate_maps
    (R : Type u) [CommRing R]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} R) (G : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (H : ℕᵒᵖ ⥤ ModuleCat.{t} R)
    (α : ∀ n : ℕ, F.obj (Opposite.op n) →ₗ[R] G.obj (Opposite.op n))
    (β : ∀ n : ℕ, G.obj (Opposite.op n) →ₗ[R] H.obj (Opposite.op n))
    (hα : ∀ (n : ℕ) (x : F.obj (Opposite.op (n + 1))),
      G.map (homOfLE (Nat.le_add_right n 1)).op (α (n + 1) x) =
        α n (F.map (homOfLE (Nat.le_add_right n 1)).op x))
    (hβ : ∀ (n : ℕ) (x : G.obj (Opposite.op (n + 1))),
      H.map (homOfLE (Nat.le_add_right n 1)).op (β (n + 1) x) =
        β n (G.map (homOfLE (Nat.le_add_right n 1)).op x))
    (hshort : ∀ n : ℕ, Function.Injective (α n) ∧ Function.Exact (α n) (β n) ∧
      Function.Surjective (β n))
    (U : ↑(limit F) →ₗ[R] ↑(limit G)) (V : ↑(limit G) →ₗ[R] ↑(limit H))
    (hU : ∀ (n : ℕ) (x : ↑(limit F)),
      limit.π G (Opposite.op n) (U x) = α n (limit.π F (Opposite.op n) x))
    (hV : ∀ (n : ℕ) (x : ↑(limit G)),
      limit.π H (Opposite.op n) (V x) = β n (limit.π G (Opposite.op n) x)) :
    Function.Injective U ∧ Function.Exact U V ∧
      ((∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_add_right n 1)).op)) →
        Function.Surjective V) := by
  classical
  have hinj : Function.Injective U := by
    intro x y hxy
    apply Concrete.limit_ext F
    intro j
    apply (hshort j.unop).1
    rw [← hU, ← hU, hxy]
  refine ⟨hinj, ?_, ?_⟩
  · intro y
    constructor
    · intro hy
      have hp : ∀ n, ∃ x, α n x = limit.π G (Opposite.op n) y := by
        intro n
        apply ((hshort n).2.1 _).mp
        rw [← hV, hy]
        simp
      choose x hx using hp
      have hc : ∀ n, F.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n := by
        intro n
        apply (hshort n).1
        rw [← hα, hx, hx]
        exact limit_succ_apply G n y
      obtain ⟨z, hz⟩ := exists_limit_of_succ F x hc
      refine ⟨z, Concrete.limit_ext G _ _ ?_⟩
      intro j
      rw [hU, hz, hx]
    · rintro ⟨x, rfl⟩
      apply Concrete.limit_ext H
      intro j
      rw [hV, hU, (hshort j.unop).2.1.apply_apply_eq_zero]
      simp
  · intro hs z
    have hstep (n : ℕ) (b : G.obj (Opposite.op n))
        (hb : β n b = limit.π H (Opposite.op n) z) :
        ∃ b' : G.obj (Opposite.op (n + 1)),
          β (n + 1) b' = limit.π H (Opposite.op (n + 1)) z ∧
          G.map (homOfLE (Nat.le_succ n)).op b' = b := by
      obtain ⟨b', hb'⟩ := (hshort (n + 1)).2.2
        (limit.π H (Opposite.op (n + 1)) z)
      have hk : β n (G.map (homOfLE (Nat.le_succ n)).op b' - b) = 0 := by
        rw [map_sub, ← hβ, hb', limit_succ_apply H n z, hb, sub_self]
      obtain ⟨a, ha⟩ := ((hshort n).2.1 _).mp hk
      obtain ⟨a', ha'⟩ := hs n a
      refine ⟨b' - α (n + 1) a', ?_, ?_⟩
      · rw [map_sub, (hshort (n + 1)).2.1.apply_apply_eq_zero, sub_zero, hb']
      · rw [map_sub, hα, ha', ha, sub_sub_cancel]
    let B (n : ℕ) := {b : G.obj (Opposite.op n) //
      β n b = limit.π H (Opposite.op n) z}
    let b0 : B 0 := ⟨((hshort 0).2.2 (limit.π H (Opposite.op 0) z)).choose,
      ((hshort 0).2.2 (limit.π H (Opposite.op 0) z)).choose_spec⟩
    let next (n : ℕ) (b : B n) : B (n + 1) :=
      ⟨(hstep n b.val b.property).choose, (hstep n b.val b.property).choose_spec.1⟩
    let b : ∀ n, B n := fun n ↦ Nat.rec (motive := B) b0 next n
    have hc : ∀ n, G.map (homOfLE (Nat.le_succ n)).op (b (n + 1)).val =
        (b n).val := by
      intro n
      exact (hstep n (b n).val (b n).property).choose_spec.2
    obtain ⟨y, hy⟩ := exists_limit_of_succ G (fun n ↦ (b n).val) hc
    refine ⟨y, Concrete.limit_ext H _ _ ?_⟩
    intro j
    rw [hV, hy]
    exact (b j.unop).property

end CategoryTheory
