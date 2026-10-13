module

public import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v w t

private theorem tower_family_compatible
    (R : Type u) [CommRing R] (G : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (a : ∀ n : ℕ, G.obj (Opposite.op n))
    (ha : ∀ n, G.map (homOfLE (Nat.le_add_right n 1)).op (a (n + 1)) = a n) :
    (fun j : ℕᵒᵖ ↦ a j.unop) ∈ (G ⋙ forget (ModuleCat R)).sections := by
  let τ : (Functor.const ℕᵒᵖ).obj PUnit ⟶ G ⋙ forget (ModuleCat R) :=
    NatTrans.ofOpSequence (fun n ↦ ↾fun _ ↦ a n) (by
      intro n
      ext x
      exact (ha n).symm)
  intro i j f
  exact (ConcreteCategory.congr_hom (τ.naturality f) PUnit.unit).symm

private theorem tower_induced_map
    (R : Type u) [CommRing R]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} R) (G : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (α : ∀ n : ℕ, F.obj (Opposite.op n) →ₗ[R] G.obj (Opposite.op n))
    (hα : ∀ (n : ℕ) (x : F.obj (Opposite.op (n + 1))),
      G.map (homOfLE (Nat.le_add_right n 1)).op (α (n + 1) x) =
        α n (F.map (homOfLE (Nat.le_add_right n 1)).op x)) :
    ∃ U : ↑(limit F) →ₗ[R] ↑(limit G), ∀ (n : ℕ) (x : ↑(limit F)),
      limit.π G (Opposite.op n) (U x) = α n (limit.π F (Opposite.op n) x) := by
  let e := Types.isLimitEquivSections
    (isLimitOfPreserves (forget (ModuleCat R)) (limit.isLimit G))
  have hcompat (x : ↑(limit F)) :
      (fun j : ℕᵒᵖ ↦ α j.unop (limit.π F j x)) ∈
        (G ⋙ forget (ModuleCat R)).sections := by
    apply tower_family_compatible R G
      (fun n ↦ α n (limit.π F (Opposite.op n) x))
    intro n
    rw [hα]
    congr 1
    exact ConcreteCategory.congr_hom (limit.w F (homOfLE (Nat.le_add_right n 1)).op) x
  let f : ↑(limit F) → ↑(limit G) := fun x ↦ e.symm ⟨_, hcompat x⟩
  have hf (j : ℕᵒᵖ) (x : ↑(limit F)) :
      limit.π G j (f x) = α j.unop (limit.π F j x) :=
    Types.isLimitEquivSections_symm_apply
      (isLimitOfPreserves (forget (ModuleCat R)) (limit.isLimit G)) ⟨_, hcompat x⟩ j
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply Concrete.limit_ext G
    intro j
    simp only [hf, map_add]
  · intro r x
    apply Concrete.limit_ext G
    intro j
    simp only [hf, map_smul, RingHom.id_apply]
  · intro n x
    exact hf (Opposite.op n) x

/-- Componentwise maps on inverse limits exist and are characterized by their
coordinate projections, under the stated naturality hypotheses.
Source: the componentwise construction in Stacks Project, Algebra Lemma 03CA.
(blueprint: new-tower-limit-induced-maps).
-/
theorem tower_limit_induced_maps
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
        β n (G.map (homOfLE (Nat.le_add_right n 1)).op x)) :
    ∃ (U : ↑(limit F) →ₗ[R] ↑(limit G)) (V : ↑(limit G) →ₗ[R] ↑(limit H)),
      (∀ (n : ℕ) (x : ↑(limit F)),
        limit.π G (Opposite.op n) (U x) = α n (limit.π F (Opposite.op n) x)) ∧
      (∀ (n : ℕ) (x : ↑(limit G)),
        limit.π H (Opposite.op n) (V x) = β n (limit.π G (Opposite.op n) x)) := by
  obtain ⟨U, hU⟩ := tower_induced_map R F G α hα
  obtain ⟨V, hV⟩ := tower_induced_map R G H β hβ
  exact ⟨U, V, hU, hV⟩

end CategoryTheory
