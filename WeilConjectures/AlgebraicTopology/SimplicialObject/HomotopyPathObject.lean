/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicTopology.SimplicialObject.PrismPath
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# The object of homotopies between two maps of simplicial objects

Let `a b : U ⟶ V` be maps of simplicial objects in a category with finite limits. The
simplicial object `pathSpace a b` has as `n`-simplices the pairs `(u, h)` of an `n`-simplex `u`
of `U` and a path family `h` (prism simplices) of `V` from `a u` to `b u`. Its projection to
`U` is homotopic, after composition with `a` and `b`, through the tautological homotopy.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SimplexCategory

namespace CategoryTheory.SimplicialObject

variable {C : Type*} [Category* C] {U V : SimplicialObject C} (a b : U ⟶ V)

/-- The shape of the limit defining the `n`-simplices of the path space. -/
def pathShape (n : ℕ) : MulticospanShape where
  L := Option (Fin (n + 1))
  R := Option (Option (Fin n))
  fst
    | none => some 0
    | some none => some (Fin.last n)
    | some (some j) => some j.succ
  snd
    | none => none
    | some none => none
    | some (some j) => some j.castSucc

/-- The diagram defining the `n`-simplices of the path space. -/
def pathIndex (n : ℕ) : MulticospanIndex (pathShape n) C where
  left
    | none => U _⦋n⦌
    | some _ => V _⦋n + 1⦌
  right _ := V _⦋n⦌
  fst
    | none => V.δ 0
    | some none => V.δ (Fin.last (n + 1))
    | some (some j) => V.δ j.succ.castSucc
  snd
    | none => b.app _
    | some none => a.app _
    | some (some j) => V.δ j.succ.castSucc

instance (n : ℕ) : Fintype (pathShape n).L := inferInstanceAs (Fintype (Option (Fin (n + 1))))
instance (n : ℕ) : Fintype (pathShape n).R :=
  inferInstanceAs (Fintype (Option (Option (Fin n))))
instance (n : ℕ) : DecidableEq (pathShape n).L :=
  inferInstanceAs (DecidableEq (Option (Fin (n + 1))))
instance (n : ℕ) : DecidableEq (pathShape n).R :=
  inferInstanceAs (DecidableEq (Option (Option (Fin n))))

variable [HasFiniteLimits C]

/-- The `n`-simplices of the path space. -/
noncomputable abbrev pathObj (n : ℕ) : C := multiequalizer (pathIndex a b n)

/-- The projection to `U`. -/
noncomputable abbrev pathU (n : ℕ) : pathObj a b n ⟶ U _⦋n⦌ :=
  Multiequalizer.ι (pathIndex a b n) none

/-- The prism simplices. -/
noncomputable abbrev pathH (n : ℕ) (j : Fin (n + 1)) : pathObj a b n ⟶ V _⦋n + 1⦌ :=
  Multiequalizer.ι (pathIndex a b n) (some j)

lemma isPathFamily_pathH (n : ℕ) : V.IsPathFamily (pathH a b n) := fun j ↦
  Multiequalizer.condition (pathIndex a b n) (some (some j))

lemma pathH_zero (n : ℕ) : pathH a b n 0 ≫ V.δ 0 = pathU a b n ≫ b.app _ :=
  Multiequalizer.condition (pathIndex a b n) none

lemma pathH_last (n : ℕ) :
    pathH a b n (Fin.last n) ≫ V.δ (Fin.last (n + 1)) = pathU a b n ≫ a.app _ :=
  Multiequalizer.condition (pathIndex a b n) (some none)

/-- Constructor of maps to the `n`-simplices of the path space. -/
noncomputable def pathLift {T : C} {n : ℕ} (u : T ⟶ U _⦋n⦌) (h : Fin (n + 1) → (T ⟶ V _⦋n + 1⦌))
    (hh : V.IsPathFamily h) (h₀ : h 0 ≫ V.δ 0 = u ≫ b.app _)
    (h₁ : h (Fin.last n) ≫ V.δ (Fin.last (n + 1)) = u ≫ a.app _) : T ⟶ pathObj a b n :=
  Multiequalizer.lift (pathIndex a b n) T
    (fun | none => u | some j => h j)
    (by
      rintro (_ | _ | j)
      · exact h₀
      · exact h₁
      · exact hh j)

@[reassoc (attr := simp)]
lemma pathLift_pathU {T : C} {n : ℕ} (u : T ⟶ U _⦋n⦌) (h : Fin (n + 1) → (T ⟶ V _⦋n + 1⦌))
    (hh : V.IsPathFamily h) (h₀) (h₁) : pathLift a b u h hh h₀ h₁ ≫ pathU a b n = u :=
  Multiequalizer.lift_ι _ _ _ _ _

@[reassoc (attr := simp)]
lemma pathLift_pathH {T : C} {n : ℕ} (u : T ⟶ U _⦋n⦌) (h : Fin (n + 1) → (T ⟶ V _⦋n + 1⦌))
    (hh : V.IsPathFamily h) (h₀) (h₁) (j : Fin (n + 1)) :
    pathLift a b u h hh h₀ h₁ ≫ pathH a b n j = h j :=
  Multiequalizer.lift_ι _ _ _ _ _

lemma pathObj_hom_ext {T : C} {n : ℕ} {f g : T ⟶ pathObj a b n}
    (hu : f ≫ pathU a b n = g ≫ pathU a b n) (hh : ∀ j, f ≫ pathH a b n j = g ≫ pathH a b n j) :
    f = g :=
  Multiequalizer.hom_ext _ _ _ (by rintro (_ | j); exacts [hu, hh j])

/-- The action of simplicial operators on the path space. -/
noncomputable def pathMapObj {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) : pathObj a b n ⟶ pathObj a b m :=
  pathLift a b (pathU a b n ≫ U.map θ.op) (V.pathMap θ (pathH a b n))
    (isPathFamily_pathMap θ (isPathFamily_pathH a b n))
    (by
      rw [pathMap_zero_δ_zero θ (isPathFamily_pathH a b n), ← Category.assoc, pathH_zero,
        Category.assoc, Category.assoc, b.naturality])
    (by
      rw [pathMap_last_δ_last θ (isPathFamily_pathH a b n), ← Category.assoc, pathH_last,
        Category.assoc, Category.assoc, a.naturality])

@[reassoc (attr := simp)]
lemma pathMapObj_pathU {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    pathMapObj a b θ ≫ pathU a b m = pathU a b n ≫ U.map θ.op :=
  pathLift_pathU _ _ _ _ _ _ _

@[reassoc (attr := simp)]
lemma pathMapObj_pathH {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (k : Fin (m + 1)) :
    pathMapObj a b θ ≫ pathH a b m k = V.pathMap θ (pathH a b n) k :=
  pathLift_pathH _ _ _ _ _ _ _ _

/-- The simplicial object of homotopies from `a` to `b`. -/
noncomputable def pathSpace : SimplicialObject C where
  obj Δ := pathObj a b Δ.unop.len
  map θ := pathMapObj a b θ.unop
  map_id Δ := by
    refine pathObj_hom_ext a b ?_ fun j ↦ ?_
    · simp
    · rw [pathMapObj_pathH, unop_id, pathMap_id, Category.id_comp]
  map_comp θ θ' := by
    refine pathObj_hom_ext a b ?_ fun j ↦ ?_
    · simp
    · rw [unop_comp, pathMapObj_pathH, Category.assoc, pathMapObj_pathH, pathMap, pathMap,
        ← Category.assoc, pathMapObj_pathH, pathMap, Category.assoc, ← Functor.map_comp,
        ← op_comp, prism_comp, comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
      rfl

end CategoryTheory.SimplicialObject
