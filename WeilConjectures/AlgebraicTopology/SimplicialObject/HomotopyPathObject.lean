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

lemma pathSpace_map_pathH {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (k : Fin (m + 1)) :
    (pathSpace a b).map θ.op ≫ pathH a b m k =
      pathH a b n (θ.toOrderHom k) ≫ V.map (prism θ k).op :=
  pathMapObj_pathH a b θ k

/-- The projection of the path space to `U`. -/
@[simps]
noncomputable def pathProj : pathSpace a b ⟶ U where
  app Δ := pathU a b Δ.unop.len
  naturality _ _ θ := pathMapObj_pathU a b θ.unop

/-- The tautological homotopy on the path space. -/
noncomputable def pathHomotopy : Homotopy (pathProj a b ≫ a) (pathProj a b ≫ b) where
  h {n} j := pathH a b n j
  h_zero_comp_δ_zero n := pathH_zero a b n
  h_last_comp_δ_last n := pathH_last a b n
  h_succ_comp_δ_castSucc_of_lt {n} i j hij := by
    change _ = (pathSpace a b).map (SimplexCategory.δ i).op ≫ pathH a b n j
    rw [pathSpace_map_pathH, δ_apply_of_le i j (by simpa [Fin.le_def] using hij),
      prism_δ_of_le i j (by simpa [Fin.le_def] using hij)]
    rfl
  h_succ_comp_δ_castSucc_succ {n} j := by
    rw [Fin.succ_castSucc]
    exact isPathFamily_pathH a b (n + 1) j
  h_castSucc_comp_δ_succ_of_lt {n} i j hji := by
    change _ = (pathSpace a b).map (SimplexCategory.δ i).op ≫ pathH a b n j
    rw [pathSpace_map_pathH, δ_apply_of_lt i j (by simpa [Fin.lt_def] using hji),
      prism_δ_of_lt i j (by simpa [Fin.lt_def] using hji)]
    rfl
  h_comp_σ_castSucc_of_le {n} i j hij := by
    change _ = (pathSpace a b).map (SimplexCategory.σ i).op ≫ pathH a b (n + 1) j.succ
    rw [pathSpace_map_pathH, σ_apply_succ_of_le i j (Fin.le_def.1 hij),
      prism_σ_of_le i j (Fin.le_def.1 hij)]
    rfl
  h_comp_σ_succ_of_lt {n} i j hji := by
    change _ = (pathSpace a b).map (SimplexCategory.σ i).op ≫ pathH a b (n + 1) j.castSucc
    rw [pathSpace_map_pathH, σ_apply_castSucc_of_ge i j (Fin.le_def.1 hji),
      prism_σ_of_ge i j (Fin.le_def.1 hji)]
    rfl

end CategoryTheory.SimplicialObject
