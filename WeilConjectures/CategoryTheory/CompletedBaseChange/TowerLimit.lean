/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit

/-!
# Sequential derived limit formalisms

A *sequential derived limit formalism* `𝔉 : TowerLimitFormalism 𝒯 T` abstracts the derived
category of towers `𝒯 = D(Tow_A(T))` over a triangulated category `T = D(T_proét, A)`
(`def-weil-pbc-adic-coefficient-datum`, `def-weil-pbc-derived-inverse-limit`):

* a functor `tower : 𝒯 ⥤ (ℕᵒᵖ ⥤ T)` sending a derived tower `M_•` to its underlying system of
  evaluations `(ev_n M_•)_n` with their transition maps;
* a derived limit functor `rlim : 𝒯 ⥤ T` with projections `π_n : rlim M ⟶ ev_n M`, natural in
  `M` and compatible with the transitions;
* the *Roos* (Milnor) property: for every `M` the projections exhibit `rlim M` as the homotopy
  limit of `tower M` (`CategoryTheory.Pretriangulated.IsHomotopyLimit`);
* joint conservativity of the evaluations: a morphism of derived towers which is an
  isomorphism at every level is an isomorphism.

On such a formalism a morphism of derived towers has a well defined limit `rlim.map f`, which
makes the passage of finite-level identities to the limit rigorous; this is how the
rectangle of the proper base change chain passes to the derived limit
(`lemma-weil-pbc-level-map-derived-limit`, `lem-weil-pbc-rectangle-derived-limit`).

## Main definitions

- `CategoryTheory.TowerLimitFormalism`, with `ev n : 𝒯 ⥤ T`, `cone M` and `proj n`.

## Main results

- `CategoryTheory.TowerLimitFormalism.isIso_rlim_map_of_forall_isIso`: a levelwise
  isomorphism of derived towers induces an isomorphism on derived limits.
- `CategoryTheory.TowerLimitFormalism.map_tower_comm`: morphisms of derived towers are maps of
  towers (`lemma-weil-pbc-level-map-tower-compatibility`, `lem-weil-pbc-tower-compatibility`).
- `CategoryTheory.TowerLimitFormalism.rlim_rectangle`: a commutative rectangle of derived towers
  passes to the derived limit, with the expected components.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits Opposite

namespace CategoryTheory

/-- A *sequential derived limit formalism* (Blueprint `def-weil-pbc-derived-inverse-limit`,
abstract form): a category `𝒯` of derived towers over a pretriangulated category `T`, with
the underlying-tower functor `tower : 𝒯 ⥤ (ℕᵒᵖ ⥤ T)`, a derived limit functor `rlim : 𝒯 ⥤ T`
and natural projections `π : rlim ⟶ tower` which exhibit `rlim M` as the homotopy limit of the
tower `tower M` (Roos triangle), the evaluations being jointly conservative. -/
structure TowerLimitFormalism (𝒯 : Type u₁) [Category.{v₁} 𝒯] (T : Type u₂) [Category.{v₂} T]
    [HasZeroObject T] [HasShift T ℤ] [Preadditive T] [∀ n : ℤ, (shiftFunctor T n).Additive]
    [Pretriangulated T] where
  /-- The underlying tower `(ev_n M)_n` of a derived tower `M`. -/
  tower : 𝒯 ⥤ ℕᵒᵖ ⥤ T
  /-- The derived limit `R lim`. -/
  rlim : 𝒯 ⥤ T
  /-- The projections `R lim M ⟶ ev_n M`. -/
  π : rlim ⋙ Functor.const ℕᵒᵖ ⟶ tower
  /-- The projections exhibit `R lim M` as the homotopy limit of the tower of `M`. -/
  isHomotopyLimit (M : 𝒯) : Pretriangulated.IsHomotopyLimit (Cone.mk _ (π.app M))
  /-- The evaluations are jointly conservative. -/
  isIso_of_forall_isIso {M N : 𝒯} (f : M ⟶ N) :
    (∀ n : ℕ, IsIso ((tower.map f).app (op n))) → IsIso f

namespace TowerLimitFormalism

variable {𝒯 : Type u₁} [Category.{v₁} 𝒯] {T : Type u₂} [Category.{v₂} T]
  [HasZeroObject T] [HasShift T ℤ] [Preadditive T] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] (𝔉 : TowerLimitFormalism 𝒯 T)

/-- The evaluation `ev_n : 𝒯 ⥤ T` at level `n`. -/
def ev (n : ℕ) : 𝒯 ⥤ T := 𝔉.tower ⋙ (evaluation ℕᵒᵖ T).obj (op n)

@[simp]
lemma ev_obj (n : ℕ) (M : 𝒯) : (𝔉.ev n).obj M = (𝔉.tower.obj M).obj (op n) := rfl

@[simp]
lemma ev_map (n : ℕ) {M N : 𝒯} (f : M ⟶ N) : (𝔉.ev n).map f = (𝔉.tower.map f).app (op n) :=
  rfl

/-- The transition `ev_{n+1} ⟶ ev_n`. -/
def transition (n : ℕ) : 𝔉.ev (n + 1) ⟶ 𝔉.ev n :=
  Functor.whiskerLeft 𝔉.tower ((evaluation ℕᵒᵖ T).map (homOfLE n.le_succ).op)

@[simp]
lemma transition_app (n : ℕ) (M : 𝒯) :
    (𝔉.transition n).app M = (𝔉.tower.obj M).map (homOfLE n.le_succ).op := rfl

/-- The projection `π_n : R lim ⟶ ev_n`. -/
def proj (n : ℕ) : 𝔉.rlim ⟶ 𝔉.ev n where
  app M := (𝔉.π.app M).app (op n)
  naturality M N f := by
    have := congr_arg (fun φ ↦ φ.app (op n)) (𝔉.π.naturality f)
    simpa using this

/-- The homotopy limit cone `R lim M ⟶ ev_n M` of a derived tower. -/
def cone (M : 𝒯) : Cone (𝔉.tower.obj M) := Cone.mk _ (𝔉.π.app M)

@[simp]
lemma cone_π_app (M : 𝒯) (n : ℕ) : (𝔉.cone M).π.app (op n) = (𝔉.proj n).app M := rfl

lemma isHomotopyLimit_cone (M : 𝒯) : Pretriangulated.IsHomotopyLimit (𝔉.cone M) :=
  𝔉.isHomotopyLimit M

/-- The projections are compatible with the transitions. -/
@[reassoc (attr := simp)]
lemma proj_comp_transition (n : ℕ) (M : 𝒯) :
    (𝔉.proj (n + 1)).app M ≫ (𝔉.transition n).app M = (𝔉.proj n).app M := by
  simpa [proj] using ((𝔉.π.app M).naturality (homOfLE n.le_succ).op).symm

/-- The projections are natural in the derived tower. -/
@[reassoc]
lemma rlim_map_comp_proj (n : ℕ) {M N : 𝒯} (f : M ⟶ N) :
    𝔉.rlim.map f ≫ (𝔉.proj n).app N = (𝔉.proj n).app M ≫ (𝔉.ev n).map f :=
  (𝔉.proj n).naturality f

/-- **Morphisms of derived towers are maps of towers** (Blueprint
`lemma-weil-pbc-level-map-tower-compatibility`, `lem-weil-pbc-tower-compatibility`, abstract
form): for `f : M ⟶ N` in the derived tower category, the evaluations
`f_n = ev_n f` commute with the transitions, `t_{n+1,n} ∘ f_{n+1} = f_n ∘ t_{n+1,n}`. -/
@[reassoc]
lemma map_tower_comm (n : ℕ) {M N : 𝒯} (f : M ⟶ N) :
    (𝔉.transition n).app M ≫ (𝔉.ev n).map f = (𝔉.ev (n + 1)).map f ≫ (𝔉.transition n).app N :=
  ((𝔉.transition n).naturality f).symm

/-- A morphism of derived towers which is an isomorphism at every level is an isomorphism. -/
lemma isIso_of_forall_isIso_ev {M N : 𝒯} (f : M ⟶ N) (hf : ∀ n, IsIso ((𝔉.ev n).map f)) :
    IsIso f :=
  𝔉.isIso_of_forall_isIso f hf

/-- **Limits preserve levelwise isomorphisms**: a morphism of derived towers which is an
isomorphism at every level induces an isomorphism on derived limits. -/
lemma isIso_rlim_map_of_forall_isIso {M N : 𝒯} (f : M ⟶ N)
    (hf : ∀ n, IsIso ((𝔉.ev n).map f)) : IsIso (𝔉.rlim.map f) := by
  have := 𝔉.isIso_of_forall_isIso_ev f hf
  infer_instance

/-- **The rectangle passes to the derived limit** (Blueprint
`lemma-weil-pbc-level-map-derived-limit`, `lem-weil-pbc-rectangle-derived-limit`, abstract
form): if a square `h ≫ v' = v ≫ h'` of derived towers commutes, then so does the square of
derived limits `H ≫ V' = V ≫ H'` with `H = R lim h` etc., and the `n`-th components of both
composites are `π_n ≫ h_n ≫ v'_n = π_n ≫ v_n ≫ h'_n`. -/
theorem rlim_rectangle {A B C D : 𝒯} {h : A ⟶ B} {v : A ⟶ C} {h' : C ⟶ D} {v' : B ⟶ D}
    (w : h ≫ v' = v ≫ h') :
    𝔉.rlim.map h ≫ 𝔉.rlim.map v' = 𝔉.rlim.map v ≫ 𝔉.rlim.map h' ∧
    ∀ n : ℕ,
      (𝔉.rlim.map h ≫ 𝔉.rlim.map v') ≫ (𝔉.proj n).app D =
        (𝔉.proj n).app A ≫ (𝔉.ev n).map h ≫ (𝔉.ev n).map v' ∧
      (𝔉.rlim.map v ≫ 𝔉.rlim.map h') ≫ (𝔉.proj n).app D =
        (𝔉.proj n).app A ≫ (𝔉.ev n).map v ≫ (𝔉.ev n).map h' := by
  refine ⟨by rw [← Functor.map_comp, w, Functor.map_comp], fun n ↦ ⟨?_, ?_⟩⟩ <;>
    rw [Category.assoc, rlim_map_comp_proj, rlim_map_comp_proj_assoc]

/-- The level `n` equality `h_n ≫ v'_n = v_n ≫ h'_n` of a commutative rectangle of derived
towers. -/
lemma ev_rectangle {A B C D : 𝒯} {h : A ⟶ B} {v : A ⟶ C} {h' : C ⟶ D} {v' : B ⟶ D}
    (w : h ≫ v' = v ≫ h') (n : ℕ) :
    (𝔉.ev n).map h ≫ (𝔉.ev n).map v' = (𝔉.ev n).map v ≫ (𝔉.ev n).map h' := by
  rw [← Functor.map_comp, w, Functor.map_comp]

end TowerLimitFormalism

end CategoryTheory
