module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-! # Free-module resolution of a set Cech nerve
Source: literature/stacks-project/hypercovering.tex, Tag 01GC (blueprint:
lem-weil-pbc-set-cech-nerve-free-resolution).
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicTopology

universe u v

variable {R : Type u} [Ring R] {A : Type v} {B : Type v} (f : A → B)

/-- The fibrewise Cech nerve in degree `n` of a map of sets.
Source: Stacks Project, Tag 01GC; (blueprint: lem-weil-pbc-set-cech-nerve-free-resolution). -/
def setCechNerve (f : A → B) (n : ℕ) : Type v :=
  {x : Fin (n + 1) → A // ∀ i, f (x i) = f (x 0)}

/-- The free `R`-module on the degree-`n` Cech nerve.
Source: Stacks Project, Tag 01GC; (blueprint: lem-weil-pbc-set-cech-nerve-free-resolution). -/
abbrev setCechNerveModule (R : Type u) [Ring R] (f : A → B) (n : ℕ) :
    Type (max u v) := setCechNerve f n →₀ R

/-- The face map deleting coordinate `j`.
Source: Stacks Project, Tag 01GC; (blueprint: lem-weil-pbc-set-cech-nerve-free-resolution). -/
def setCechFace (f : A → B) {n : ℕ} (j : Fin (n + 2)) :
    setCechNerve f (n + 1) → setCechNerve f n := by
  intro x
  let y : Fin (n + 1) → A := fun i => x.1 (Fin.succAbove j i)
  refine ⟨y, ?_⟩
  intro i
  have hi := x.2 (Fin.succAbove j i)
  have h0 := x.2 (Fin.succAbove j 0)
  simpa [y] using hi.trans h0.symm

/-- The alternating face differential on free modules of the Cech nerve.
Source: Stacks Project, Tag 01GC; (blueprint: lem-weil-pbc-set-cech-nerve-free-resolution). -/
noncomputable def setCechDifferential (R : Type u) [Ring R] (f : A → B) (n : ℕ) :
    setCechNerveModule R f (n + 1) →ₗ[R] setCechNerveModule R f n :=
  Finsupp.lift _ _ _ (fun x =>
    ∑ j : Fin (n + 2), ((-1 : R) ^ (j : ℕ)) •
      Finsupp.single (setCechFace f j x) (1 : R))

/-- The augmentation induced by `f` on free modules.
Source: Stacks Project, Tag 01GC; (blueprint: lem-weil-pbc-set-cech-nerve-free-resolution). -/
noncomputable def setCechAugmentation (R : Type u) [Ring R] (f : A → B) :
    setCechNerveModule R f 0 →ₗ[R] B →₀ R :=
  Finsupp.lift _ _ _ (fun x => Finsupp.single (f ((x : setCechNerve f 0).1 0)) (1 : R))

/-- The augmented free-module Cech nerve is a resolution of the free module on the target.
Source: Stacks Project, Tag 01GC and Tag 03AT
(blueprint: lem-weil-pbc-set-cech-nerve-free-resolution).
Proof: choose a section of the surjection and prefix it to tuples to obtain a contracting
homotopy; alternating-face terms cancel in pairs, yielding the chain identities and exactness.
-/
theorem setCechNerve_free_resolution
    (R : Type u) [Ring R] (f : A → B) (hsurj : Function.Surjective f) :
    (∀ n : ℕ, (setCechDifferential R f n).comp (setCechDifferential R f (n + 1)) = 0) ∧
    (setCechAugmentation R f).comp (setCechDifferential R f 0) = 0 ∧
    LinearMap.range (setCechAugmentation R f) = ⊤ ∧
    LinearMap.range (setCechDifferential R f 0) = LinearMap.ker (setCechAugmentation R f) ∧
    (∀ n : ℕ, LinearMap.range (setCechDifferential R f (n + 1)) =
      LinearMap.ker (setCechDifferential R f n)) := by
  sorry

end AlgebraicTopology
