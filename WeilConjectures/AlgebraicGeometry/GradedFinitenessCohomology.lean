/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.GradedCohomologyModuleStructure
import WeilConjectures.AlgebraicGeometry.GradedCohomologyModuleFinite

/-!
# Cohomology of a finite type graded module

## References

* [Stacks Project, Cohomology of Schemes, Tag 0897]
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry

/-- Cohomology of a finite type graded module over `f ^* B~` is finite over `B`, with the
graded module action written through the homogeneous maps. (Stacks, Tag 0897) -/
theorem gradedFinitenessCohomology
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (graded : ℕ → Submodule A B)
    (hgrading : DirectSum.IsInternal graded)
    (hunit : (1 : B) ∈ graded 0)
    (hmul : ∀ (k l : ℕ) {x y : B}, x ∈ graded k → y ∈ graded l → x * y ∈ graded (k + l))
    (hscalar : ∀ (a : A), algebraMap A B a ∈ graded 0)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (G : ℕ → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hG : ∀ m : ℕ, (G m).IsQuasicoherent)
    (mu : ∀ (m k : ℕ), graded k → (G m ⟶ G (m + k)))
    (hmu_add : ∀ (m k : ℕ) (b b' : graded k),
      mu m k (b + b') = mu m k b + mu m k b')
    (hmu_mul : ∀ (m k l : ℕ) (b : graded k) (b' : graded l),
      HEq (mu m l b' ≫ mu (m + l) k b)
        (mu m (k + l) ⟨b.val * b'.val, hmul k l b.property b'.property⟩))
    (hmu_scalar : ∀ (m : ℕ) (a : A) (U : X.Opens)
      (t : (G m).val.obj (op U)),
      HEq ((mu m 0 ⟨algebraMap A B a, hscalar a⟩).val.app (op U) t)
        ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) • t))
    (hfinite : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      ∃ (r : ℕ) (d : Fin r → ℕ) (s : ∀ i : Fin r, (G (d i)).val.obj (op U)),
        ∀ (m : ℕ) (V : X.Opens) (hVU : V ≤ U) (t : (G m).val.obj (op V))
          (y : X), y ∈ V → ∃ (W : X.Opens) (hWV : W ≤ V), y ∈ W ∧
            (G m).val.map (homOfLE hWV).op t ∈
              Submodule.span ((moduleRings X.toRingedSpace).obj.obj (op W))
                {z | ∃ (i : Fin r), d i ≤ m ∧
                  ∃ b : graded (m - d i),
                    HEq z ((mu (d i) (m - d i) b).val.app (op W)
                      ((G (d i)).val.map (homOfLE (hWV.trans hVU)).op (s i)))})
    (p : ℕ) :
    ∃ mod : Module B (DirectSum ℕ (fun m => ((RingedSpace.moduleCohomology
      X.toRingedSpace p).obj (G m) : Type u))),
      @Module.Finite B _ _ _ mod ∧
      ∀ (k m : ℕ) (b : graded k)
        (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m)),
        @SMul.smul B _ mod.toDistribMulAction.toMulAction.toSemigroupAction.toSMul b.val
          (DirectSum.of (fun n => ((RingedSpace.moduleCohomology
            X.toRingedSpace p).obj (G n) : Type u)) m x) =
        DirectSum.of (fun n => ((RingedSpace.moduleCohomology
          X.toRingedSpace p).obj (G n) : Type u)) (m + k)
          ((RingedSpace.moduleCohomology X.toRingedSpace p).map (mu m k b) x) := by
  obtain ⟨mod, hact⟩ := gradedCohomologyModuleStructure
    graded hgrading hunit hmul hscalar f G mu hmu_add hmu_mul hmu_scalar p
  exact ⟨mod, gradedCohomologyModuleFinite
    graded hgrading hunit hmul hscalar f G hG mu hmu_add hmu_mul hmu_scalar hfinite p
    mod hact, hact⟩

end AlgebraicGeometry
