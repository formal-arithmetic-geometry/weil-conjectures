/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Sheaf.Paper.PQFCohomology

/-!
# The homogeneous action on graded cohomology

Source: Stacks Project, Cohomology of Schemes, Lemma 0897
(blueprint: lem-weil-pbc-graded-cohomology-module-structure).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry


/-- The homogeneous action induces the uniquely specified action on graded cohomology.

Source: Stacks Project, Cohomology of Schemes, Lemma 0897(1), the graded action in
its statement; this algebraic part does not require properness or finite generation.
(blueprint: lem-weil-pbc-graded-cohomology-module-structure).

Proof:
Write H_m = H^p(X, G_m). Applying the additive cohomology functor to mu gives
additive maps H_m -> H_(m+k), additive in b by hmu_add. Functoriality and hmu_mul
give the composition law, after transporting along the equalities of degrees.
For a = 1, hmu_scalar says sectionwise that mu m 0 (1) is the identity (with the
transport m+0=m). Thus its cohomology map is the identity.

Every b in B has a unique finite homogeneous decomposition, by hgrading. Define
b acting on a finite family (x_m) by summing the images H^p(mu m k b_k)(x_m)
in degree m+k. The sum is finite. Additivity in both arguments follows from
additivity of the homogeneous decomposition and the maps above. The unit law
uses hunit and the identity map just established. For the product law expand the
two finite sums; hmul places b_k c_l in degree k+l and hmu_mul identifies its
map with the composite. This constructs a Module B structure, with the asserted
formula on homogeneous generators. That formula also determines the action
uniquely: every scalar and every vector is a finite sum of such generators.
No geometric finiteness assertion is used in this construction.
-/
theorem gradedCohomologyModuleStructure
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (graded : ℕ → Submodule A B)
    (hgrading : DirectSum.IsInternal graded)
    (hunit : (1 : B) ∈ graded 0)
    (hmul : ∀ (k l : ℕ) {x y : B}, x ∈ graded k → y ∈ graded l → x * y ∈ graded (k + l))
    (hscalar : ∀ (a : A), algebraMap A B a ∈ graded 0)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (G : ℕ → SheafOfModules.{u} (moduleRings X.toRingedSpace))
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
    (p : ℕ) :
    ∃ mod : Module B (DirectSum ℕ (fun m => ((RingedSpace.moduleCohomology
      X.toRingedSpace p).obj (G m) : Type u))),
      ∀ (k m : ℕ) (b : graded k)
        (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m)),
        @SMul.smul B _ mod.toDistribMulAction.toMulAction.toSemigroupAction.toSMul b.val
          (DirectSum.of (fun n => ((RingedSpace.moduleCohomology
            X.toRingedSpace p).obj (G n) : Type u)) m x) =
        DirectSum.of (fun n => ((RingedSpace.moduleCohomology
          X.toRingedSpace p).obj (G n) : Type u)) (m + k)
          ((RingedSpace.moduleCohomology X.toRingedSpace p).map (mu m k b) x) := by
  sorry

end AlgebraicGeometry
