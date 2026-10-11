/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.Ample
import Sheaf.Paper.PQFCohomology

/-! # Serre vanishing for finite graded modules

Source: Stacks Project, Cohomology of Schemes, Lemma 0897 (2)
(blueprint: lem-weil-pbc-formal-systems-graded-vanishing).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry

/-- A finite type graded quasi-coherent module over a pulled-back finite type graded
algebra has uniformly vanishing higher cohomology after sufficiently large ample twists.
The graded module `G = ⊕ G m` over `f ^* B~` is written, as in
`gradedFinitenessCohomology` (Lemma 0897 (1)), through its homogeneous pieces and the
homogeneous action maps `mu`; finite type allows generators in arbitrary degrees `d i`.
No equality between the degree-zero algebra and the base ring, and no degree-one
algebra generators, are assumed.
Source: Stacks Project, Cohomology of Schemes, Lemma 0897 (2)
(blueprint: lem-weil-pbc-formal-systems-graded-vanishing).

Proof:
1. Forget the grading. Set X' = Spec(B) ×_Spec(A) X. Its projection pi to X is affine
   by lem-weil-pbc-morphism-affine-schemes-affine and
   lem-weil-pbc-affine-morphism-permanence; its map to Spec(B) is proper by
   lem-weil-pbc-proper-fp-permanence. B and X' are Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian and lem-weil-pbc-finite-type-over-noetherian.
2. The associated algebra and tensor pullback identify X' with the relative spectrum
   (lem-weil-pbc-affine-morphism-relative-spec). The affine module correspondence
   (lem-weil-pbc-affine-module-correspondence) realizes G as pi_* G'. Local finite
   generation is preserved (lem-weil-pbc-affine-module-finite-type), so G' is coherent
   by pqf-lem-coherent-ft-locnoeth.
3. The pullback L' = pi^* L is ample by lem-weil-pbc-pullback-ample-invertible.
   Apply lem-weil-pbc-coherent-serre-vanishing on X' to obtain one bound d0 for all p > 0.
4. Trivialize L locally. Both pi_*(G' tensor pi^* L^d) and G tensor L^d identify with
   pi_* G'. Changing the local generator by a unit a changes both identifications by
   a^d, so they glue. The same computation identifies (pi^* L)^d with pi^*(L^d).
5. The twisted module upstairs is quasi-coherent since locally it is G'. The affine
   cohomology comparison lem-weil-pbc-affine-morphism-cohomology-edge identifies its
   cohomology with the cohomology downstairs. Step 3 gives the required vanishing. -/
theorem graded_serre_vanishing
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (graded : ℕ → Submodule A B)
    (hgrading : DirectSum.IsInternal graded)
    (hunit : (1 : B) ∈ graded 0)
    (hmul : ∀ (k l : ℕ) {x y : B}, x ∈ graded k → y ∈ graded l → x * y ∈ graded (k + l))
    (hscalar : ∀ (a : A), algebraMap A B a ∈ graded 0)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (G : ℕ → X.Modules)
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
    (L : X.Modules) [L.IsInvertible] (hL : Scheme.Modules.IsAmple X L) :
    ∃ d₀ : ℕ, ∀ (p d : ℕ), 0 < p → d₀ ≤ d →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj
        (Scheme.Modules.tensorObj (∐ G) (L.tensorPow d))) := by
  sorry

end AlgebraicGeometry
