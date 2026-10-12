/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Artinian.Module
import Sheaf.AlgebraicGeometry.SmoothAtPrimeArtinianLifting

/-!
# Artinian lifting criterion for smoothness at a point

Source: Stacks Project, More on Morphisms, Lemma 02HX, (1) iff (3), and Algebra,
Definition 02HS (blueprint: lem-weil-pbc-smooth-artinian-lifting-at-point).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, More on Morphisms, Lemma 02HX, (1) iff (3), with small
extensions as in Algebra, Definition 02HS
(blueprint: lem-weil-pbc-smooth-artinian-lifting-at-point).

A locally finite type morphism over a locally Noetherian scheme is smooth on a
neighbourhood of `x` iff every compatible diagram at `x` lifts along each surjection
of Artinian local rings whose kernel has module length one. The consequences
that the kernel is a residue-field module and is square zero are not extra hypotheses.

Proof, following the five steps of the DAG node:
1. Choose affine neighbourhoods `V = Spec R` of `f(x)` and `U = Spec A` of `x`
   with `f(U)` contained in `V`. Local Noetherianity (pqf-def-locnoeth) makes `R`
   Noetherian, and local finite type (def-weil-finite-type-morphism) makes `A`
   finite type over `R`. Factor the restriction through `V`
   (lem-weil-pbc-morphism-factors-through-open-subscheme).
2. Both test spectra have a unique point
   (lem-weil-pbc-artinian-local-unique-prime), so the test maps factor through `U`
   and `V`. The affine spectrum correspondence (def-weil-affine-spectrum)
   identifies their commutative square with a commutative square of ring maps,
   with the maximal ideal pulling back to the prime corresponding to `x`.
   Cancel the open inclusion using lem-weil-pbc-open-immersion-monomorphism.
3. A lift also has image `x`, so it factors through `U`. The same correspondence
   and cancellation identify scheme lifts with ring lifts, giving exactly the
   test condition of lem-weil-pbc-smooth-at-prime-artinian-lifting.
4. Restriction to open subschemes, composition with their inclusions, and
   invariance under isomorphism (lem-weil-pbc-smooth-restrict-open-subschemes)
   identify smoothness on a neighbourhood of `x` with smoothness on a
   neighbourhood of the corresponding prime of `A`.
5. Apply lem-weil-pbc-smooth-at-prime-artinian-lifting to the Noetherian ring `R`
   and finite type `R`-algebra `A`; steps 2--4 identify both sides of its equivalence.
-/
theorem smooth_near_iff_artinian_lifting_at_point
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (x : X) :
    (∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) ↔
      ∀ (B' B : Type u) [CommRing B'] [CommRing B]
        [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
        (φ : B' →+* B),
        Function.Surjective φ → Module.length B' ↥(RingHom.ker φ) = 1 →
        ∀ (α : Spec (CommRingCat.of B) ⟶ X)
          (β : Spec (CommRingCat.of B') ⟶ S),
          α ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ β →
          α (IsLocalRing.closedPoint B) = x →
          ∃ γ : Spec (CommRingCat.of B') ⟶ X,
            Spec.map (CommRingCat.ofHom φ) ≫ γ = α ∧ γ ≫ f = β := by
  sorry

end AlgebraicGeometry
