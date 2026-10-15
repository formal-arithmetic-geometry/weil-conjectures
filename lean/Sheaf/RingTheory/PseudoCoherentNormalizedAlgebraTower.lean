/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.RingTheory.RingPseudoCoherent
public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Sheaf.RingTheory.PseudoCoherentNilpotentInvariance
import Sheaf.Algebra.Category.ModuleCat.RingScalarExtension
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Algebra.Homology.SurjectiveModuleComplexTowerLimit
import Sheaf.CategoryTheory.Triangulated.DerivedLimitMorphism
import Sheaf.RingTheory.NilpotentMarkedFreeComplexLift
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients

/-!
# Effectivity of a normalized algebra tower

Source: Stacks Project, More on Algebra, Tags 09AV and 066E,
lemma-Rlim-pseudo-coherent-gives-complete-pseudo-coherent and
lemma-Noetherian-pseudo-coherent
(blueprint: lem-weil-pbc-pseudocoherent-normalized-algebra-tower).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A normalized tower over an adically complete Noetherian ring is effective without a
perfectness assumption. Index `n` represents the positive level `n + 1`.

Normalization is written as the universal property of derived scalar extension: composing
with the supplied transition gives a bijection against every object over the quotient.
Likewise, `L n` is any left adjoint to exact derived restriction of scalars, hence is derived
scalar extension to `C / J^(n+1)`. The isomorphism `e n` is the adjunct of the given projection,
not an independently chosen isomorphism. The all-level equation gives compatibility with
transitions and their quotient cocycles. The last clause exhibits `E` itself as a derived
limit of its reductions, with transitions transported along these specified isomorphisms.

Source: Stacks Project, More on Algebra, Tags 09AV, 0CQF and 066E
(blueprint: lem-weil-pbc-pseudocoherent-normalized-algebra-tower).

Proof:
1. The quotient C/J is Noetherian. Apply the Noetherian cohomology criterion
   (lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion) to E_1 and choose a bounded
   above finite-free representative P_1 (def-pc-ring-pseudo-coherent-complex).
2. Each successive quotient has square-zero kernel. Pseudo-coherence lifts by
   lem-weil-pbc-pseudo-coherent-nilpotent-invariance. Inductively use
   lem-weil-pbc-nilpotent-marked-free-complex-lift to lift P_n with its specified marking,
   keeping the same upper bound. The marking equation identifies the chain transitions
   with the supplied derived transitions.
3. Lift bases degree by degree. A map between free modules invertible modulo a square-zero
   ideal is invertible: lift the inverse and invert the error matrices by 1 minus the error.
   In these bases the transitions are coordinatewise reduction. Adic completeness identifies
   their termwise limit P with a bounded-above complex of finite free C-modules, whose
   reductions are the P_n, with their projection maps.
4. Apply lem-weil-pbc-surjective-module-complex-tower-limit to P_n. The markings give a
   levelwise tower isomorphism. Lemmas lem-weil-derived-limit-morphism and
   lem-weil-derived-limit-levelwise-iso identify Q(P) with the specified E respecting
   projections. Thus E is pseudo-coherent.
5. Free terms are flat and P is K-flat by lem-pc-kflat-closure, on the one-object site.
   Lemma lem-pur-derived-change-of-rings computes its reductions termwise. The ordinary
   scalar-extension adjunction (def-pod-ring-scalar-extension), exact derived restriction
   (lem-weil-pbc-exact-functor-derived-functor), and the canonical derived adjunction
   (lem-pc-pre-derived-adjoint-functors-general) identify these isomorphisms with the
   adjuncts of the given projections.
6. Chain projections satisfy every quotient cocycle. Passing to the derived category and
   through the markings gives the all-level equation. The reductions and original tower
   are isomorphic; transport its Roos triangle by lem-weil-derived-limit-morphism and
   lem-weil-derived-limit-levelwise-iso. This proves derived completeness. -/
theorem pseudoCoherent_normalizedAlgebraTower
    {C : Type u} [CommRing C] [IsNoetherianRing C]
    (J : Ideal C) [IsAdicComplete J C]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} C)]
    [∀ n : ℕ, HasDerivedCategory.{w} (ModuleCat.{max u v} (C ⧸ J ^ (n + 1)))]
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (C ⧸ J ^ (n + 1))))
    (t : ∀ n : ℕ, K (n + 1) ⟶
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))).mapDerivedCategory.obj (K n))
    (hnorm : ∀ (n : ℕ) (N : DerivedCategory (ModuleCat.{max u v} (C ⧸ J ^ (n + 1)))),
      Function.Bijective (fun a : K n ⟶ N ↦ t n ≫
        (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))).mapDerivedCategory.map a))
    (f : ∀ n : ℕ,
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (J ^ (n + 2)))).mapDerivedCategory.obj
        (K (n + 1)) ⟶
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.obj
        (K n))
    (hf : ∀ n : ℕ, f n =
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (J ^ (n + 2)))).mapDerivedCategory.map
        (t n) ≫
      (Functor.mapDerivedCategoryCompIso
        (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1)))))
        (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (J ^ (n + 2))))).inv.app (K n) ≫
      (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp'.{max u v}
        (Ideal.Quotient.mk (J ^ (n + 2)))
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))
        (Ideal.Quotient.mk (J ^ (n + 1)))
        (Ideal.Quotient.factor_comp_mk _).symm)).inv.app (K n))
    [HasProduct (fun n : ℕ ↦
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.obj
        (K n))]
    (E : DerivedCategory (ModuleCat.{max u v} C))
    (p : E ⟶ ∏ᶜ (fun n : ℕ ↦
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.obj
        (K n)))
    (δ : (∏ᶜ (fun n : ℕ ↦
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.obj
        (K n))) ⟶ E⟦(1 : ℤ)⟧)
    (hE : IsDerivedLimitTriangle f E p δ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((homologyFunctor (ModuleCat.{max u v} (C ⧸ J ^ (0 + 1))) i).obj (K 0)))
    (hfinite : ∀ i : ℤ, Module.Finite (C ⧸ J ^ (0 + 1))
      ((homologyFunctor (ModuleCat.{max u v} (C ⧸ J ^ (0 + 1))) i).obj (K 0))) :
    IsPseudoCoherent E ∧
      ∀ (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} C) ⥤
          DerivedCategory (ModuleCat.{max u v} (C ⧸ J ^ (n + 1))))
        (adj : ∀ n : ℕ, L n ⊣
          (ModuleCat.restrictScalars.{max u v}
            (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory),
      ∃ e : ∀ n : ℕ, (L n).obj E ≅ K n,
        (∀ n : ℕ, (e n).hom = ((adj n).homEquiv E (K n)).symm (p ≫ Pi.π _ n)) ∧
        (∀ (m n : ℕ) (h : n ≤ m),
          (adj m).unit.app E ≫
            (ModuleCat.restrictScalars.{max u v}
              (Ideal.Quotient.mk (J ^ (m + 1)))).mapDerivedCategory.map
              (e m).hom ≫
            (Functor.ofOpSequence (X := fun k : ℕ ↦
              (ModuleCat.restrictScalars.{max u v}
                (Ideal.Quotient.mk (J ^ (k + 1)))).mapDerivedCategory.obj (K k))
              f).map (homOfLE h).op =
          (adj n).unit.app E ≫
            (ModuleCat.restrictScalars.{max u v}
              (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.map
              (e n).hom) ∧
        HasProduct (fun n : ℕ ↦
          (ModuleCat.restrictScalars.{max u v}
            (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.obj
            ((L n).obj E)) ∧
        (∀ [HasProduct (fun n : ℕ ↦
          (ModuleCat.restrictScalars.{max u v}
            (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.obj
            ((L n).obj E))],
          IsDerivedLimit (fun n : ℕ ↦
            (ModuleCat.restrictScalars.{max u v}
              (Ideal.Quotient.mk (J ^ (n + 2)))).mapDerivedCategory.map
              (e (n + 1)).hom ≫ f n ≫
            (ModuleCat.restrictScalars.{max u v}
              (Ideal.Quotient.mk (J ^ (n + 1)))).mapDerivedCategory.map
              (e n).inv) E) := by
  sorry

end DerivedCategory
