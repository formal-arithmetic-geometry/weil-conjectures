/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import Sheaf.AlgebraicGeometry.ProjectiveSpaceTiltingEquivalence
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.PerfectRHomTensorComparison
import Sheaf.RingTheory.FiniteFreeAlgebraPseudoCoherentResolution
import Sheaf.CategoryTheory.DerivedCategory.BoundedAboveAcyclicComputation

/-! # Finite twist tests for pseudo-coherence on projective space

Source: Stacks Project, perfect.tex, Tag 0CSG, lemma-pseudo-coherent-on-projective-space,
implication (5) to (1) (blueprint: lem-sfb-projective-space-pseudocoherence-twist-test).

The model of projective space and its twists is the one of def-pc-projective-space-twist.
Derived global sections is the shared functor, followed by exact restriction of scalars
along the structural map R -> Γ(P, O_P), so the tests take values in D(R).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wR wG

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.ProjectiveSpace

/-- A quasi-coherent derived object on projective N-space is pseudo-coherent if the
R-complexes of derived sections of its twists O(d), for 0 <= d <= N, are pseudo-coherent.
No boundedness of K or Noetherian hypothesis on R is imposed.

Source: Stacks Project, perfect.tex, Tag 0CSG, implication (5) to (1)
(blueprint: lem-sfb-projective-space-pseudocoherence-twist-test).

Proof, following the accepted split:
1. Put T = O ⊕ O(-1) ⊕ ... ⊕ O(-N) and B = End(T). The unbounded equivalence of
   lem-sfb-projective-space-tilting-equivalence gives a right B-derived object M with
   M tensor^L_B T isomorphic to K and its R-restriction isomorphic to RHom(T,K).
2. On each standard chart the twists are free of rank one, so T is perfect
   (def-pc-perfect-complex) and its dual is the sum of O(d), 0 <= d <= N. The twist
   pairings multiply the local bases to 1, and inverse transition factors cancel.
   By lem-pc-perfect-rhom-tensor-comparison and def-pc-global-derived-rhom,
   RHom(T,K) is the finite sum of RΓ(K tensor^L O(d)). Tensor and derived sections
   preserve finite biproducts: their inclusions and projections retain the biproduct
   identities after derivation, since finite sums of resolving complexes resolve.
3. By def-pc-ring-pseudo-coherent-complex choose bounded-above finite-free R-models
   of the finitely many tests. Their termwise finite sum is finite free, bounded above
   by the maximum of their upper bounds, and represents the biproduct. Hence the
   underlying R-derived object of M is pseudo-coherent.
4. The matrix blocks of B are homogeneous polynomial pieces of degrees j-i. Each
   is finite free over R on the monomials of that degree; there are finitely many
   blocks. Thus B is finite free over R, also for N=0. Apply
   lem-sfb-finite-free-algebra-pseudocoherent-resolution to obtain a bounded-above
   finite-free right B-complex F representing M.
5. Balanced tensor V(L) = L tensor_B T is additive and right exact (a cokernel
   followed by exact sheafification). Its total left derived functor exists by the
   tilting node. Right B-modules have enough projectives: free modules surject onto
   them, and basis maps lift across surjections. Therefore
   lem-trf-bounded-above-acyclic-derived-computation computes K by F tensor_B T.
   Each term is a finite sum of T, by (b_a) tensor t |-> (b_a t). On each standard
   chart it is free of rank (N+1) times the rank of F in that degree, with the same
   upper bound as F. These local models give def-pur-pseudo-coherent-complex. -/
theorem isPseudoCoherent_of_twist_derivedGlobalSections
    (R : Type u) [CommRing R] (N : ℕ)
    [HasDerivedCategory.{wX} (SheafOfModules.{u}
      (moduleRings (ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of R))).toRingedSpace))]
    [∀ U : (ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of R))).Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u}
        ((moduleRings
          (ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of R))).toRingedSpace).over U))]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wG} (ModuleCat.{u}
      ((moduleRings (ProjectiveSpace (ULift.{u} (Fin (N + 1)))
        (Spec (.of R))).toRingedSpace).obj.obj (op ⊤)))]
    (K : schemeDerivedQCohCategory
      (ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of R))))
    (hK : ∀ d : Fin (N + 1), DerivedCategory.IsPseudoCoherent
      ((Functor.mapDerivedCategory.{wG, wR} (ModuleCat.restrictScalars.{u}
          (S := (moduleRings (ProjectiveSpace (ULift.{u} (Fin (N + 1)))
            (Spec (.of R))).toRingedSpace).obj.obj (op ⊤))
          (((Scheme.ΓSpecIso (.of R)).inv ≫
            ((ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of R))) ↘
              Spec (.of R)).appTop).hom))).obj
        ((schemeDerivedGlobalSections
          (ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of R)))).obj
          (K.obj ⊗ (DerivedCategory.singleFunctor (SheafOfModules.{u}
            (moduleRings (ProjectiveSpace (ULift.{u} (Fin (N + 1)))
              (Spec (.of R))).toRingedSpace)) 0).obj
            (twist (ULift.{u} (Fin (N + 1))) (Spec (.of R)) (d.val : ℤ)))))) :
    Scheme.IsPseudoCoherent
      (ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of R))) K.obj := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
