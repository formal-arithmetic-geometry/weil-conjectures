/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.RingTheory.Noetherian.Defs

import Sheaf.Algebra.Homology.SingleDegreeCoefficientConeCancellation
import Sheaf.RingTheory.PolynomialPresentationPseudoCoherence
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.ConePseudoCoherent
import WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent

/-! # Finite-window coefficient lifts of relatively pseudo-coherent affine complexes

Source: agent-formulated prerequisite for the unnumbered Kiehl assertion following
Stacks Tag 0CSD, perfect.tex, lemma-flat-proper-pseudo-coherent-direct-image-general.
The paragraph does not state this affine assertion; the primary Kiehl proof is WANTED.
(blueprint: lem-sfb-relative-affine-coefficient-window-lift).

As in the single-degree cancellation interface, universal derived base-change arrows
and their transpose equation specify the actual scalar-action composite. The cone bound
is tested on the canonical A-linear tensor and action map. Forgetting its cone to
D-modules gives the same complex as forgetting the stipulated R_D-linear cone.
Both restrictions are exact and faithful, so they detect precisely the same vanishing.
This does not assert an R_A-action on the derived tensor source.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

namespace ModuleCat

/-- Every upper cohomology window admits a bounded finite-cohomology coefficient lift.
Source: agent-formulated affine prerequisite for the Kiehl paragraph after Stacks Tag 0CSD,
perfect.tex, lemma-flat-proper-pseudo-coherent-direct-image-general.
(blueprint: lem-sfb-relative-affine-coefficient-window-lift).

Proof (the node's finite downward induction):
1. Choose a finite polynomial quotient Q_B -> R. Polynomial presentation invariance
(lem-sfb-polynomial-presentation-pseudocoherence-invariance) makes K pseudo-coherent
on Q_A. A bounded-above finite-free representative gives an upper cohomology bound b.
2. Start at n=b+1 with D=B, L=0 and gamma=0. The action map has cone K, hence no
cohomology in degrees at least n. Maintain the stated factorization, bounded finite
cohomology of L, and this upper cone bound. No transition between models is required.
3. Finite-type permanence (lem-weil-pbc-finite-type-algebra-noetherian) makes D and
Q_D Noetherian. Restriction of L has bounded finite cohomology over Q_D. The Noetherian
criterion (lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion) supplies a
bounded-above finite-free Q_D-model E. Its terms are D-free via the monomial basis;
lem-pc-module-bounded-flat-kflat makes E K-flat over D as well as Q_D. Thus its scalar
extension is pseudo-coherent over Q_A. Its action counit and the coefficient counit
both send a tensor a tensor k to ak. Their cones have the same underlying cohomology.
4. The Q_A-cone is pseudo-coherent by lem-pc-ring-pseudo-coherent-iff-all-m and
lem-sc-cone-pseudo-coherent. Its vanishing in degrees at least n and
lem-sc-finite-cohomology make its degree n-1 cohomology finite over Q_A.
5. Apply lem-sfb-single-degree-coefficient-cone-cancellation at n-1 with S=R_D and
Q_D -> R_D. It gives D', L', gamma' and the same normalized action composite with cone
zero in degrees at least n-1. Finite generating lists for D/B and D'/D combine to one
for D'/B. Identify the iterated scalar rings with R tensor_B D' and R tensor_B A.
6. If a <= b+1, iterate b+1-a times; otherwise keep the zero initial stage. The final
D, L and gamma have exactly the asserted properties. Universal base-change arrows
identify the tensor with its K-flat computation, and the transpose equation fixes
mu_K composed with 1 tensor gamma. Exact faithful forgetting detects cone cohomology
vanishing. No flatness, lower tensor bound or exact descent of K is used. -/
theorem relativeAffineCoefficientWindowLift
    (B A R : Type u) [CommRing B] [CommRing A] [CommRing R]
    [IsNoetherianRing B] [Algebra B A] [Algebra B R] [Algebra.FiniteType B R]
    (r : ℕ) (p : @AlgHom A (MvPolynomial (Fin r) A) (R ⊗[B] A)
      _ _ _ _ Algebra.TensorProduct.rightAlgebra)
    (hp : Function.Surjective p)
    (K : DerivedCategory (ModuleCat.{u} (R ⊗[B] A)))
    (hK : DerivedCategory.IsPseudoCoherent
      ((derivedRestrictScalars (@AlgHom.toRingHom A (MvPolynomial (Fin r) A)
        (R ⊗[B] A) _ _ _ _ Algebra.TensorProduct.rightAlgebra p)).obj K)) (a : ℤ) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra D A)
      (_ : IsScalarTower B D A),
      Algebra.FiniteType B D ∧
      ∃ (L : DerivedCategory (ModuleCat.{u} (R ⊗[B] D)))
        (γ : L ⟶ (derivedRestrictScalars
          (Algebra.TensorProduct.map (AlgHom.id B R)
            (IsScalarTower.toAlgHom B D A)).toRingHom).obj K),
        (∃ c b : ℤ, ∀ i : ℤ, i < c ∨ b < i → IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⊗[B] D)) i).obj L)) ∧
        (∀ i : ℤ, Module.Finite (R ⊗[B] D)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⊗[B] D)) i).obj L)) ∧
        ∃ (T : DerivedCategory (ModuleCat.{u} A))
          (η : (derivedRestrictScalars
              (Algebra.TensorProduct.includeRight : D →ₐ[B] R ⊗[B] D).toRingHom).obj L ⟶
            (derivedRestrictScalars (algebraMap D A)).obj T),
          IsDerivedBaseChange η ∧
          ∃ (θ : T ⟶ (derivedRestrictScalars
                (Algebra.TensorProduct.includeRight : A →ₐ[B] R ⊗[B] A).toRingHom).obj K)
            (C : DerivedCategory (ModuleCat.{u} A))
            (ι : (derivedRestrictScalars
                (Algebra.TensorProduct.includeRight : A →ₐ[B] R ⊗[B] A).toRingHom).obj K ⟶ C)
            (δ : C ⟶ T⟦(1 : ℤ)⟧),
            (η ≫ (derivedRestrictScalars (algebraMap D A)).map θ =
              (derivedRestrictScalars
                (Algebra.TensorProduct.includeRight : D →ₐ[B] R ⊗[B] D).toRingHom).map γ ≫
              (derivedRestrictScalarsCompIso
                  (f := (Algebra.TensorProduct.includeRight : D →ₐ[B] R ⊗[B] D).toRingHom)
                  (g := (Algebra.TensorProduct.map (AlgHom.id B R)
                    (IsScalarTower.toAlgHom B D A)).toRingHom) rfl ≪≫
                Functor.mapDerivedCategoryNatIso (restrictScalarsCongr
                  (congrArg AlgHom.toRingHom (Algebra.TensorProduct.map_comp_includeRight
                    (AlgHom.id B R) (IsScalarTower.toAlgHom B D A)))) ≪≫
                (derivedRestrictScalarsCompIso (f := algebraMap D A)
                  (g := (Algebra.TensorProduct.includeRight : A →ₐ[B] R ⊗[B] A).toRingHom)
                  rfl).symm).hom.app K) ∧
            Triangle.mk θ ι δ ∈ distTriang _ ∧
            ∀ i : ℤ, a ≤ i →
              IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj C) := by
  sorry

end ModuleCat
