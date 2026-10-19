/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.RingTheory.CompletedPolynomialConormal
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.Algebra.Module.LocalizedModule.Exact
import WeilConjectures.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent
import Mathlib.RingTheory.Kaehler.Polynomial
import Sheaf.RingTheory.PresentationsHomotopyEquivalent
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Shrinking a finite type model using its completed Jacobian

Source: Stacks Project, restricted.tex, Tag 0ALQ (2), with Tags 0AJU (3) and 0GAF
(blueprint: lem-per-jacobian-torsion-etale-shrink).

The étale conclusion is expressed on the affine cover indexed by `a ∈ I`: inverting
`g * algebraMap A C a` in C gives the inverse image of D(a) in Spec(C_g).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AlgebraicGeometry

/-- A power-torsion completed Jacobian permits shrinking by an element of `1 + IC`
so that the model is étale over the complement of V(I). The kernel and cokernel use
Mathlib's conormal module and the canonical continuous partial derivatives.

Source: Stacks Project, restricted.tex, Tag 0ALQ (2), using 0AJU (3) and 0GAF
(blueprint: lem-per-jacobian-torsion-etale-shrink).

Proof:
1. Choose a finite polynomial presentation of C. Finite-type Noetherianity and the
   Noetherian submodule theorem make the kernel and cokernel of its conormal
   differential finite C-modules. Their direct sum H is finite as well.
2. The completed-Jacobian homology comparison (Tags 0GAE and 0GAF, node
   lem-per-completed-jacobian-homology-comparison) identifies their completions with
   the displayed kernel and cokernel. Thus (IC)^c kills the completion of H.
3. Put L = IC and N = L^c H. Finite ideal generators give a surjection from a finite
   direct sum of H onto N. Exactness of completion makes the completed surjection
   followed by the completed inclusion into H injective on its image. Its composite
   is zero by step 2, so the completion of N is zero. Exact completion of
   0 → LN → N → N/LN → 0 gives zero completion of N/LN. Its positive quotient tower
   is constant because L kills it. Hence N/LN = 0 and LN = N.
4. Nakayama's one-plus-ideal annihilator theorem gives a common g with g - 1 ∈ L
   and gN = 0. In particular gL^c kills both ordinary homology modules.
5. For a ∈ I, localize at v = g*a. Both g and a become units, so the unit g*a^c
   kills both localized homology modules. Exactness of module localization shows
   that the localized conormal differential has zero kernel and cokernel.
6. Present C_v by adjoining the inverse of v to the finite polynomial presentation.
   The principal-localization naive-cotangent theorem splits its complex as the
   localized complex and the acyclic complex C_v → C_v with differential v.
   Polynomial Kähler bases identify its coordinate derivatives, and presentation
   homotopy invariance compares it with the canonical presentation (including its
   possibly infinite variable set). The conormal exact sequence identifies the
   cokernel with Kähler differentials. Thus H1Cotangent and differentials vanish.
   Adjoining an inverse to a finite presentation is still a finite presentation.
7. The affine étale criterion now gives the displayed étale ring map for every
   a ∈ I. These spectra cover the inverse image of Spec(A) minus V(I) in Spec(C_g):
   a prime lies in that inverse image exactly when it omits some a ∈ I. Consequently
   the affine-cover definition of étale gives the required geometric assertion.
-/
theorem jacobian_torsion_etale_shrink
    (A : Type u) (C : Type v) [CommRing A] [CommRing C] [Algebra A C]
    [IsNoetherianRing A] [Algebra.FiniteType A C]
    (I : Ideal A) (r : ℕ) (J : Ideal (rigPolynomialCompletion I r))
    (_e : (rigPolynomialCompletion I r ⧸ J) ≃ₐ[A]
      AdicCompletion (I.map (algebraMap A C)) C)
    (c : ℕ)
    (_hker : I ^ c ≤ Module.annihilator A (LinearMap.ker (rigJacobianDifferential r I J)))
    (_hcoker : I ^ c ≤ Module.annihilator A
      ((Fin r → (rigPolynomialCompletion I r ⧸ J)) ⧸
        LinearMap.range (rigJacobianDifferential r I J))) :
    ∃ g : C, g - 1 ∈ I.map (algebraMap A C) ∧
      ∀ a : A, a ∈ I →
        RingHom.Etale (algebraMap A (Localization.Away (g * algebraMap A C a))) := by
  sorry

end AlgebraicGeometry
