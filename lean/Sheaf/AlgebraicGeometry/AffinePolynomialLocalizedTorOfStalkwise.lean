/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-! Finite Tor dimension on primes containing the presentation kernel.
(blueprint: lem-pc-affine-polynomial-localized-tor-of-stalkwise)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finite Tor dimension over the affine base for a supported prime localization.
Source: Stacks Project, Tag 069C, proof of (3) implies (1).
Proof: Put A = Γ(Y,U), B = Γ(X,V), R = A[t₁,...,tₙ]. Surjectivity and ker(g) ⊆ p identify p with the
inverse image of a prime q of B. The affine correspondence for V gives a point x in V with prime q.
Let r be its image prime in A. The localization of B as an R-module at p is canonically B_q:
denominators outside p map outside q, and every B denominator outside q has a lift outside p by
surjectivity.

Affine germ maps identify B_q with O_{X,x} and A_r with O_{Y,f(x)}. The equation g.comp C = f.appLE
makes the section-to-germ square commute, so the A-action on the localized module is scalar
restriction of the actual stalkMap. Apply HasStalkwiseFiniteTorDimension at x to obtain a natural
bound d over A_r.

Localization A → A_r is flat. Finite Tor dimension gives an A_r-flat resolution of the source stalk
of length d, by dimension shifting and the Tor criterion for flatness. After scalar restriction this
is an A-flat resolution, since A_r is A-flat. For any A-module N, tensoring that resolution over A
agrees with tensoring it over A_r with A_r ⊗_A N. Its homology vanishes above d. The flat-resolution
computation of Tor and the compatible affine localization/stalk isomorphism give precisely the
stated Tor objects over A. No uniform bound in p is used.
The zero algebra has no prime containing the kernel of a surjection onto it. For n = 0,
the same localization and flat scalar-restriction argument applies.
(blueprint: lem-pc-affine-polynomial-localized-tor-of-stalkwise). -/
theorem affinePolynomial_localized_finiteTorDimension_of_stalkwise_of_kernel_le
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hperfect : HasStalkwiseFiniteTorDimension f)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (n : ℕ) (g : MvPolynomial (Fin n) Γ(Y, U) →+* Γ(X, V))
    (hg : Function.Surjective g)
    (hcomp : g.comp (MvPolynomial.C) = (f.appLE U V e).hom)
    (p : PrimeSpectrum (MvPolynomial (Fin n) Γ(Y, U)))
    (hker : RingHom.ker g ≤ p.asIdeal) :
    ∃ d : ℕ, ∀ N : ModuleCat.{u} Γ(Y, U), ∀ i : ℕ, d < i →
      IsZero (((Tor' (ModuleCat.{u} Γ(Y, U)) i).obj
        ((ModuleCat.restrictScalars
          ((algebraMap (MvPolynomial (Fin n) Γ(Y, U))
            (Localization p.asIdeal.primeCompl)).comp MvPolynomial.C)).obj
          (((ModuleCat.restrictScalars g).obj
            (ModuleCat.of Γ(X, V) Γ(X, V))).localizedModule
              p.asIdeal.primeCompl))).obj N) := by
  sorry

end AlgebraicGeometry
