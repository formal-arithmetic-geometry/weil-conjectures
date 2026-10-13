/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPolynomial.Basic

/-! # A bounded polynomial resolution from finite stalk Tor dimension

Source: Stacks Project, Tag 069C, proof of (3) implies (1), and Tags 068X and 068W.
(blueprint: lem-pc-affine-polynomial-resolution-of-stalkwise).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite polynomial presentation of an affine chart admits a bounded projective
resolution of its coordinate algebra over the polynomial ring.
Source: Stacks Project, Tag 069C, proof of (3) implies (1), using Tags 068X and 068W.

Proof: A = Γ(Y,U) is Noetherian. The polynomial ring P = A[x_1,...,x_n] is
Noetherian and the surjective presentation makes B = Γ(X,V) a finite P-module.
Thus B[0] is pseudo-coherent. For each prime q of P not containing the kernel,
B_q = 0. For a prime containing the kernel, its quotient corresponds to a point
of V. The affine stalk identifications and the compatibility of the presentation
with f identify B_q with that source stalk and the A-localization with the image
stalk. The assumption supplies a finite Tor bound there. The map A_p -> P_q is
flat, with fibres localizations of polynomial algebras over fields, of global
dimension at most n. Tag 068X makes B_q perfect over P_q. Tag 068W applies to the
bounded-below pseudo-coherent complex B[0], making B perfect over P. A finite
module concentrated in degree zero which is perfect has a finite projective
resolution: truncate a bounded projective representative above degree zero and
use exactness and projective splitting successively there. Reverse cochain degrees
to obtain a nonnegative projective resolution, with a natural bound d. For B = 0
use the zero projective resolution. No finite-dimensional hypothesis on A is used.
(blueprint: lem-pc-affine-polynomial-resolution-of-stalkwise). -/
theorem affinePolynomial_boundedResolution_of_stalkwise
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hperfect : HasStalkwiseFiniteTorDimension f)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (n : ℕ) (g : MvPolynomial (Fin n) Γ(Y, U) →+* Γ(X, V))
    (hg : Function.Surjective g)
    (hcomp : g.comp (MvPolynomial.C) = (f.appLE U V e).hom) :
    ∃ (d : ℕ) (P : ProjectiveResolution
        ((ModuleCat.restrictScalars g).obj (ModuleCat.of Γ(X, V) Γ(X, V)))),
      ∀ i : ℕ, d < i → IsZero (P.complex.X i) := by sorry

end AlgebraicGeometry
