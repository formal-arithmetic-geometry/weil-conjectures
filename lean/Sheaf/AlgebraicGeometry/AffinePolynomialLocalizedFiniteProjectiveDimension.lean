/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-! # Pointwise projective dimension from stalkwise finite Tor dimension

Source: Stacks Project, Tag 069C, using Tag 068X.
(blueprint: lem-pc-affine-polynomial-localized-finite-projective-dimension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Each prime localization of the coordinate algebra has finite projective dimension
as a module over the localized polynomial ring.
Source: Stacks Project, Tag 069C, proof of (3) implies (1), using Tag 068X.

Proof: Put A = Γ(Y,U), B = Γ(X,V), and R = A[t₁,...,tₙ]. The affine target
ring A is Noetherian, hence so is R by the Hilbert basis theorem. The surjection
R → B makes B finite over R, so B_q is pseudo-coherent over R_q. Fix a prime q.
If q does not contain ker(g), an element of the kernel becomes a unit and
annihilates B_q; it is zero and has projective dimension at most zero. Otherwise
q corresponds to a prime of B, hence to x in V. The affine stalk isomorphisms
identify B_q with O_{X,x} and A_p, for the contraction p of q, with O_{Y,f(x)}.
The compatibility equation on g makes the scalar actions agree with the stalk
map. The hypothesis therefore supplies a finite Tor bound over A_p. The map
A_p → R_q is flat, and its fibres are localizations of polynomial algebras in
n variables over fields, of global dimension at most n. Tag 068X now makes
B_q[0] perfect over R_q. Equivalently, a high syzygy in a finite free resolution
is flat; it is finitely presented by Noetherianity, hence projective. Truncating
at that syzygy gives a bounded projective resolution of B_q. Computing Ext
from it gives HasProjectiveDimensionLE at its length. The bound depends on q;
no uniform bound is asserted. The zero algebra and n = 0 are included.
(blueprint: lem-pc-affine-polynomial-localized-finite-projective-dimension). -/
theorem affinePolynomial_localized_finiteProjectiveDimension_of_stalkwise
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hperfect : HasStalkwiseFiniteTorDimension f)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (n : ℕ) (g : MvPolynomial (Fin n) Γ(Y, U) →+* Γ(X, V))
    (hg : Function.Surjective g)
    (hcomp : g.comp (MvPolynomial.C) = (f.appLE U V e).hom) :
    ∀ p : PrimeSpectrum (MvPolynomial (Fin n) Γ(Y, U)), ∃ d : ℕ,
      HasProjectiveDimensionLE
        (((ModuleCat.restrictScalars g).obj (ModuleCat.of Γ(X, V) Γ(X, V))).localizedModule
          p.asIdeal.primeCompl) d := by sorry

end AlgebraicGeometry
