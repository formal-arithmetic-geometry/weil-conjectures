/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.RingTheory.Noetherian.Defs

/-! # Finite cohomology of a single projective twist over an affine base

Source: Stacks Project, Tag 01XT, Lemma 30.8.1.
(blueprint: lem-pc-m4-projective-twist-finite-cohomology)
-/

@[expose] public section

universe u
open CategoryTheory
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.ProjectiveSpace

/-- Every twist has finite cohomology over the ring of an affine Noetherian base.

Source: Stacks Project, Tag 01XT, Lemma 30.8.1.
(blueprint: lem-pc-m4-projective-twist-finite-cohomology)

Proof: Set A = Gamma(T,O). The affine isomorphism T ≅ Spec A induces an
isomorphism of projective spaces, carrying the twist to the twist by its base-change
isomorphism. Compute cohomology by the standard affine coordinate cover. Its intersections
are affine and the twist is quasi-coherent, so the Cech-to-derived comparison applies.
Decompose the resulting complex by Laurent monomials of total degree m. A monomial with
some but not all exponents negative gives a contractible simplex complex. The remaining
summands contribute only in degree zero (all exponents nonnegative), or the top degree
(all exponents strictly negative). In each of those degrees only finitely many exponent
vectors have the prescribed total degree, so the cohomology is finite free over A.
With one coordinate the scheme is Spec A, every twist is free of rank one and positive
cohomology vanishes. With no coordinates the scheme is empty and all cohomology vanishes.
The comparison with T commutes with multiplication by every element of A, since restriction,
localization and the Cech comparison are natural for multiplication endomorphisms.
Thus the A-action is exactly restriction along the projective projection displayed below. -/
theorem finite_H_twist_affine {T : Scheme.{u}} [IsAffine T]
    [IsNoetherianRing Γ(T, ⊤)] (N : Type u) [Finite N] (m : ℤ) (q : ℕ) :
    letI : Module Γ(T, ⊤) ((twist N T m).H q) :=
      Module.compHom _ (ℙ(N; T) ↘ T).appTop.hom
    Module.Finite Γ(T, ⊤) ((twist N T m).H q) := by sorry

end AlgebraicGeometry.ProjectiveSpace
