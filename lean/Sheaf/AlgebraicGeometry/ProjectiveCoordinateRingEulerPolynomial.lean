/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q21
-/
module

public import Sheaf.RingTheory.CoordinateQuotientGrading
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.AlgebraicGeometry.ClosedImmersionSerreVanishing
import Sheaf.RingTheory.StandardGradedHilbertFunction

/-! # Homogeneous coordinate rings and Euler polynomials

Source: Stacks Project, Tags 0AG7, 01YS (4), 08AE and 00K1.
(blueprint: lem-sfb-projective-coordinate-ring-euler-polynomial)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

variable {k : Type u} [Field k] {N : ℕ}

/-- The actual graded quotient homomorphism, without saturation of the ideal.
Source: Stacks, Tag 00JL (blueprint: lem-sfb-projective-coordinate-ring-euler-polynomial). -/
def coordinateQuotientGradedMap
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k)) :
    MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k →+*ᵍ
      coordinateQuotientPiece J where
  __ := Ideal.Quotient.mk J.toIdeal
  map_mem hx := Submodule.mem_map_of_mem hx

/-- The closed-subscheme morphism induced by the actual quotient map.
Source: Stacks, Tag 01N0 (blueprint: lem-sfb-projective-coordinate-ring-euler-polynomial). -/
def coordinateQuotientImmersion
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k)) :
    Proj (coordinateQuotientPiece J) ⟶
      Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (N + 1))) k :=
  Proj.map (coordinateQuotientGradedMap J)
    (GradedRingHom.irrelevant_le_map_of_surjective (Ideal.Quotient.mk_surjective))

/-- The Euler characteristic of the pulled-back Proj twist, with its canonical k-structure.
Source: Stacks, Tags 01MN, 08AE.
(blueprint: lem-sfb-projective-coordinate-ring-euler-polynomial) -/
def coordinateQuotientEuler
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k))
    (m : ℕ) : ℤ :=
  @Scheme.Modules.eulerChar k _ (Proj (coordinateQuotientPiece J))
    (OverClass.ofHom (coordinateQuotientImmersion J ≫
      Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (N + 1))) k))
    ((Scheme.Modules.tensorPullback (coordinateQuotientImmersion J)).obj
      (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k) m))

/-- High coordinate dimensions equal Euler characteristics and a rational polynomial;
for an empty Proj the polynomial and both eventual values are zero.
Source: Stacks, Tags 0AG7, 01YS (4), 08AE, 00K1.
(blueprint: lem-sfb-projective-coordinate-ring-euler-polynomial)
Proof, following all six steps of the node: (1) On D_+(u_j), the degree-m localized
module is free on u_j^m, with transitions (u_i/u_j)^m. Thus its sheaf is exactly the
pullback of the projective twist (def-pc-proj, def-weil-pbc-proj-twisting-sheaf,
def-pc-projective-space-twist, def-pc-module-pullback). (2) The degree-zero quotient
is k or zero, hence Noetherian. Apply lem-sfb-finite-graded-module-section-tail to
S=M=B/J. Its eventual section isomorphism is k-linear, and the finite set of degree-m
monomials spans each piece. (3) Apply lem-weil-pbc-closed-immersion-serre-vanishing
to the structure sheaf and this closed immersion. (4) Above both bounds, the sum in
def-pc-euler-characteristic has only its degree-zero term. If Proj is empty, that
term is zero. (5) Apply lem-trf-standard-graded-hilbert-function to S=B, M=B/J to
obtain the eventual rational polynomial, and increase the common bound. (6) For
an empty Proj this polynomial vanishes at infinitely many integers, hence is zero.
The same uniqueness argument gives independence in the next declaration. -/
theorem exists_coordinateQuotient_euler_polynomial
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k)) :
    ∃ (m₀ : ℕ) (P : Polynomial ℚ),
      (∀ m : ℕ, m₀ ≤ m →
        (Module.finrank k (coordinateQuotientPiece J m) : ℤ) = coordinateQuotientEuler J m ∧
        P.eval (m : ℚ) = (Module.finrank k (coordinateQuotientPiece J m) : ℚ)) ∧
      (IsEmpty (Proj (coordinateQuotientPiece J)) → P = 0 ∧
        ∀ m : ℕ, m₀ ≤ m → Module.finrank k (coordinateQuotientPiece J m) = 0 ∧
          coordinateQuotientEuler J m = 0) := by
  sorry

/-- The eventual coordinate polynomial depends only on the embedded closed subscheme.
Source: Stacks, Tag 08AE (blueprint: lem-sfb-projective-coordinate-ring-euler-polynomial).
Proof: step 6 of the node. The isomorphism over the fixed projective space identifies
the pulled-back twists and their k-linear cohomology, hence their Euler characteristics.
Step 4, applied to each ideal, identifies the two coordinate Hilbert functions with
these same Euler values above a common bound. The two proposed polynomials then
agree on all sufficiently large nonnegative integers. Their difference has infinitely
many roots over Q and is zero. This uses no saturation or nonemptiness hypothesis. -/
theorem coordinateQuotient_polynomial_independent
    (J K : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k))
    (e : Proj (coordinateQuotientPiece J) ≅ Proj (coordinateQuotientPiece K))
    (he : e.hom ≫ coordinateQuotientImmersion K = coordinateQuotientImmersion J)
    (P Q : Polynomial ℚ)
    (hP : ∃ a : ℕ, ∀ m : ℕ, a ≤ m →
      P.eval (m : ℚ) = (Module.finrank k (coordinateQuotientPiece J m) : ℚ))
    (hQ : ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      Q.eval (m : ℚ) = (Module.finrank k (coordinateQuotientPiece K m) : ℚ)) :
    P = Q := by
  sorry

end
end AlgebraicGeometry
