/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.EquivariantAdicFibreNaturalityData

import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.Paper.CartesianCoefficients
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.SixFunctors.IntegralLisseFiniteConstants
import Sheaf.Paper.ContinuousCoefficientRealizations
import Sheaf.SixFunctors.IntegralLisseReductionComplete
import Sheaf.SixFunctors.IntegralLisseCoefficientLimit
import Sheaf.AlgebraicGeometry.ProEtalePointPullback
import Sheaf.SixFunctors.IntegralLisseLocalization

/-! # Equivariant adic fibre realization on the actual pro-etale slice

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.4(1), equivariant expansion
(blueprint: lem-sfb-equivariant-adic-fibre-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.EquivariantAdicFibre
open ContinuousModule

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {l E}

/-- Equivariant adic fibre realization, normalized on every finite quotient and on X[G].
Source: BS Lemma 6.8.2 and Proposition 6.8.4(1), equivariant expansion
(blueprint: lem-sfb-equivariant-adic-fibre-realization).

Proof: (1) use the DVR and finite-quotient theorems to identify the actual transition
kernels; (2) lift a basis inductively, using the determinant criterion over the finite
local rings, including the empty basis in rank zero; (3) apply the profinite integer
tower theorem, with its residue projections and topology; (4) take compatible basis
coordinates to identify the actual sections module with A^d, obtaining the adic basis
and quotient projections; (5) act coordinatewise and extend matrices to E; continuity
is detected on finite coordinates and then on matrix entries. (6) Identify u-inverse
image with slice restriction, transport Cartesian coefficients and the continuous
coefficient realization, and retain the actual quotient maps. (7) The normalized
integral lisse module cone and coefficient cone are limiting; their finite direct sums
are limiting coordinatewise. They produce the integral comparison with exactly the
prescribed phi_n. (8) Localize along A to E; ell is a unit times a positive uniformizer
power, and inverse image preserves this localization colimit. The resulting comparison
sends integral sections to 1 tensor q. (9) Restrict these limit cones to the whole
scheme X[G]. Their finite projections agree with the given descent arrows and the
coordinate action; limit uniqueness proves equality of sheaf maps. Localizing gives
rational equivariance. Steps (10)--(12), morphisms, refinements and basis independence,
are stated separately below. No finite-image condition, connectedness or qcqs assumption
is used, and the empty scheme and rank zero remain included. -/
theorem exists_realization {B X : Scheme.{u}} (u : X ⟶ B) [WeaklyEtale u]
    (G : Profinite.{u}) [Group G] [IsTopologicalGroup G]
    (a : ProfiniteCoefficientAction X G)
    (hu : a.act ≫ u = coefficientParameterProjection X G ≫ u)
    (D : FiniteData l E G) (P : Data B X u G a hu D) : Nonempty (Realization P) := by
  sorry


/-- The normalized realization is natural for compatible morphisms, arbitrary pro-etale
refinements, and continuous homomorphisms of the profinite groups.
Source: BS Proposition 6.8.4(1), expansion steps 10--11
(blueprint: lem-sfb-equivariant-adic-fibre-realization).

Proof: send q to the sequence (f_n(q_n)); transition compatibility puts it in the actual
inverse limit, and finite-coordinate continuity proves continuity. Equality in every
coordinate proves equivariance with the group homomorphism. Extend by e tensor q mapping
to e tensor f(q); finite basis coordinates prove norm continuity. The point-section maps
are postcomposition with these two maps. They are scalar linear and respect restriction,
so the fully faithful section-module interface gives the internal module maps. Restrict
the integral comparison to X' using the point-composition isomorphism. Each finite target
projection of its naturality square is exactly F.finite_square. Uniqueness into the
restricted limiting cone proves the integral square; localization proves the rational
square. The finite-coordinate equations also prove compatibility with identities and
compositions. No surjectivity of the group map or the refinement is needed. -/
theorem realization_natural {B X X' : Scheme.{u}} {u : X ⟶ B} {u' : X' ⟶ B}
    [WeaklyEtale u] [WeaklyEtale u']
    {G G' : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    [Group G'] [IsTopologicalGroup G']
    {a : ProfiniteCoefficientAction X G} {a' : ProfiniteCoefficientAction X' G'}
    {hu : a.act ≫ u = coefficientParameterProjection X G ≫ u}
    {hu' : a'.act ≫ u' = coefficientParameterProjection X' G' ≫ u'}
    {D : FiniteData l E G} {D' : FiniteData l E G'}
    {P : Data B X u G a hu D} {P' : Data B X' u' G' a' hu' D'}
    {r : X' ⟶ X} [WeaklyEtale r] {hr : r ≫ u = u'} {γ : G' →ₜ* G}
    (F : Morphism P P' r hr γ) (R : Realization P) (R' : Realization P') :
    Nonempty (Naturality F R R') := by
  sorry


/-- Compatible changes of finite bases lift to A, and conjugate the integral matrices.
The scalar-extended coordinates conjugate the E-matrices by the scalar extension of c.
Source: BS Proposition 6.8.4(1), expansion step 12
(blueprint: lem-sfb-equivariant-adic-fibre-realization).

Proof: take the entries of b'_n b_n^{-1} in the complete scalar limit. The inverse entries
are compatible as well, so the two limiting matrices are inverses. Their coordinate
identity gives the displayed conjugation. Extending entries to E gives the two rational
bases and the scalar-extended change matrix, with the same conjugation formula. All
identities are valid for empty matrices and bases. -/
theorem compatible_bases_conjugate {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    (D : FiniteData l E G) (R : Algebraic D)
    (b : ∀ n : ℕ, Level D n ≃ₗ[Integers l E]
      (Fin D.rank → Padic.coefficientExtensionRing l E (n + 1)))
    (_hb : ∀ (n : ℕ) (v : Level D (n + 1)) (i : Fin D.rank),
      b n (D.tower.map (homOfLE (Nat.le_succ n)).op v) i =
        Padic.coefficientExtensionTransition l E (n + 1) (b (n + 1) v i)) :
    ∃ (c : (Fin D.rank → Integers l E) ≃ₗ[Integers l E] (Fin D.rank → Integers l E))
      (bQ : Fibre D ≃ₗ[Integers l E] (Fin D.rank → Integers l E))
      (bE bE' : Rational D ≃ₗ[E] (Fin D.rank → E))
      (cE : (Fin D.rank → E) ≃ₗ[E] (Fin D.rank → E)),
      bQ = R.coordinates.trans c ∧
      (∀ (n : ℕ) (q : Fibre D) (i : Fin D.rank), b n (projection D n q) i =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) (bQ q i)) ∧
      (∀ (g : G), bQ.symm.trans ((R.action g).trans bQ) =
        c.symm.trans ((R.coordinates.symm.trans ((R.action g).trans R.coordinates)).trans c)) ∧
      (∀ (e : E) (q : Fibre D) (i : Fin D.rank),
        bE (e ⊗ₜ[Integers l E] q) i = e * (R.coordinates q i : E)) ∧
      (∀ (e : E) (q : Fibre D) (i : Fin D.rank),
        bE' (e ⊗ₜ[Integers l E] q) i = e * (bQ q i : E)) ∧
      (∀ (v : Fin D.rank → Integers l E) (i : Fin D.rank),
        cE (fun j ↦ (v j : E)) i = (c v i : E)) ∧
      (∀ g : G, bE'.symm.trans ((R.rho g).trans bE') =
        cE.symm.trans ((bE.symm.trans ((R.rho g).trans bE)).trans cE)) := by
  sorry

/-- The intrinsic comparison is independent of the compatible bases used to construct it.
Source: BS Proposition 6.8.4(1), expansion step 12
(blueprint: lem-sfb-equivariant-adic-fibre-realization).

Proof: the identity on Q induces the unique identity-on-continuous-sections map between
its two point realizations. It is an isomorphism, with the map induced by the reverse
identity as inverse. Composing the two integral comparisons with each finite projection
gives the same prescribed phi_n, so the limiting property makes their square commute.
The same identity on E tensor Q gives the rational isomorphism, and the localization unit
makes its square commute. Both maps intertwine the full parameter descent by their
pointwise action formulas. Thus changing bases gives an isomorphic equivariant module. -/
theorem realization_independent {B X : Scheme.{u}} {u : X ⟶ B} [WeaklyEtale u]
    {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    {a : ProfiniteCoefficientAction X G}
    {hu : a.act ≫ u = coefficientParameterProjection X G ≫ u}
    {D : FiniteData l E G} {P : Data B X u G a hu D}
    (R R' : Realization P) :
    ∃ (e : R.integral.object ≅ R'.integral.object)
      (eE : R.rational.object ≅ R'.rational.object),
      RepresentsMap R.integral R'.integral (LinearMap.id : Fibre D →ₗ[Integers l E] Fibre D)
        e.hom ∧
      RepresentsMap R.rational R'.rational (LinearMap.id : Rational D →ₗ[E] Rational D) eE.hom ∧
      R.integralIso.hom ≫ (pull (Integers l E) X).map e.hom = R'.integralIso.hom ∧
      R.rationalIso.hom ≫ (pull E X).map eE.hom = R'.rationalIso.hom := by
  sorry


end AlgebraicGeometry.ProEtale.EquivariantAdicFibre
