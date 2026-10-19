/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q148
-/
module

public import Sheaf.RingTheory.RingPseudoCoherent
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.TraceFormula.AlgebraicShriekCalculus
import Sheaf.TraceFormula.FlatPolynomialQuotientPerfect
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Sheaf.CategoryTheory.DerivedCategory.PerfectComplexDerivedBiduality
import Sheaf.TraceFormula.UpperShriekBoundedCoherent
import Sheaf.Algebra.Homology.AlgebraicShriekDerivedHomAdjunction

/-! # Relative perfection of the algebraic polynomial upper-shriek model

Source: Stacks Project, dualizing.tex, Tag 0BZW, parts (1) and (2)(a)
(blueprint: lem-trf-algebraic-shriek-relative-perfect).

The polynomial model is actual coinduction of a K-injective resolution of P[0],
with the multiplication action provided by ModuleCat.coextendScalars, shifted by n.
Internal Hom and tensor are the existing closed derived module tensor structure.
The scalar map is the transpose of the identity, not an arbitrary isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

/-- The concrete polynomial coinduction complex Hom_P(A,I_P)[n], where I_P is the
canonical functorial K-injective resolution of P[0]. Ordinary coinduction supplies
(a h)(a') = h(a'a), including its A-action, in every degree.
Source: Stacks 0BZI, 0A70 and 0BZW
(blueprint: lem-trf-algebraic-shriek-relative-perfect). -/
def algebraicShriekPolynomialComplex {R A : Type u} [CommRing R] [CommRing A]
    (n : ℕ) (p : MvPolynomial (Fin n) R →+* A) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  ((((ModuleCat.coextendScalars p).mapHomologicalComplex (.up ℤ)).obj
    ((CochainComplex.kInjectiveResolutionFunctor.{u}
      (ModuleCat.{u} (MvPolynomial (Fin n) R))).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) R)) 0).obj
          (ModuleCat.of (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))))))⟦(n : ℤ)⟧

/-- The scalar-action morphism A[0] to RHom_A(K,K). It is the derived tensor-Hom
transpose of the identity of K, transported from the tensor unit to A[0].
Source: Stacks 0BZW(1)(c)
(blueprint: lem-trf-algebraic-shriek-relative-perfect). -/
def algebraicShriekScalarMap {A : Type u} [CommRing A]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶
      (ihom K).obj K :=
  (DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} A)).hom ≫
    MonoidalClosed.curry' (𝟙 K)

/-- Relative perfection and scalar rigidity for every polynomial presentation of a
flat finite-type map of commutative Noetherian rings. No lci assumption is used.
Source: Stacks 0BZW(1), (2)(a)
(blueprint: lem-trf-algebraic-shriek-relative-perfect).

Proof:
1. By lem-trf-flat-polynomial-quotient-perfect, A is perfect over P, with a
bounded finite-projective P-resolution.
2. Apply lem-trf-upper-shriek-bounded-coherent to R[0]. The polynomial model of
lem-trf-algebraic-shriek-calculus is precisely the displayed coinduction complex.
It has bounded finite A-cohomology. The Noetherian criterion
lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion gives pseudo-coherence.
3. By lem-trf-perfect-complex-derived-biduality, RHom_P(A,P) is perfect over P.
Choose a bounded finite-projective model E. The monomial basis makes P flat over R;
therefore all terms of E are R-flat. E[n] computes tensor with every R-module in
degree zero, and its finite support supplies one Tor interval independent of that module.
4. Apply lem-trf-algebraic-shriek-derived-hom-adjunction with X = D[n], Y = P[n],
D = RHom_P(A,P) with its coinduced A-action. Under its evaluation-at-one comparison,
the scalar-action map becomes the canonical P-double-dual evaluation of A. The
compatibility is a mapped to (h mapped to h(a)), including both shift cancellations.
Perfect biduality from step 1 makes this map invertible. Exact restriction reflects
isomorphisms because the cohomology of its cone has the same underlying groups.
-/
theorem algebraicShriek_relative_perfect
    {R A : Type u} [CommRing R] [CommRing A]
    [IsNoetherianRing R] [IsNoetherianRing A]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    (φ : R →+* A) (hflat : RingHom.Flat φ) (hfinite : RingHom.FiniteType φ)
    (n : ℕ) (p : MvPolynomial (Fin n) R →+* A)
    (hp : Function.Surjective p)
    (hcomp : p.comp (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) = φ) :
    DerivedCategory.IsPseudoCoherent
        (DerivedCategory.Q.obj (algebraicShriekPolynomialComplex n p)) ∧
      (∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (DerivedCategory.Q.obj (algebraicShriekPolynomialComplex n p)))) ∧
      (∀ i : ℤ, Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (DerivedCategory.Q.obj (algebraicShriekPolynomialComplex n p)))) ∧
      (∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn (ModuleCat.{u} R) a b
        ((ModuleCat.restrictScalars φ).mapDerivedCategory.obj
          (DerivedCategory.Q.obj (algebraicShriekPolynomialComplex n p)))) ∧
      IsIso (algebraicShriekScalarMap
        (DerivedCategory.Q.obj (algebraicShriekPolynomialComplex n p))) := by
  sorry

end AlgebraicGeometry
