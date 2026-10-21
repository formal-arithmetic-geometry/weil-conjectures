/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.CategoryTheory.ContinuousScalarRing
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Normed.Module.Basic
import Sheaf.CategoryTheory.CondensedProductActionInflation
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization

/-! # Acyclicity of polynomial translation modules

Source: main-20261015 blueprint, direct-images proof, paragraph (3), agent-formulated
polynomial translation analytic obligation; the exact all-continuous noncomplete
reference is WANTED (blueprint: lem-sfb-polynomial-translation-acyclic).

The coproduct cocone and the formula on every generalized monomial section specify
precisely the polynomial direct sum and its action. Existence is asserted as well as
acyclicity for every such presentation. No completion or degree bound is introduced.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar
open Profinite.CondensedAction (continuousScalarRing)

namespace Profinite.CondensedAction.PolynomialTranslation

variable (ell : ℕ) [Fact ell.Prime] (F : Type u) [NormedField F]
  [NormedAlgebra ℚ_[ell] F] (r m : ℕ)

/-- Substitute y_i-g_i in a monomial and leave every spectator z_j unchanged.
The coefficients are all continuous F-valued functions on S, with no completeness
hypothesis. The multiplicative tag encodes the additive lattice action.
Source: node's displayed translation formula, paragraph (3)
(blueprint: lem-sfb-polynomial-translation-acyclic). -/
def translatedMonomial (S : Profinite.{u})
    (g : C(S, Multiplicative (ULift.{u} (Fin r → ℤ_[ell]))))
    (d : (Fin r ⊕ Fin m) →₀ ℕ) : MvPolynomial (Fin r ⊕ Fin m) C(S, F) :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim
      (fun i ↦ MvPolynomial.X (Sum.inl i) - MvPolynomial.C
        (⟨fun s ↦ algebraMap ℚ_[ell] F ((g s).toAdd.down i : ℚ_[ell]),
          by fun_prop⟩ : C(S, F)))
      (fun j ↦ MvPolynomial.X (Sum.inr j))) (MvPolynomial.monomial d 1)

/-- A presentation of T_(r,m) by its monomial coproduct and exact internal translation
formula. The coproduct is in ordinary internal modules; its injections are internal
linear maps. The action equation holds for every profinite S and every varying g.
The formula on all coefficient sections of all coprojections determines the action.
Source: node's definition of T_(r,m), paragraph (3)
(blueprint: lem-sfb-polynomial-translation-acyclic). -/
structure Model where
  /-- The recorded category of internal condensed-group actions. -/
  object : CategoryTheory.CondensedBar.Equivariant (continuousScalarRing F)
    (Multiplicative (ULift.{u} (Fin r → ℤ_[ell])))
  /-- One copy of A for each finite exponent vector. -/
  ι : ((Fin r ⊕ Fin m) →₀ ℕ) →
    (Mod.regular (continuousScalarRing F).X ⟶ object.module)
  /-- The internal direct sum, without any bound on polynomial degree. -/
  isColimit : IsColimit (Cofan.mk object.module ι)
  /-- Finite polynomial substitution on every generalized monomial section. -/
  translation : ∀ (S : Profinite.{u})
    (g : C(S, Multiplicative (ULift.{u} (Fin r → ℤ_[ell]))))
    (d : (Fin r ⊕ Fin m) →₀ ℕ) (c : ULift.{u + 1} C(S, F)),
    object.act S g (((ι d).hom.hom.app (op S)) c) =
      ∑ e ∈ (translatedMonomial ell F r m S g d).support,
        ((ι e).hom.hom.app (op S))
          (ULift.up ((translatedMonomial ell F r m S g d).coeff e) * c)

/-- The polynomial translation module exists, and its ordinary total derived invariants
have zero positive cohomology as internal A-modules, for every coproduct presentation.
This is an assertion about the full internal action category, including ranks zero and
zero spectator count. The functor is the recorded ordinary derived invariants.
Source: node's vanishing assertion, paragraph (3)
(blueprint: lem-sfb-polynomial-translation-acyclic). -/
def Assertion : Prop :=
  Nonempty (Model ell F r m) ∧ ∀ T : Model ell F r m, ∀ q : ℤ, 0 < q →
    IsZero ((DerivedCategory.homologyFunctor
      (CategoryTheory.CondensedBar.Modules (continuousScalarRing F)) q).obj
      ((CategoryTheory.CondensedDerivedRestriction.derived (continuousScalarRing F)
        (Multiplicative (ULift.{u} (Fin r → ℤ_[ell])))).obj
          ((DerivedCategory.singleFunctor _ 0).obj T.object)))

/-- Polynomial translations are acyclic for internal lattice invariants, both over a
finite intermediate field and over the algebraic closure with its extended norm topology.
All continuous coefficient functions are retained; no completeness is assumed on Omega.
Source: main-20261015 direct-images proof, paragraph (3), agent-formulated analytic input
(blueprint: lem-sfb-polynomial-translation-acyclic).

Proof:
1. Induct on r simultaneously for every spectator count m. For r=0 the group is trivial,
   invariants and their derived functor are identity, so a degree-zero module is acyclic.
2. For r>0 separate translation in y_1 from G, the remaining r-1 coordinates. Filter
   polynomials by total degree n over E. On each finite-dimensional stage, D=-d/dy_1 is
   nilpotent, commutes with G, and its finite exponential is translation by -t. The
   transition maps are injective and compatible. Polynomial matrices prove continuity.
3. Finite-stage continuous F-valued functions are finite direct sums of A. Their sheaf
   colimit is the monomial coproduct. Apply lem-sfb-ind-unipotent-procyclic-difference
   to identify the ordinary H-derived invariants with [T --Delta--> T] in degrees 0,1,
   where Delta f=f(y_1-1)-f(y_1); no commutation with a filtered colimit is assumed.
4. Over B=A[y_2,...,y_r,z_1,...,z_m], use the polynomial basis b_0=1 and
   b_n=(-1)^n y_1(y_1+1)...(y_1+n-1)/n!. Its invertible rational leading terms give
   a basis, Delta b_n=b_(n-1), and Delta b_0=0. Set J b_n=b_(n+1), p f=f(0),
   and let i include constants. Then Delta J=1, J Delta=1-ip, and pi=1. These finite
   formulas give internal G-equivariant maps and a homotopy equivalence with B[0].
5. By lem-sfb-condensed-product-action-inflation, trivial and projection inflations
   are exact left adjoints to normalized invariants. Apply
   lem-sfb-derived-composition-adjunction-normalization: total lattice invariants are
   successive H- and G-derived invariants. Step 4 reduces them to those of T_(r-1,m),
   and induction proves positive vanishing for both E and Omega. The coproduct and
   substitution constructions also supply the asserted presentations in every rank.
-/
theorem polynomial_translation_acyclic (ell : ℕ) [Fact ell.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]
    (E : IntermediateField ℚ_[ell] Ω) [FiniteDimensional ℚ_[ell] E] (r m : ℕ) :
    Assertion ell E r m ∧ Assertion ell Ω r m := by
  sorry

end Profinite.CondensedAction.PolynomialTranslation
