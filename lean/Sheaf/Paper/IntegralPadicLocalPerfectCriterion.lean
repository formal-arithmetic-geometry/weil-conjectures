/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z5
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.IntegralStratifiedPerfectModels
public import Sheaf.Paper.PbcCompletedPullbackActual
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification

/-! # Local perfect models over the actual valuation ring

Source: Bhatt--Scholze, Proposition 6.6.11 and Definition 6.5.1.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The local-perfect criterion with the actual valuation ring, using the small
pro-etale site of each covering scheme rather than its equivalent slice site.
Source: Bhatt--Scholze, Proposition 6.6.11 and Definition 6.5.1
(blueprint: lem-weil-pbc-integral-padic-local-perfect-criterion).

Proof: membership gives a uniform constructible reduction tower and intrinsic
completeness. Refine the finitely many constructibility stratifications of the
bounded residue complex. On a pro-etale cover of each stratum this residue complex
is constant and perfect, since the residue ring is a field. The valuation ring is
complete for its uniformizer ideal. Residue-lisse perfect lifting therefore lifts
the residue complex to a bounded finite-projective complex over the valuation ring.
Completeness identifies its completed realization with the original local object.
The pro-etale slice over a covering object is equivalent to the pro-etale site of
its underlying scheme; transport the realization and its isomorphism through this
equivalence and the canonical completed-coefficient inverse-image comparison.

Conversely, finite-projective terms are retracts of finite sums of the completed
ring, hence complete, with finite locally constant reductions. Completeness is
local for pro-etale covers and is detected on the finite strata. Each stratum is
quasi-compact: choose finitely many covering members to get a single bound for all
reductions. Normalized constructible local effectivity supplies the uniform tower
with its common local models. Finite-level site comparison supplies etale origins;
bounded-below full faithfulness uniquely lifts the transition isomorphisms and
inverses, and faithfulness gives their cocycles. These are precisely the three
membership conditions. The empty stratification and zero complexes cause no
exception. All coefficient comparisons preserve the actual quotient projections. -/
theorem integralPadicLocalPerfectCriterion
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] [IsNoetherian T]
    (hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n) (hl : IsUnit (l : Γ(T, ⊤)))
    (K : PbcCompletedDerived T (pbcPadicCoefficientDatum l E)) :
    PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E) K ↔
      ∃ s : FiniteLocallyClosedStratification T, ∀ k : Fin s.n,
        ∃ V : Sieve (⊤_ (s.domain k).ProEt),
          V ∈ ProEt.topology (s.domain k) (⊤_ (s.domain k).ProEt) ∧
          ∀ (U : (s.domain k).ProEt) (f : U ⟶ ⊤_ (s.domain k).ProEt), V f →
            ∃ (P : CochainComplex
                (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
              (a b : ℤ),
              P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
              (∀ q : ℤ, Module.Projective (Padic.coefficientExtensionIntegers l E) (P.X q) ∧
                Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X q)) ∧
              Nonempty ((pbcActualDerivedPull (U.hom ≫ s.immersion k)
                (pbcPadicCoefficientDatum l E)).obj K ≅
                (integralConstantDerived U.left (pbcPadicCoefficientDatum l E)).obj
                  ((completedConstantQ _).obj P)) := by sorry

end AlgebraicGeometry.Scheme
