/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientData
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.Algebra.Homology.ScalarHomTensorCancellation
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.SecSmoothPurity.ScalarExtensionFunctor

/-! # Cofinal finite reductions and constructibility

Source: blueprint main-20261015, sk-lem-sp-tower, final integral-constructibility sentence;
Stacks Tags 0D6D and 0G7E; scalar-extension proof paragraphs (2) and (4)
(blueprint: lem-sp-cofinal-finite-reduction-constructibility).

Index n means positive exponent n+1. The ordinary and derived tensors below are the
published universal presentations. Their normalization records the pure-tensor formula,
K-flat counit calculation, and naturality under commuting coefficient squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.SuccessiveDerivedQuotient

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})

/-- The quotient exists exactly at the stated cofinal exponents.
Source: blueprint tower proof, quotient arithmetic; Stacks 0D6D
(blueprint: lem-sp-cofinal-finite-reduction-constructibility).
Proof: ell = v*pi^e implies ell^(N+1) = v^(N+1)*pi^(e*(N+1)).
When j+1 <= e*(N+1), factor out pi^(j+1). The principal-ideal power formula
then gives the required inclusion. This uses no unramifiedness assumption. -/
theorem sp_cofinal_finite_ideal_le (e : ℕ)
    (v : (Padic.coefficientExtensionIntegers l E)ˣ)
    (hfactor : (l : Padic.coefficientExtensionIntegers l E) =
      v * Padic.coefficientExtensionUniformizer l E ^ e)
    (N j : ℕ) (h : j + 1 ≤ e * (N + 1)) :
    spEllIdeal l E ^ (N + 1) ≤ Padic.coefficientExtensionIdeal l E (j + 1) := by
  sorry

/-- The canonical quotient, sending the class of x to the class of x.
Source: blueprint tower proof, quotient arithmetic
(blueprint: lem-sp-cofinal-finite-reduction-constructibility). -/
def spCofinalFiniteQuotient (e : ℕ)
    (v : (Padic.coefficientExtensionIntegers l E)ˣ)
    (hfactor : (l : Padic.coefficientExtensionIntegers l E) =
      v * Padic.coefficientExtensionUniformizer l E ^ e)
    (N j : ℕ) (h : j + 1 ≤ e * (N + 1)) :
    (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (N + 1)) →+*
      Padic.coefficientExtensionRing l E (j + 1) :=
  Ideal.Quotient.factor (sp_cofinal_finite_ideal_le l E e v hfactor N j h)

/-- Constant sheafification of the actual cofinal quotient, retaining target coefficients.
Source: blueprint tower proof, quotient arithmetic
(blueprint: lem-sp-cofinal-finite-reduction-constructibility). -/
def spCofinalFiniteCoefficientMap (e : ℕ)
    (v : (Padic.coefficientExtensionIntegers l E)ˣ)
    (hfactor : (l : Padic.coefficientExtensionIntegers l E) =
      v * Padic.coefficientExtensionUniformizer l E ^ e)
    (N j : ℕ) (h : j + 1 ≤ e * (N + 1)) :
    (spCoefficientCommRings.{u, u} l E T).obj (op N) ⟶
      WeilConjectures.integralCoefficientCommRingSheaf.{u, u} l E T j :=
  letI : HasSheafify (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
    WeilConjectures.integralCoefficientRingSheafify.{u, u} T
  (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((spCofinalFiniteQuotient l E e v hfactor N j h).comp
        ULift.ringEquiv.toRingHom)))

/-- The cofinal quotients commute with further reduction in either index.
These are equalities of the actual coefficient sheaf maps, including the endpoints.
Source: blueprint tower proof, quotient arithmetic and scalar-extension proof (4)
(blueprint: lem-sp-cofinal-finite-reduction-constructibility).
Proof: all four composites are induced by the identity on the valuation ring.
Quotient induction proves the equalities on the finite rings; constant sheafification
and forgetting commutativity preserve them. Identity and successive reductions are
included. No completeness or flatness assertion enters this argument. -/
theorem sp_cofinal_finite_quotient_compatibility (e : ℕ)
    (v : (Padic.coefficientExtensionIntegers l E)ˣ)
    (hfactor : (l : Padic.coefficientExtensionIntegers l E) =
      v * Padic.coefficientExtensionUniformizer l E ^ e) :
    (∀ (M N j : ℕ) (hMN : M ≤ N)
      (h : j + 1 ≤ e * (M + 1)) (h' : j + 1 ≤ e * (N + 1)),
      (spCoefficientRings l E T).map (homOfLE hMN).op ≫
        (sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (spCofinalFiniteCoefficientMap l E T e v hfactor M j h) =
        (sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (spCofinalFiniteCoefficientMap l E T e v hfactor N j h')) ∧
    (∀ (N k j : ℕ) (hkj : k ≤ j)
      (h : j + 1 ≤ e * (N + 1)) (h' : k + 1 ≤ e * (N + 1)),
      (sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (spCofinalFiniteCoefficientMap l E T e v hfactor N j h) ≫
        (WeilConjectures.integralCoefficientSheafSystem l E T).map (homOfLE hkj).op =
      (sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (spCofinalFiniteCoefficientMap l E T e v hfactor N k h')) := by
  sorry

/-- The standard-localization instance of the recorded universal scalar presentation.
This is only an abbreviation of the dependency's data, not a new tensor construction.
Source: Stacks 06YY (blueprint: lem-sp-cofinal-finite-reduction-constructibility). -/
abbrev spCofinalScalarPresentation
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :=
  Presentation.{u + 1, u, u + 1, u + 2} (C := T.ProEt)
    (J := Scheme.ProEt.topology T)
    (hD := fun R ↦ HasDerivedCategory.standard
      (SheafOfModules.SuccessiveDerivedQuotient.Modules.{u + 1, u, u + 1} R)) a

/-- Positivity supplies the existing finiteness theorem for every uniformizer quotient.
Source: blueprint coefficient convention
(blueprint: lem-sp-cofinal-finite-reduction-constructibility). -/
instance spCofinalUniformizerQuotientFinite (j : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (j + 1)) :=
  Padic.finite_coefficientExtensionRing l E (j + 1) (Nat.le_add_left 1 j)

/-- Cofinal scalar associativity, its K-flat model, and transfer of constructibility
and the same Tor interval. The completed ell projections are specified by equality
with the uniquely normalized limit comparison; they are not arbitrary coefficient maps.
The family `n` is the published normalized presentation of scalar extension. Its fields
`ordinary_hom`, `ordinary_inv`, and `representative` specify precisely the ordinary
reassociation formula and its derived class; `coefficient_naturality` and `associative`
specify compatibility with further quotients in both indices. They apply to the displayed
canonical quotients. Using arbitrary such presentations expresses independence of models.
Source: blueprint main-20261015, tower proof final integral-constructibility sentence;
Stacks 0D6D, 0G7E; scalar-extension proof (2),(4)
(blueprint: lem-sp-cofinal-finite-reduction-constructibility).

Proof: (1) The ideal inclusion above defines the quotient. Every quotient square commutes
because all maps send the class of x to the class of x. Composing the completed ell
projection with the quotient is the uniformizer projection: check after the canonical
constant-to-completion map and use the finite-quotient normalization/uniqueness.
(2) For an acyclic B-complex L, exact scalar restriction preserves acyclicity. Ordinary
scalar-tensor cancellation identifies the restriction of L tensor_B (P tensor_R B)
with Res(L) tensor_R P. K-flatness of P kills its cohomology; restriction detects this.
Thus the extended representative is K-flat (lem-pur-sheaf-ring-derived-coefficient-adjunction,
lem-sfb-scalar-tensor-cancellation-independent, def-pc-kflat-complex).
(3) Apply lem-sfb-successive-derived-quotient-normalization and lem-pc-kflat-resolution.
Its ordinary formula is (x tensor b) tensor d mapped to x tensor (bar(b)*d), with inverse
x tensor d mapped to (x tensor 1) tensor d; its counit equation fixes the derived map
in D(D_j). Naturality and coherence give all further quotient compatibilities.
(4) Test the assumed Tor interval on the degree-zero unit B_N: cohomology vanishes
outside [a,b]. Thus each reduction is bounded constructible of finite Tor dimension.
For j choose N=j (in positive-exponent notation); e>=1 makes this cofinal. Apply clause
(2) of det-sp-scalar-extension-functor to the finite quotient map, with no flatness or
finite projective-dimension requirement. Transport constructibility and the same Tor
interval through (3); testing on D_j gives the stated cohomology vanishing. No assumption
on completeness, invertibility of ell on T, or boundedness of the original K is used. -/
theorem sp_cofinal_finite_reduction_constructibility (e : ℕ) (he : 1 ≤ e)
    (v : (Padic.coefficientExtensionIntegers l E)ˣ)
    (hfactor : (l : Padic.coefficientExtensionIntegers l E) =
      v * Padic.coefficientExtensionUniformizer l E ^ e)
    (β : ∀ N : ℕ, WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T ⟶
      (spCoefficientCommRings.{u, u} l E T).obj (op N))
    (hβ : ∀ N : ℕ,
      (sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (β N) =
      (sp_completed_coefficient_limit l E T).exists.choose.hom ≫
        limit.π (spCoefficientRings l E T) (op N))
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
      (a : R ⟶ S), spCofinalScalarPresentation T a)
    (n : Normalization.{u + 1, u, u + 1, u + 2}
      (C := T.ProEt) (J := Scheme.ProEt.topology T)
      (hD := fun R ↦ HasDerivedCategory.standard
      (SheafOfModules.SuccessiveDerivedQuotient.Modules.{u + 1, u, u + 1} R)) p) :
    (∀ (N j : ℕ) (h : j + 1 ≤ e * (N + 1)),
      ∃ hcomp : β N ≫ spCofinalFiniteCoefficientMap l E T e v hfactor N j h =
          WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T j,
        ∃ α : (p (β N)).derived ⋙
            (p (spCofinalFiniteCoefficientMap l E T e v hfactor N j h)).derived ≅
          (p (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T j)).derived,
          α = n.derived (β N) (spCofinalFiniteCoefficientMap l E T e v hfactor N j h) ≪≫
            eqToIso (congrArg (fun f ↦ (p f).derived) hcomp)) ∧
    (∀ (N : ℕ)
      (P : CochainComplex
        (SheafOfModules.SuccessiveDerivedQuotient.Modules.{u + 1, u, u + 1}
          (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients P →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := Scheme.ProEt.topology T)
        (R := WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T) (P.X i)) →
      CochainComplex.IsKFlatIndependentCoefficients
        (((p (β N)).ordinary.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ∧
    ∀ (K : @DerivedCategory
        (SheafOfModules.SuccessiveDerivedQuotient.Modules.{u + 1, u, u + 1}
          (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T))
          _ _ (HasDerivedCategory.standard _)) (a b : ℤ), a ≤ b →
      (∀ N : ℕ,
        (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T
          (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (N + 1))
          ((DerivedCategory.homologyFunctor _ i).obj ((p (β N)).derived.obj K))) ∧
        Scheme.HasProEtaleTorAmplitude T
          (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (N + 1))
          ((p (β N)).derived.obj K) a b) →
      ∀ j : ℕ,
        (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T
          (Padic.coefficientExtensionRing l E (j + 1))
          ((DerivedCategory.homologyFunctor _ i).obj
            ((p (WeilConjectures.completedIntegralCommRingProjectionUnrestricted
              l E T j)).derived.obj
              K))) ∧
        Scheme.HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (j + 1))
          ((p (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T j)).derived.obj
            K) a b ∧
        ∀ i : ℤ, i < a ∨ b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
          ((p (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T j)).derived.obj
            K)) := by
  sorry

end AlgebraicGeometry.ProEtale
