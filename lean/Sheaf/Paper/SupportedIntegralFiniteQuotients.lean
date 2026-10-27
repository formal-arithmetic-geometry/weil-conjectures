/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.SupportedIntegralRestrictionComparison
public import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves

/-! # Finite supported integral quotients and scalar pullback

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md (2),
integral closed-fibre comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.SupportedIntegral
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
/-- Finite supported quotients in fixed scalar coordinates are classical, retain their
quotient action and a uniform ell-power annihilator, and scalar coordinates admit the
normalized geometric pullback comparison.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md (2), integral
closed-fibre comparison, steps 1--3 of the supported restriction-tower argument
(blueprint: lem-sfb-supported-integral-finite-quotients).

Proof in words:
1. Transport the continuous coefficient ring along the given topological ring isomorphism.
For the valuation-ring case, two generators of the maximal ideal differ by a unit;
transport multiplication and each quotient projection along these units. The integral
quotient normalization identifies each positive quotient with a finite discrete ring.
The prime ell lies in the uniformizer ideal, so its (n+1)-st power kills that quotient.
2. On each finite scalar-model chart, exact scalar extension takes a finite presentation
to the presentation of the ordinary quotient. Its finite quotient model is locally
constant. Extend the finite constructible strata through each support edge, adjoining
the complementary stratum with zero module. Exactness and scalar linearity preserve
the quotient relation and ell-power annihilation on these extensions.
3. Constructible pro-etale sheaves with finite discrete coefficients are classical.
Forgetting to sets preserves this assertion; the specified scalar coordinates identify
the underlying sheaf and the action, giving all three displayed properties.
4. Restrict continuous coefficients to constant scalars. The cartesian coefficient square
identifies this restriction before and after geometric inverse image. In section-action
coordinates its underlying direct-image map is identity. Conjugate by the prescribed
underlying coordinate isomorphisms to get lower_normalization. The adjunction mate is
invertible by the cartesian square; it gives upper and exactly the required mate equation.
The zero quotient, empty schemes and identity support path obey the same formulas. -/
theorem supported_integral_finite_quotients
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (π : R)
    (hR :
      (∃ e : R ≃+* ℤ_[ℓ], Continuous e ∧ Continuous e.symm ∧ e π = (ℓ : ℤ_[ℓ])) ∨
      (letI := spectralNorm.nontriviallyNormedField (Padic ℓ) E
       ∃ e : R ≃+* Padic.coefficientExtensionIntegers ℓ E,
         Continuous e ∧ Continuous e.symm ∧
         Ideal.span ({e π} : Set (Padic.coefficientExtensionIntegers ℓ E)) =
           Padic.coefficientExtensionMaximalIdeal ℓ E))
    {T₀ T S : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace T₀] [QuasiSeparatedSpace T₀]
    (t : T₀ ⟶ T) [IsClosedImmersion t]
    (tree : QcqsOpenClosedTree T) (p : tree.Path S)
    (c₀ : Coordinates R T₀) (c : Coordinates R T) :
    Nonempty (PullbackCoordinates R t c₀ c) ∧
    (∀ (M : Models R S) (n : ℕᵒᵖ),
      IsClassical ((sheafCompose (Scheme.ProEt.topology T)
        (forget (ModuleCat.{u + 1} (ULift.{u + 1} R)))).obj
          ((((supportedQuotients R p π) ⋙ towerMap c.functor).obj M).obj n))) ∧
    (∀ (M : Models R S) (n : ℕ) (V : T.ProEtᵒᵖ),
      (((((supportedQuotients R p π) ⋙ towerMap c.functor).obj M).obj (op n)).obj.obj V).smul
        (ULift.up (π ^ (n + 1))) = 0) ∧
    (∀ (M : Models R S) (n : ℕ), ∃ k : ℕ, ∀ (V : T.ProEtᵒᵖ)
      (x : ((((supportedQuotients R p π) ⋙ towerMap c.functor).obj M).obj (op n)).obj.obj V),
      (ℓ ^ k) • x = 0) := by sorry

end AlgebraicGeometry.ProEtale.SupportedIntegral
