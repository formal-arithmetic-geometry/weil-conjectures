module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Simultaneous algebra and module models over a Noetherian local subring

Source: Stacks Project, `flat.tex`, Tag 0AT8, proof of lemma-find-pure-spreadout,
the choice of the local coefficient subring and simultaneous algebra/module models
(blueprint: lem-sfb-local-algebra-module-noetherian-subring-model).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra

/-- A finitely presented algebra and module descend together to a local Noetherian subring
essentially of finite type over the integers. The scalar structures on `M` and `M₀` are the
restrictions of the displayed algebra actions, as expressed by the scalar-tower conditions.
The `C₀`-algebra structure on `C` is specified by the equation involving `α`. The last equation
expresses compatibility with its action; together with `R`-linearity it gives compatibility
with the whole algebra `R ⊗[R₀] C₀` transported through `α`.

Source: Stacks Project, `flat.tex`, Tag 0AT8, proof of lemma-find-pure-spreadout
(blueprint: lem-sfb-local-algebra-module-noetherian-subring-model).

Proof: Choose a finite polynomial presentation of `C` and a finite matrix presentation of
`M`. Lift the matrix entries to polynomials. Adjoin variables `Yₗ` and relations `Yₗ - uₗ`
for their finitely many coefficients `uₗ`; evaluation and inclusion identify this augmented
presentation with `C`, including empty presentations. Apply
`lem-trf-presentation-noetherian-coefficient-model` to this presentation. Its coefficient
subring `D` contains every coefficient, is finite type over the integers and Noetherian,
and its finitely presented model `E` has the specified tensor identification with `C`.

Let `p = D ∩ m` and invert `D ∖ p`. These denominators are units in the local ring `R`.
The localization injects into `R`, since a fraction mapping to zero has numerator zero
already in `D`. Its image is the subring `R₀`. Its nonunits are precisely the fractions
with numerator in `p`, giving maximal ideal `R₀ ∩ m`. Localization preserves Noetherianity
by `lem-weil-pbc-localization-noetherian`; this description also makes `R₀` essentially
finite type over the integers, and its maximal ideal is finitely generated.

Set `C₀ = E ⊗[D] R₀`. The coefficient-model lemma gives its finite presentation and,
by tensor associativity, the algebra isomorphism `α`. The original matrix descends to a
matrix over `C₀`; define `M₀` as its cokernel. It is finitely presented. Tensor right
exactness (`lem-weil-pbc-tensor-right-exact`) identifies its base-changed cokernel with
`M`, giving `β`, without any flatness assumption.

Finally, the balanced maps `r ⊗ x ↦ (r ⊗ 1) ⊗ x` and
`(r ⊗ c₀) ⊗ x ↦ r ⊗ (c₀ • x)` are mutually inverse. Compose this identification with
`α` and `β` to obtain `γ`, whose pure-tensor formula is the canonical balanced map.
The formulas respect multiplication on the algebra tensor factor, so `γ` respects the
`C`-action through `α`, as expressed by the last equation.
-/
theorem exists_local_algebra_module_noetherian_subring_model
    (R : Type u) (C : Type v) (M : Type w)
    [CommRing R] [IsLocalRing R] [CommRing C] [Algebra R C]
    [Algebra.FinitePresentation R C] [AddCommGroup M] [Module C M]
    [Module R M] [IsScalarTower R C M] [Module.FinitePresentation C M] :
    ∃ (R₀ : Subring R) (_ : IsLocalRing R₀),
      IsNoetherianRing R₀ ∧ Algebra.EssFiniteType ℤ R₀ ∧
      IsLocalRing.maximalIdeal R₀ = (IsLocalRing.maximalIdeal R).comap R₀.subtype ∧
      (IsLocalRing.maximalIdeal R₀).FG ∧
      ∃ (C₀ : Type u) (_ : CommRing C₀) (_ : Algebra R₀ C₀),
        Algebra.FinitePresentation R₀ C₀ ∧
        ∃ (α : R ⊗[R₀] C₀ ≃ₐ[R] C) (_ : Algebra C₀ C),
          (∀ c₀ : C₀, algebraMap C₀ C c₀ = α (1 ⊗ₜ[R₀] c₀)) ∧
          ∃ (M₀ : Type u) (_ : AddCommGroup M₀) (_ : Module C₀ M₀)
            (_ : Module R₀ M₀) (_ : IsScalarTower R₀ C₀ M₀),
            Module.FinitePresentation C₀ M₀ ∧
            ∃ (β : C ⊗[C₀] M₀ ≃ₗ[C] M) (γ : R ⊗[R₀] M₀ ≃ₗ[R] M),
              (∀ (r : R) (x : M₀), γ (r ⊗ₜ[R₀] x) = r • β (1 ⊗ₜ[C₀] x)) ∧
              (∀ (c₀ : C₀) (r : R) (x : M₀),
                γ (r ⊗ₜ[R₀] (c₀ • x)) = α (1 ⊗ₜ[R₀] c₀) • γ (r ⊗ₜ[R₀] x)) := by
  sorry

end Algebra
