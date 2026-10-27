module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Dual.Defs
public import Sheaf.Algebra.Lie.RestrictedEnvelopingAlgebra
import Sheaf.Algebra.Lie.AssociativeJacobsonIdentities
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Relative restricted tangent calculus

Source: Milne, Algebraic Groups (2017), Propositions 10.28--10.29, pp.195--196,
and the paragraph before Proposition 11.36, p.223
(blueprint: lem-sfb-relative-restricted-tangent-calculus).

The arbitrary-base bialgebra formulation is the agent-supplied generalization recorded
in the node. `WithConv` supplies the existing convolution algebra. The Jacobson terms
are computed in that algebra; coefficientwise inclusion identifies them with the
coefficients of the tangent-module polynomial in the node.
## Main definitions and statements

- `RelativeBialgebra.tangentFunctionals`: the relative augmentation-rule submodule.
- `RelativeBialgebra.contraction`: contraction for any functional.
- `RelativeBialgebra.relative_restricted_tangent_calculus`: all ten clauses of the node.

- The universes of the field, base, coordinate algebra, and test algebra are independent.
- `DualNumber R` is Mathlib's split square-zero algebra, with elements `r + εs`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

open scoped TensorProduct

namespace RelativeBialgebra

/-- Augmentation derivations, as the submodule cut out by the augmentation product rule.
Source: Milne, Proposition 10.28, p.195; the relative version in
(blueprint: lem-sfb-relative-restricted-tangent-calculus).
This construction also applies to augmented algebras without a coalgebra structure,
which is needed for the last naturality clause. -/
def tangentFunctionals (R : Type v) (C : Type w) [CommRing R] [CommRing C]
    [Algebra R C] (ε : C →ₐ[R] R) : Submodule R (C →ₗ[R] R) :=
  ⨅ x : C, ⨅ y : C, LinearMap.ker
    (Module.Dual.eval R C (x * y) - ε x • Module.Dual.eval R C y -
      ε y • Module.Dual.eval R C x)

/-- Contract the second leg of comultiplication with any linear functional.
Source: Milne, Proposition 10.29, pp.195--196; relative version in
(blueprint: lem-sfb-relative-restricted-tangent-calculus).
The right tensor unitor supplies the scalar multiplication suppressed in `(1 ⊗ a) Δ`. -/
def contraction (R : Type v) (C : Type w) [CommRing R] [CommRing C]
    [Bialgebra R C] (a : C →ₗ[R] R) : Module.End R C :=
  (TensorProduct.rid R C).toLinearMap.comp
    ((TensorProduct.map (LinearMap.id : C →ₗ[R] C) a).comp
      (Coalgebra.comul (R := R) (A := C)))

/-- Relative tangent calculus, including the restricted operation and natural dual-number
interpretation. Source: Milne, Propositions 10.28--10.29, pp.195--196, and the paragraph
before Proposition 11.36, p.223; the relative generalization is agent-supplied
(blueprint: lem-sfb-relative-restricted-tangent-calculus).

Proof plan (the ten steps of the node):
1. Split `C = R ⊕ I` using `εη = 1`. A tangent functional kills `1` by subtraction,
   and kills `I²` by its product rule. Conversely use `c ↦ λ([c - ηε(c)])`.
   The identity for the augmentation part of a product proves the inverse product rule.
2. Tensor bilinearity (`def-weil-pbc-module-tensor-product`) and tensor multiplication
   (`lem-weil-pbc-algebra-tensor-pushout-universal-property`) show that contraction of
   a tangent functional is a derivation. Coassociativity proves its invariance.
3. Applying the counit to an invariant derivation gives a tangent functional.
   The two counit identities prove that contraction and counit composition are inverse;
   the counit recovers every functional, even one not tangent.
4. Coassociativity gives `D_(a*b) = D_a D_b` in the stated order, and induction gives
   compatibility with convolution powers. No cocommutativity is used.
5. Expand the product rule for a commutator: the middle terms cancel. Invariance
   is preserved under composition and subtraction. Expand the six triple products
   to obtain Jacobi; convolution bilinearity and subtraction give alternation.
6. In `k`, the integers strictly between zero and `p` are invertible. The integer
   binomial recurrence kills the interior coefficients in `k`, hence in `R`, even
   when `R` is the zero ring; no cancellation in `R` is required (`def-weil-field`).
7. On the tensor square, `U = D ⊗ 1` and `V = 1 ⊗ D` commute. Induct from
   `D μ = μ(U+V)` and apply `Commute.add_pow`
   (`lem-sfb-commuting-binomial-expansion`). Step 6 leaves the two endpoint terms,
   so `D^p` is an invariant derivation and the convolution pth power is tangent.
8. Apply `Algebra.associative_jacobson_identities`
   (`lem-sfb-associative-jacobson-identities`) in `End_R(C)` over `k`.
   Contraction is injective, also coefficientwise on polynomials. Thus the adjoint
   and sum identities descend with `LieAlgebra.restrictedJacobsonTerm`'s
   coefficient normalization (`def-sfb-restricted-enveloping-algebra`).
   R-linearity gives `(aD)^p = a^p D^p` for every `a : R`.
9. A bialgebra homomorphism preserves augmentation and comultiplication. Precomposition
   is linear, preserves the augmentation rule, convolution, bracket and pth power.
10. In dual numbers, the second coefficient of a product is `rs' + sr'`.
    Thus the displayed lift is an algebra map exactly for tangent functionals, and
    every augmented lift has a unique such coefficient. Substitution proves
    naturality for augmented algebra maps, without a coalgebra assumption on them.
    For an affine group these lifts are precisely the relative tangent vectors at
    its identity by definition, and contraction realizes its invariant Lie operations.
-/
theorem relative_restricted_tangent_calculus
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (R : Type v) [CommRing R] [Algebra k R]
    (C : Type w) [CommRing C] [Bialgebra R C] :
    (∀ a : C →ₗ[R] R,
      a ∈ tangentFunctionals R C (Bialgebra.counitAlgHom R C) ↔
        ∀ x y : C, a (x * y) = Coalgebra.counit (R := R) x * a y +
          a x * Coalgebra.counit (R := R) y) ∧
    (∃ e : tangentFunctionals R C (Bialgebra.counitAlgHom R C) ≃ₗ[R]
        Module.Dual R (RingHom.ker (Bialgebra.counitAlgHom R C).toRingHom).Cotangent,
      ∀ a : tangentFunctionals R C (Bialgebra.counitAlgHom R C),
        ∀ x : RingHom.ker (Bialgebra.counitAlgHom R C).toRingHom,
          e a ((RingHom.ker (Bialgebra.counitAlgHom R C).toRingHom).toCotangent x) = a.1 x.1) ∧
    (∃ M : Submodule R (Derivation R C C),
      (∀ D : Derivation R C C, D ∈ M ↔
        (Coalgebra.comul (R := R)).comp D.toLinearMap =
          (TensorProduct.map (LinearMap.id : C →ₗ[R] C) D.toLinearMap).comp
            (Coalgebra.comul (R := R))) ∧
      ∃ e : tangentFunctionals R C (Bialgebra.counitAlgHom R C) ≃ₗ[R] M,
        (∀ a : tangentFunctionals R C (Bialgebra.counitAlgHom R C),
          (e a).1.toLinearMap = contraction R C a.1) ∧
        (∀ D : M, (e.symm D).1 = (Coalgebra.counit (R := R)).comp D.1.toLinearMap)) ∧
    (∀ a b : C →ₗ[R] R,
      contraction R C (WithConv.toConv a * WithConv.toConv b).ofConv =
        contraction R C a * contraction R C b) ∧
    (∃ B : tangentFunctionals R C (Bialgebra.counitAlgHom R C) →ₗ[R]
        tangentFunctionals R C (Bialgebra.counitAlgHom R C) →ₗ[R]
          tangentFunctionals R C (Bialgebra.counitAlgHom R C),
      ∃ P : tangentFunctionals R C (Bialgebra.counitAlgHom R C) →
          tangentFunctionals R C (Bialgebra.counitAlgHom R C),
        (∀ a b : tangentFunctionals R C (Bialgebra.counitAlgHom R C),
          (B a b).1 =
            (WithConv.toConv a.1 * WithConv.toConv b.1 -
              WithConv.toConv b.1 * WithConv.toConv a.1).ofConv) ∧
        (∀ a : tangentFunctionals R C (Bialgebra.counitAlgHom R C),
          (P a).1 = (WithConv.toConv a.1 ^ p).ofConv ∧
            contraction R C (P a).1 = contraction R C a.1 ^ p) ∧
        (∀ a : tangentFunctionals R C (Bialgebra.counitAlgHom R C), B a a = 0) ∧
        (∀ a b c : tangentFunctionals R C (Bialgebra.counitAlgHom R C),
          B a (B b c) + B b (B c a) + B c (B a b) = 0) ∧
        (∀ (r : R) (a : tangentFunctionals R C (Bialgebra.counitAlgHom R C)),
          P (r • a) = r ^ p • P a) ∧
        (∀ a b : tangentFunctionals R C (Bialgebra.counitAlgHom R C),
          B (P a) b = Nat.iterate (B a) p b) ∧
        (∀ a b : tangentFunctionals R C (Bialgebra.counitAlgHom R C),
          WithConv.toConv (P (a + b)).1 =
            WithConv.toConv (P a).1 + WithConv.toConv (P b).1 +
              ∑ i ∈ Finset.Ico 1 p,
                @LieAlgebra.restrictedJacobsonTerm k _ (WithConv (C →ₗ[R] R))
                  LieRing.ofAssociativeRing inferInstance p
                  (WithConv.toConv a.1) (WithConv.toConv b.1) i) ∧
        (∀ (C' : Type w') [CommRing C'] [Bialgebra R C'] (f : C →ₐc[R] C'),
          ∃ T : tangentFunctionals R C' (Bialgebra.counitAlgHom R C') →ₗ[R]
              tangentFunctionals R C (Bialgebra.counitAlgHom R C),
            (∀ a : tangentFunctionals R C' (Bialgebra.counitAlgHom R C'),
              (T a).1 = a.1.comp (f : C →ₗ[R] C')) ∧
            (∀ a b : tangentFunctionals R C' (Bialgebra.counitAlgHom R C'),
              (B (T a) (T b)).1 =
                ((WithConv.toConv a.1 * WithConv.toConv b.1 -
                  WithConv.toConv b.1 * WithConv.toConv a.1).ofConv).comp
                    (f : C →ₗ[R] C')) ∧
            (∀ a : tangentFunctionals R C' (Bialgebra.counitAlgHom R C'),
              (P (T a)).1 = (WithConv.toConv a.1 ^ p).ofConv.comp
                (f : C →ₗ[R] C')))) ∧
    (∃ E : tangentFunctionals R C (Bialgebra.counitAlgHom R C) ≃
        {g : C →ₐ[R] DualNumber R //
          (TrivSqZeroExt.fstHom R R R).comp g = Bialgebra.counitAlgHom R C},
      (∀ (a : tangentFunctionals R C (Bialgebra.counitAlgHom R C)) (c : C),
        (E a).1 c = TrivSqZeroExt.inl (Coalgebra.counit (R := R) c) +
          TrivSqZeroExt.inr (a.1 c)) ∧
      ∀ (A : Type w') [CommRing A] [Algebra R A] (ε : A →ₐ[R] R)
        (f : A →ₐ[R] C), (Bialgebra.counitAlgHom R C).comp f = ε →
        ∃ T : tangentFunctionals R C (Bialgebra.counitAlgHom R C) →ₗ[R]
            tangentFunctionals R A ε,
          (∀ a : tangentFunctionals R C (Bialgebra.counitAlgHom R C),
            (T a).1 = a.1.comp f.toLinearMap) ∧
          ∀ (a : tangentFunctionals R C (Bialgebra.counitAlgHom R C)) (x : A),
            ((E a).1.comp f) x = TrivSqZeroExt.inl (ε x) +
              TrivSqZeroExt.inr ((T a).1 x)) := by
  sorry

end RelativeBialgebra
