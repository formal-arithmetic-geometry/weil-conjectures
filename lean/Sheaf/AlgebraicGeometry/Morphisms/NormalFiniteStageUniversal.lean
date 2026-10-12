module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.RingTheory.FiniteTypeZDomainNormalizationFinite

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- A single approximation stage has a finite normal replacement with its universal
property among normal integral factorizations dominated by `S`.

Source: Stacks Project, Tag 0EZJ, normal approximation paragraph, and Tags 035E,
035N, 035L and 0335. (blueprint: lem-sbc-normal-finite-stage-universal)

Proof: Form the scheme-theoretic image Z of the projection S -> N_i. It is integral
because S is integral, and is a closed subscheme of a finite type integer scheme.
Construct X as the normalization of Z in its own function field, by gluing the spectra
of the integral closures of affine chart rings in their fraction fields. These closures
are finite by finiteTypeZDomain_integralClosure_finite. Integral closure commutes with
localization, so the gluing gives an integral scheme with integrally closed stalks and
a finite map p to N_i. The dominant map S -> Z factors through X: the embedding of
function fields sends integral elements into the integrally closed local rings of S.
This yields a dominant alpha and alpha followed by p is the projection.
For any Y, beta and g in the conclusion, the image of g lies in Z: beta is dominant,
and Y is reduced, so the pullback of the ideal defining Z vanishes on Y. The induced
map Y -> Z is dominant since its composite with beta is S -> Z. Normality of Y
therefore gives a unique lift to X by the same integral-closure argument. Uniqueness
also shows beta followed by this lift is alpha. This proves the asserted universal
property. In particular it determines (X, alpha, p) up to unique compatible isomorphism;
no arbitrary witness of mere existence is used as the data of a definition. -/
theorem exists_normal_finite_stage_universal {S : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (N : S.NoetherianApproximation) (i : N.I) :
    ∃ (X : Scheme.{u}) (α : S ⟶ X) (p : X ⟶ N.D.obj i),
      α ≫ p = N.π.app i ∧ IsFinite p ∧ IsDominant α ∧ IsIntegral X ∧
      (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) ∧
      (∀ (Y : Scheme.{u}) (_ : IsIntegral Y)
        (_ : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
        (β : S ⟶ Y) (_ : IsDominant β) (g : Y ⟶ N.D.obj i),
        β ≫ g = N.π.app i → ∃! f : Y ⟶ X, β ≫ f = α ∧ f ≫ p = g) := by
  sorry

end AlgebraicGeometry.Scheme
