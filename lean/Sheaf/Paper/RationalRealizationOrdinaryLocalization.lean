/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y5
-/
module

public import Sheaf.Paper.RationalModuleRealizationFunctor
public import Sheaf.Paper.RationalContinuousCoefficientDerivedLocalization

/-!
# Ordinary coefficient comparison for normalized rational realization

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The standard localization action, with the scheme module abbreviation in its type.
This is the existing constant-section action, with no change of scalar structure.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-rational-realization-ordinary-localization). -/
@[instance_reducible]
def rationalLocalizationModulesLinear (Y : Scheme.{u})
    (A : Type (u + 1)) [CommRing A]
    (B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (a : A →+* RingCat.sectionsSubring (B.obj ⋙ forget₂ CommRingCat RingCat)) (t : A) :
    Linear (Localization.Away t) (pbcModules Y
      (ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} B (a t))) :=
  scalarLocalizationCoefficientLinearOfUniverses (Localization.Away t)
    (ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} B (a t))
    (scalarLocalizationCoefficientMapOfUniverses A B a t)

attribute [local irreducible] pbcIntegralDatum pbcRationalCoefficientEquiv
  ringedLocalizationRingOfUniverses ringedLocalizationRingUnitOfUniverses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The ordinary coefficient presentation agrees with standard sheaf localization.
This assertion concerns module sheaves and ordinary tensor extension only.

Source: Bhatt--Scholze, Proposition 6.8.14(2), pp. 61--62; coefficient-presentation
transport in steps 2--3 of lem-per-rational-realization-hom-transport.
(blueprint: lem-per-rational-realization-ordinary-localization).

Proof: compare the completed ring with continuous integral functions using R.integralIso.
Its quotient normalizations identify constant sections: compose with every finite quotient
projection and use R.finite_normalization and R.integral_normalization. Localization of
this isomorphism, followed by R.localizationIso, identifies the sheafified localization
of the completed ring with the continuous rational ring. R.localization_normalization
and R.inclusion_normalization identify the localization unit with the prescribed map
R.integralIso.hom followed by R.inclusion. Equality on integral numerators extends to
fractions because the image of the uniformizer is invertible. This is an identity of
sheaves, so denominators may vary locally; no uniform denominator condition is needed.
Let G be restriction of scalars along the inverse of this ring-sheaf isomorphism. Its
inverse is restriction along the forward isomorphism. Both functors preserve underlying
abelian sheaves, so G is additive and is an equivalence. Its scalar action agrees with
the restriction of the normalized E-action: on integral coefficients this is the
constant-section equality, and invertibility gives the equality on every fraction via
the canonical valuation-ring localization equivalence and R.scalar_normalization.
Finally, the usual tensor/change-of-rings comparison gives F followed by G isomorphic
to ordinary tensor extension along R.integralIso.hom followed by R.inclusion. On local
pure tensors the comparison sends s tensor m to the image of s tensor m; its inverse
uses the inverse ring map. The balancing relations hold by the coefficient-unit square,
and the two composites fix pure tensors. These maps sheafify and are natural in the
module. This includes the empty scheme and zero or torsion modules. -/
theorem rationalRealizationOrdinaryLocalization (R : RationalModuleRealization l E X) :
    let B := pbcAdicCompletion X (pbcIntegralDatum l E)
    let a := pbcCompletedScalarSections X (pbcIntegralDatum l E)
    let t := pbcUniformizer l E
    let S := ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} B (a t)
    letI := R.moduleLinear
    (fun [_localizedLinear : Linear (Localization.Away t)
        (pbcModules X S)] ↦
      ∀ (F : pbcModules X B ⥤ pbcModules X S)
        (hF : ∀ M, F.obj M =
          SheafOfModules.changeOfRingsOfUniverses
            (ringedLocalizationRingUnitOfUniverses.{u + 1, u + 1, u} B (a t)) M)
        (_hmap : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hF M) ≫
          SheafOfModules.changeOfRingsHomOfUniverses
            (ringedLocalizationRingUnitOfUniverses.{u + 1, u + 1, u} B (a t)) M f ≫
            eqToHom (hF N).symm),
        ∃ (G : pbcModules X S ⥤ pbcModules X (rationalCoefficientSheaf l X E)),
          G.IsEquivalence ∧ G.Additive ∧
          (∀ {K L} (f : K ⟶ L) (r : Localization.Away t),
            G.map (r • f) = pbcRationalCoefficientEquiv l E r • G.map f) ∧
          Nonempty (F ⋙ G ≅ pbcExtend (R.integralIso.hom ≫ R.inclusion)))
      (_localizedLinear := rationalLocalizationModulesLinear X (PbcIntegralRing l E)
        B a t) := by sorry

end AlgebraicGeometry.Scheme
