/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Sf.SfClopenRestrictionData
import WeilConjectures.SixFunctors.Sf.SfClopenScalarModuleComparison
import WeilConjectures.SixFunctors.Sf.SfClopenScalarComparisonDescent
import WeilConjectures.SixFunctors.Sf.SfClopenScalarChainComparison

/-! # Scalar extension and actual quotient complexes on a clopen

Scalar extension is compatible with the actual quotient complexes on a clopen component.

## References

* [Stacks, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Normalized scalar and chain-level quotient comparisons on a clopen component.
This assertion concerns scalar extension and chain maps only: it does not assert
naturality of a derived tower, preservation of completeness, or a Tor bound. -/
theorem sf_clopen_scalar_quotient_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens)
    (hU : IsClosed (U : Set T)) (d : SfClopenCoefficientRestriction l E T U) :
    ∃ (reduction : ∀ n : ℕ,
    scalarReductionDerivedExtension l E T n ⋙ sfClopenFiniteDerivedRestriction d n ≅
      sfClopenDerivedRestriction d ⋙ scalarReductionDerivedExtension l E U.toScheme n)
       (finite_quotient : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (sfClopenFiniteComplexRestriction d n).obj (unrestrictedTowerFiniteComplex l E T n P) ≅
      unrestrictedTowerFiniteComplex l E U.toScheme n ((sfClopenComplexRestriction d).obj P))
       (quotient : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (sfClopenComplexRestriction d).obj (unrestrictedTowerComplex l E T n P) ≅
      unrestrictedTowerComplex l E U.toScheme n ((sfClopenComplexRestriction d).obj P)),
    (∀ (P : CochainComplex (scalarReductionSource l E T) ℤ)
      (n : ℕ) (q : ℤ) (V : U.toScheme.ProEt)
      (s : (integralCoefficientCommRingSheaf l E U.toScheme n).obj.obj (op V))
      (x : (P.X q).val.obj (op ((sfClopenSiteInclusion U).obj V))),
    (((finite_quotient P n).hom.f q).val.app (op V))
      (unrestrictedTowerTensorSection l E T n (P.X q)
        (op ((sfClopenSiteInclusion U).obj V)) ((d.finite n).hom.hom.app (op V) s) x) =
    unrestrictedTowerTensorSection l E U.toScheme n
      (((sfClopenComplexRestriction d).obj P).X q) (op V) s x) ∧
    (∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (sfClopenFiniteDerivedRestriction d n).map (sfClopenReductionCounit T n P) ≫
        (sfClopenFiniteLocalizationIso d n (unrestrictedTowerFiniteComplex l E T n P)).hom ≫
        DerivedCategory.Q.map (finite_quotient P n).hom =
      (reduction n).hom.app (DerivedCategory.Q.obj P) ≫
        (scalarReductionDerivedExtension l E U.toScheme n).map
          (sfClopenLocalizationIso d P).hom ≫
        sfClopenReductionCounit U.toScheme n ((sfClopenComplexRestriction d).obj P)) ∧
    (∀ (P : CochainComplex (scalarReductionSource l E T) ℤ)
      (n : ℕ) (q : ℤ) (V : U.toScheme.ProEt)
      (s : (integralCoefficientCommRingSheaf l E U.toScheme n).obj.obj (op V))
      (x : (P.X q).val.obj (op ((sfClopenSiteInclusion U).obj V))),
    (((quotient P n).hom.f q).val.app (op V))
      (unrestrictedTowerTensorSection l E T n (P.X q)
        (op ((sfClopenSiteInclusion U).obj V)) ((d.finite n).hom.hom.app (op V) s) x) =
    unrestrictedTowerTensorSection l E U.toScheme n
      (((sfClopenComplexRestriction d).obj P).X q) (op V) s x) := by
  classical
  let := fun n ↦ scalarReductionExtensionAdditive l E T n
  let := fun n ↦ scalarReductionExtensionAdditive l E U.toScheme n
  let := d.additive
  let := d.finite_additive
  choose c hc using sf_clopen_scalar_module_comparison l E T U d
  obtain ⟨quotient, hquot⟩ := sf_clopen_scalar_chain_comparison l E T U d
  choose reduction hred using fun n ↦
    sf_clopen_scalar_comparison_descent l E T U hU d n (c n)
  let finiteQuotient (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) :
      (sfClopenFiniteComplexRestriction d n).obj (unrestrictedTowerFiniteComplex l E T n P) ≅
        unrestrictedTowerFiniteComplex l E U.toScheme n ((sfClopenComplexRestriction d).obj P) :=
    (NatIso.mapHomologicalComplex (c n) (.up ℤ)).app P
  refine ⟨reduction, finiteQuotient, quotient, ?_, fun P n ↦ hred n P, ?_⟩
  · intro P n q V s x
    exact hc n (P.X q) V s x
  · exact hquot

end WeilConjectures
