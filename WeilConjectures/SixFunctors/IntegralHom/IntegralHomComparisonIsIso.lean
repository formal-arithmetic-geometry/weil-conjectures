/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomComparisonRepresentative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Invertibility of the normalized integral Hom comparison

## References

* [Stacks, Tag 093M]
* [Stacks, Tag 06YQ]
* [Stacks, Tag 08J7]
* [Stacks, Tag 0A8X]
* [Stacks, Tag 07A6]
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

-- Use the existing sheafification at the coefficient universe for this declaration.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The specified transpose of reduced evaluation is invertible for arbitrary
inputs. The presentation hypotheses only specify the normalized tensor models. -/
theorem comparison_isIso
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (K L : completedIntegralDerivedCategory l E Y D hl) :
    IsIso (comparison l E Y D hl m K L) := by
  let U := scalarReductionRestriction l E Y n
  have : PreservesFiniteLimits U := scalarReductionRestrictionLimits l E Y n
  have : PreservesFiniteColimits U := scalarReductionRestrictionColimits l E Y n
  let V := SheafOfModules.toSheaf (completedIntegralCoefficientSheaf l E Y D hl)
  have : (U ⋙ V).ReflectsIsomorphisms :=
    inferInstanceAs (SheafOfModules.toSheaf
      (integralCoefficientSheaf l E Y n)).ReflectsIsomorphisms
  have : U.ReflectsIsomorphisms := reflectsIsomorphisms_of_comp U V
  obtain ⟨P, I, Q, _, _, _, _, hzero, eNeg, eZero, f, hf, s, t, h⟩ :=
    comparison_representative l E Y D hl a n m K L
  have (j : ℤ) : IsIso (f.f j) :=
    twoTermFreeHomTensor_component_isIso Y _ P I Q hzero eNeg eZero f hf j
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  have hmap : IsIso ((scalarReductionDerivedRestriction l E Y n).map
      (comparison l E Y D hl m K L)) := by
    have : IsIso ((scalarReductionDerivedRestriction l E Y n).map
        (comparison l E Y D hl m K L) ≫ t.hom) := by
      rw [h]
      infer_instance
    exact (isIso_comp_right_iff _ t.hom).mp this
  rw [DerivedCategory.isIso_iff]
  intro j
  have : IsIso (U.map ((DerivedCategory.homologyFunctor _ j).map
      (comparison l E Y D hl m K L))) :=
    (NatIso.isIso_map_iff (U.mapDerivedCategoryHomologyFunctorIso j) _).2
      (by change IsIso ((DerivedCategory.homologyFunctor _ j).map
            ((scalarReductionDerivedRestriction l E Y n).map
              (comparison l E Y D hl m K L)))
          infer_instance)
  exact isIso_of_reflects_iso _ U

end WeilConjectures.IntegralHom
