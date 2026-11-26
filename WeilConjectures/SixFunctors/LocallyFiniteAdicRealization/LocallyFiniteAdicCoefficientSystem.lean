/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRealizationData
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCoefficientPresentations
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafRing

/-! # Coefficient and section transport for the native adic realization

## References

* [Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] sections CoefficientPresentation.integralMap
  completedTensorComparison

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The coefficient part of the native realization, before any derived functor is built. -/
structure CoefficientSystem where
  [commutative : IsCommMonObj (abRing l X)]
  [sectionsAdditive : (sections l X).Additive]
  [sectionsLimits : PreservesFiniteLimits (sections l X)]
  [sectionsColimits : PreservesFiniteColimits (sections l X)]
  coefficient : ∀ E : Index l (PadicAlgCl l),
    CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)
  coefficient_scalar : ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L),
    completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) X ≫
      (coefficient L).integralMap l X = (coefficient E).integralMap l X

/-- The normalized coefficient presentations and exact section transport exist. -/
theorem coefficientSystem_exists
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Nonempty (CoefficientSystem l X) := by
  let e := ProEtale.padicAlgClSheafIsoAdicConstantSheaf X l
  haveI : IsMonHom e.hom :=
    inferInstanceAs (IsMonHom (ProEtale.padicAlgClSheafToAdicConstantSheaf X l))
  letI : IsCommMonObj (abRing l X) := by
    constructor
    apply (cancel_epi (e.hom ⊗ₘ e.hom)).mp
    rw [← Category.assoc, BraidedCategory.braiding_naturality, Category.assoc,
      ← IsMonHom.mul_hom, ← Category.assoc, IsCommMonObj.mul_comm]
  letI := ProEtale.nativeScalarForgetting_isEquivalence l X
  haveI : (sections l X).IsEquivalence := by
    unfold sections
    infer_instance
  haveI : PreservesFiniteLimits (sections l X) := inferInstance
  haveI : PreservesFiniteColimits (sections l X) := inferInstance
  haveI : (sections l X).Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨coefficient, scalar⟩ := coefficientPresentations_exists l X
  exact ⟨{ coefficient := coefficient, coefficient_scalar := scalar }⟩

end WeilConjectures.LocallyFiniteAdicRealization
