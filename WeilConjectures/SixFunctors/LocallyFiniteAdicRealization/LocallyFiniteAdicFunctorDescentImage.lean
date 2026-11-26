/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicNormalizedFunctorData
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.NativeIntegralTensorConstructible
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.CondensedFiniteIntegralTensorModel
import WeilConjectures.AlgebraicGeometry.NativeEncoding.NativeAdicEncodingConstructible
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting

/-! # Essential image descent for a normalized locally finite adic functor

The essential image of the normalized locally finite adic functor consists exactly of the
bounded adic constructible objects.

## Implementation details

Bounded native constructible objects are identified with the condensed module category via the
internal-module and section-module equivalences and the finite-field local-freeness theorems.
The object clause of `constructibleCocone_isFilteredTwoColimit` descends a condensed object to a
finite field; essential surjectivity of the finite-field realization lifts that model to a
source object, and tensor transitivity identifies its normalized image with the original object.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Proposition 6.8.14(1),(2)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

attribute [local irreducible] sections CoefficientPresentation.integralMap
  completedTensorComparison

/-- Bounded adic constructibility is exactly the essential image of the normalized functor. -/
theorem normalizedFunctor_descent_image
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] (D : NormalizedFunctor l X) :
    ∀ K, ProEtale.DerivedCategory.boundedAdicConstructible l X K ↔
      ∃ A, Nonempty (D.J.obj A ≅ K) := by
  have := D.commutative
  have := D.sectionsAdditive
  have := D.sectionsLimits
  have := D.sectionsColimits
  have : (ProEtale.AdicSheaf.forgetAb l X).IsEquivalence :=
    ProEtale.nativeScalarForgetting_isEquivalence l X
  have : (sections l X).IsEquivalence := by
    unfold sections
    infer_instance
  let S := (sections l X).mapDerivedCategory
  let F := ProEtale.NativeEncoding.derivedEncoding l X
  intro K
  constructor
  · intro hK
    have hc := ProEtale.NativeEncoding.encoding_boundedConstructible l X K hK
    obtain ⟨E, M, ⟨e⟩⟩ := ProEtale.constructibleCocone_essSurjObj X l ⟨F.obj K, hc⟩
    have em : (ProEtale.derivedExtendScalarsToPadicAlgCl X l E).obj M.obj ≅ F.obj K :=
      (ObjectProperty.ι (ProEtale.boundedConstructible
        (ProEtale.padicAlgClRingObj X l))).mapIso e
    obtain ⟨L, ⟨eL⟩⟩ := condensedFinite_integralTensor_model l X E (D.coefficient E) M
    have ex : F.inv.obj
        ((ProEtale.derivedExtendScalarsToPadicAlgCl X l E).obj M.obj) ≅ K :=
      F.inv.mapIso em ≪≫ (F.asEquivalence.unitIso.app K).symm
    refine ⟨(GeneralAlgebraicallyClosedCoefficients.inclusion E).obj
      ((sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj L),
      ⟨S.preimageIso ((D.integral E).app L ≪≫ eL ≪≫ S.mapIso ex)⟩⟩
  · rintro ⟨⟨E, ⟨L⟩⟩, ⟨e⟩⟩
    exact nativeIntegralTensor_constructible l X E (D.coefficient E) L K
      (S.mapIso e.symm ≪≫ (D.integral E).app L)

end WeilConjectures.LocallyFiniteAdicRealization
