/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedIntegralModel
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCoefficientSystem
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedCoefficientSquare

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicAmbientChiComparison

/-! # The raw ambient comparison is the completion map

The quotient-normalized coefficient isomorphisms intertwine the completed scalar map of the
finite coefficient stages with the completed coefficient map. The ambient comparison of a
completion-integral comparison is the specified completion map, transported along the tensor
comparison through this coefficient square.

## Main statements

* `AlgebraicGeometry.Scheme.purCoefficientIso_hom_comp_completedCoefficientMap`: the coefficient
  square of an inclusion of finite coefficient fields.
* `WeilConjectures.AdicFiniteRealization.FiniteCondensedData.rawComparison_hom_app`: the ambient
  comparison of the raw integral data is the transported completion map.

## Implementation details

The raw ambient comparison satisfies the quotient-cocone equation chi, which fixes it
(`WeilConjectures.heq_tensorThroughCoefficientSquare_of_chi`). Its ordinary scalar transport is
fixed on the unit tensor generators. The presentations `pbcFiniteField` and `Coefficient` of the
finite coefficient fields are identified once, by
`tensorThroughCoefficientSquare_completedTensorComparison_heq`, so that the two are never
unfolded against each other.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.8.2 and
  Proposition 6.8.14(2)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w u
open CategoryTheory
open WeilConjectures.LocallyFiniteAdicRealization

namespace WeilConjectures.AdicFiniteRealization

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicallyClosedCoefficients

/-- The completed scalar map of finite coefficient stages, between the completed coefficients
of the coefficient fields of the fixed closure. This is `pbcCompletedScalarMap`, retyped with the
coefficient fields `Coefficient E` and `Coefficient L`. -/
def coefficientCompletedScalarMap (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    pbcAdicCompletion X (pbcIntegralDatum l (Coefficient.{u} l (PadicAlgCl l) E)) ⟶
      pbcAdicCompletion X (pbcIntegralDatum l (Coefficient.{u} l (PadicAlgCl l) L)) :=
  pbcCompletedScalarMap l (PadicAlgCl l) X h

/-- The completed coefficient square of an inclusion of coefficient fields of the fixed
closure. -/
theorem purCoefficientIso_hom_comp_completedCoefficientMap_index (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) E) X).hom ≫
        completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) X =
      coefficientCompletedScalarMap l X h ≫
        (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) L) X).hom :=
  purCoefficientIso_hom_comp_completedCoefficientMap l (PadicAlgCl l) X h

section Presentation

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

/-- The tensor comparison through a coefficient square, followed by the completion map, does not
depend on the presentation of the coefficient fields. -/
theorem tensorThroughCoefficientSquare_inv_app_comp_heq {E₁ E₂ L₁ L₂ : Type u}
    [f₁ : Field E₁] [f₂ : Field E₂] [g₁ : Field L₁] [g₂ : Field L₂]
    [a₁ : Algebra ℚ_[l] E₁] [a₂ : Algebra ℚ_[l] E₂] [b₁ : Algebra ℚ_[l] L₁] [b₂ : Algebra ℚ_[l] L₂]
    [FiniteDimensional ℚ_[l] E₁] [FiniteDimensional ℚ_[l] E₂]
    [FiniteDimensional ℚ_[l] L₁] [FiniteDimensional ℚ_[l] L₂]
    (hE : E₁ = E₂) (hL : L₁ = L₂) (hf : HEq f₁ f₂) (hg : HEq g₁ g₂) (ha : HEq a₁ a₂)
    (hb : HEq b₁ b₂) (i₁ : E₁ →ₐ[ℚ_[l]] L₁) (i₂ : E₂ →ₐ[ℚ_[l]] L₂) (hi : HEq i₁ i₂)
    (s₁ : pbcAdicCompletion X (pbcIntegralDatum l E₁) ⟶ pbcAdicCompletion X (pbcIntegralDatum l L₁))
    (s₂ : pbcAdicCompletion X (pbcIntegralDatum l E₂) ⟶ pbcAdicCompletion X (pbcIntegralDatum l L₂))
    (hs : HEq s₁ s₂)
    (sq₁ : (purCoefficientIso l E₁ X).hom ≫ completedCoefficientMap l E₁ L₁ i₁ X =
      s₁ ≫ (purCoefficientIso l L₁ X).hom)
    (sq₂ : (purCoefficientIso l E₂ X).hom ≫ completedCoefficientMap l E₂ L₂ i₂ X =
      s₂ ≫ (purCoefficientIso l L₂ X).hom)
    (K₁ : DerivedCategory (integralTowerModules.{u, u} l E₁ X))
    (K₂ : DerivedCategory (integralTowerModules.{u, u} l E₂ X)) (hK : HEq K₁ K₂) :
    HEq ((tensorThroughCoefficientSquare X (purCoefficientIso l E₁ X) (purCoefficientIso l L₁ X) s₁
        (completedCoefficientMap l E₁ L₁ i₁ X) sq₁).inv.app K₁ ≫
        (pbcDerivedRestrict (purCoefficientIso l L₁ X).hom).map
          ((completedTensorComparison l X E₁ L₁ i₁).app K₁))
      ((tensorThroughCoefficientSquare X (purCoefficientIso l E₂ X) (purCoefficientIso l L₂ X) s₂
        (completedCoefficientMap l E₂ L₂ i₂ X) sq₂).inv.app K₂ ≫
        (pbcDerivedRestrict (purCoefficientIso l L₂ X).hom).map
          ((completedTensorComparison l X E₂ L₂ i₂).app K₂)) := by
  subst hE hL
  cases hf
  cases hg
  cases ha
  cases hb
  cases hi
  cases hs
  cases hK
  rfl
/-- The transported completion map in the presentation `pbcFiniteField` of the finite
coefficient fields is the one in the presentation `Coefficient`. -/
theorem tensorThroughCoefficientSquare_completedTensorComparison_heq
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    HEq ((tensorThroughCoefficientSquare X
        (purCoefficientIso l (pbcFiniteField.{u} l (PadicAlgCl l) E) X)
        (purCoefficientIso l (pbcFiniteField.{u} l (PadicAlgCl l) L) X)
        (pbcCompletedScalarMap l (PadicAlgCl l) X h)
        (completedCoefficientMap l (pbcFiniteField.{u} l (PadicAlgCl l) E)
          (pbcFiniteField.{u} l (PadicAlgCl l) L) (pbcFiniteFieldInclusion l (PadicAlgCl l) h) X)
        (purCoefficientIso_hom_comp_completedCoefficientMap l (PadicAlgCl l) X h)).inv.app K.obj ≫
        (pbcDerivedRestrict (purCoefficientIso l (pbcFiniteField.{u} l (PadicAlgCl l) L) X).hom).map
          ((completedTensorComparison l X (pbcFiniteField.{u} l (PadicAlgCl l) E)
            (pbcFiniteField.{u} l (PadicAlgCl l) L)
              (pbcFiniteFieldInclusion l (PadicAlgCl l) h)).app K.obj))
      ((tensorThroughCoefficientSquare X
          (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) E) X)
          (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) L) X)
          (coefficientCompletedScalarMap l X h)
          (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) X)
          (purCoefficientIso_hom_comp_completedCoefficientMap_index l X h)).inv.app
          ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι.obj K) ≫
        (pbcDerivedRestrict (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) L) X).hom).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)).app
              ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι.obj K))) := by
  refine tensorThroughCoefficientSquare_inv_app_comp_heq
    (E₁ := pbcFiniteField.{u} l (PadicAlgCl l) E)
    (E₂ := Coefficient.{u} l (PadicAlgCl l) E) (L₁ := pbcFiniteField.{u} l (PadicAlgCl l) L)
    (L₂ := Coefficient.{u} l (PadicAlgCl l) L) rfl rfl ?_ ?_ ?_ ?_
    (pbcFiniteFieldInclusion l (PadicAlgCl l) h) (coefficientInclusion l (PadicAlgCl l) E L h) ?_
    (pbcCompletedScalarMap l (PadicAlgCl l) X h) (coefficientCompletedScalarMap l X h) ?_
    (purCoefficientIso_hom_comp_completedCoefficientMap l (PadicAlgCl l) X h)
    (purCoefficientIso_hom_comp_completedCoefficientMap_index l X h) K.obj
    ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι.obj K) ?_
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl

end Presentation

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}} [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)] [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The ambient comparison of the raw integral data is the specified completion map, transported
along the tensor comparison through the coefficient square. -/
theorem FiniteCondensedData.rawComparison_hom_app (A : FiniteCondensedData l X)
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    (A.raw.integral.comparison h).hom.app K ≍
      (tensorThroughCoefficientSquare X (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) E) X)
          (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) L) X)
          (coefficientCompletedScalarMap l X h)
          (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) X)
          (purCoefficientIso_hom_comp_completedCoefficientMap_index l X h)).inv.app
          ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι.obj K) ≫
        (pbcDerivedRestrict (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) L) X).hom).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)).app
              ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι.obj K)) := by
  have key := heq_tensorThroughCoefficientSquare_of_chi h
    (integralDetailedCoefficientComparison X l (pbcFiniteField.{u} l (PadicAlgCl l) E))
    (purCoefficientIso_existsUnique l (pbcFiniteField.{u} l (PadicAlgCl l) E) X).exists.choose_spec
    (integralDetailedCoefficientComparison X l (pbcFiniteField.{u} l (PadicAlgCl l) L))
    (purCoefficientIso_existsUnique l (pbcFiniteField.{u} l (PadicAlgCl l) L) X).exists.choose_spec
    (h₀l := (integralDetailedCoefficientRestriction_exact X l _).1)
    (h₀c := (integralDetailedCoefficientRestriction_exact X l _).2)
    (h₁l := (integralDetailedCoefficientRestriction_exact X l _).1)
    (h₁c := (integralDetailedCoefficientRestriction_exact X l _).2)
    (A.raw.integral.ordinary h).comparison ?_ (A.raw.integral.comparison h) ?_ K
  · exact key.trans (tensorThroughCoefficientSquare_completedTensorComparison_heq h K)
  · intro M U x
    have hg := (A.raw.integral.ordinary h).generators M U 1 x
    refine hg.trans ?_
    congr 1
    exact map_one _
  · intro P hP
    refine (eq_of_heq (A.raw.integral.chi h P hP)).trans ?_
    refine congrArg (fun t ↦ _ ≫ _ ≫ DerivedCategory.Q.map t) ?_
    rw [FdOrdinaryScalarTransport.completion]
    congr 1


end WeilConjectures.AdicFiniteRealization

namespace WeilConjectures.LocallyFiniteAdicRealization

open AlgebraicGeometry AlgebraicGeometry.Scheme AdicFiniteRealization
open scoped Obj
open AlgebraicallyClosedCoefficients (Index Coefficient)

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)] [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The continuous integral realization map, with source the completed coefficients of the
coefficient field of the fixed closure. This is the composite of `integralIso` and `inclusion` of
the realization, retyped with the coefficient field `Coefficient E`. -/
def realizationCoefficientMap (A : FiniteCondensedData l X) (E : Index l (PadicAlgCl l)) :
    pbcAdicCompletion X (pbcIntegralDatum l (Coefficient.{u} l (PadicAlgCl l) E)) ⟶
      rationalCoefficientSheaf l X (pbcFiniteField.{u} l (PadicAlgCl l) E) :=
  (A.realization E).integralIso.hom ≫ (A.realization E).inclusion

/-- The coefficient square of the continuous realization and the coefficient presentation. -/
theorem finiteOrdinaryCoefficientSquare (A : FiniteCondensedData l X)
    (C : CoefficientSystem l X) (E : Index l (PadicAlgCl l)) :
    letI := C.commutative
    letI := sectionRingMap_isIso X (condensedNativeMap l X)
    (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) E) X).hom ≫
        (C.coefficient E).integralMap l X =
      (realizationCoefficientMap l X A E ≫ A.closure.leg E) ≫
        (asIso (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X))).hom := by
  dsimp only [asIso_hom, realizationCoefficientMap]
  simp only [Category.assoc]
  exact finiteCondensedIntegralCoefficientSquare l X A E (C.coefficient E)

/-- The completed scalar square of the continuous realizations. -/
theorem coefficientCompletedScalarMap_comp_realizationCoefficientMap
    (A : FiniteCondensedData l X) {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    coefficientCompletedScalarMap l X h ≫ realizationCoefficientMap l X A L =
      realizationCoefficientMap l X A E ≫ (A.scalar.coefficient h).coefficient :=
  A.scalar.completed_square h

end WeilConjectures.LocallyFiniteAdicRealization
