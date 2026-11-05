/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor

/-! # Units and composition of finite coefficient extension

Source: blueprint proper base change, order 1307; Milne, Section 19.
Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.
(blueprint: lem-pbc-scalar-tensor-composition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime]
variable (E F G : Type u) [Field E] [Field F] [Field G]
variable [Algebra (Padic l) E] [Algebra (Padic l) F] [Algebra (Padic l) G]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable [FiniteDimensional (Padic l) G]
variable (i : E →ₐ[Padic l] F) (j : F →ₐ[Padic l] G) (T : Scheme.{u})

/-- The ambient associator is the adjunction-normalized balanced tensor comparison.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-tensor-composition). -/
@[irreducible] def pbcAmbientScalarComp :
    pbcEmbeddingAmbientTensor l E F i T ⋙ pbcEmbeddingAmbientTensor l F G j T ≅
      pbcEmbeddingAmbientTensor l E G (j.comp i) T :=
  NatIso.ofComponents
    (pbcReductionNormalization (pbcScalarCoefficientMap l E F i T)
      (pbcScalarCoefficientMap l F G j T) (pbcScalarCoefficientMap l E G (j.comp i) T)
      (pbcScalarCoefficientMap_comp l E F G i j T))
    (fun f ↦ pbcAmbientScalarComp_naturality l E F G i j T _ _ f)

variable [IsNoetherian T] (hDim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
variable (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

section
attribute [-instance] ULift.module
attribute [local irreducible] pbcRationalScalarHom
end

/-- The specified natural rational associator before literal-unit normalization.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-tensor-composition). -/
@[irreducible] def pbcRationalScalarComp :
    pbcRationalScalarExtension l E F i T hDim hInv ⋙
        pbcRationalScalarExtension l F G j T hDim hInv ≅
      pbcRationalScalarExtension l E G (j.comp i) T hDim hInv :=
  NatIso.ofComponents (pbcRationalScalarCompComponent l E F G i j T hDim hInv)
    (fun f ↦ pbcRationalScalarComp_naturality l E F G i j T hDim hInv _ _ f)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
section Units
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The ordinary identity-on-sections restriction comparison.
Source: Stacks 03DA (blueprint: lem-pbc-scalar-tensor-composition). -/
@[irreducible] def pbcScalarRestrictId := (pbcScalarRestrictId_exists l E T).exists.choose

/-- The canonical tensor unit is conjugate to identity restriction under the
ordinary-unit-normalized derived adjunction.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-tensor-composition). -/
@[irreducible] def pbcEmbeddingAmbientUnit :
    pbcEmbeddingAmbientTensor l E E (AlgHom.id (Padic l) E) T ≅ 𝟭 _ :=
  eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ) (pbcScalarCoefficientMap_id l E T)) ≪≫
    ((conjugateIsoEquiv
      (pbcDerivedScalarAdjunction (𝟙 (pbcAdicCompletion T (pbcIntegralDatum l E))))
      (Adjunction.id : (𝟭 (PbcCompletedDerived T (pbcIntegralDatum l E))) ⊣ 𝟭 _)).symm
        (Functor.mapDerivedCategoryNatIso (pbcScalarRestrictId l E T) ≪≫
          Functor.mapDerivedCategoryIdIso _)).symm

variable [IsNoetherian T]
variable (hDim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
variable (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

section
attribute [-instance] ULift.module
attribute [local irreducible] pbcRationalScalarHom

end

/-- The natural rational tensor unit, before choosing literal identity transitions.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-tensor-composition). -/
@[irreducible] def pbcRationalScalarUnit :
    pbcRationalScalarExtension l E E (AlgHom.id (Padic l) E) T hDim hInv ≅ 𝟭 _ :=
  NatIso.ofComponents (pbcRationalScalarUnitComponent l E T hDim hInv)
    (fun f ↦ pbcRationalScalarUnit_naturality l E T hDim hInv _ _ f)
end Units
end AlgebraicGeometry.Scheme
