/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
import WeilConjectures.SmoothPurity.CompletedScalarAssociator.CompletedScalarAssociator
import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedScalarIdentityUnit
import WeilConjectures.SixFunctors.Finite.FiniteFreeScalarCochainProperties
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison

/-! # Ordinary scalar associators and units for completed coefficients

Source: Stacks 06YY, 07A4; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).

The ordinary (uncompleted) derived scalar extensions along completed coefficient maps
carry an associator and a multiplication unitor, each fixed by its pure-tensor formula
and the universal K-flat counits. This file records them and proves their two unit laws
and the pentagon. The completed comparisons are obtained from them by conjugation in
`CompletedLineTensorCoherence`.

## Main definitions and statements

* `associatorData`, `ordinaryUnit`: the normalized ordinary associator and unitor.
* `associatorData_derived_source_unit`, `associatorData_derived_target_unit`:
  the two unit laws.
* `associatorData_derived_pentagon`: the pentagon.
-/

@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
attribute [local instance 5000] Algebra.toModule
attribute [local irreducible] Padic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace WeilConjectures
namespace CompletedLineTensor

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses
  completedScalarChangeData completedOrdinaryScalarComplex

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)
variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)


/-- Ordinary scalar associativity, fixed on sheafified tensors and universal K-flat counits.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def AssociatorData :=
  (completedOrdinaryScalarExtension l E F ι X ⋙
    completedOrdinaryScalarExtension l F G j X ≅
      completedOrdinaryScalarExtension l E G (j.comp ι) X) ×
  (completedDerivedScalarExtension l E F ι X ⋙
    completedDerivedScalarExtension l F G j X ≅
      completedDerivedScalarExtension l E G (j.comp ι) X)

variable {l E X F ι G j}

/-- Projection of the canonical ordinary comparison package.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def AssociatorData.sheaf (d : AssociatorData l E X F ι G j) :
    completedOrdinaryScalarExtension l E F ι X ⋙
    completedOrdinaryScalarExtension l F G j X ≅
      completedOrdinaryScalarExtension l E G (j.comp ι) X := d.1

/-- Projection of the canonical ordinary comparison package.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def AssociatorData.derived (d : AssociatorData l E X F ι G j) :
    completedDerivedScalarExtension l E F ι X ⋙
    completedDerivedScalarExtension l F G j X ≅
      completedDerivedScalarExtension l E G (j.comp ι) X := d.2

variable (l E X F ι G j)

/-- Balanced-tensor multiplication and the universal-counit normalization.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def IsAssociatorNormalized (d : AssociatorData l E X F ι G j) : Prop :=
  (∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U)
      (x : M.val.obj U),
    (d.sheaf.hom.app M).val.app U
        (completedScalarTensorSection l F G j X _ U t
          (completedScalarTensorSection l E F ι X M U s x)) =
      completedScalarTensorSection l E G (j.comp ι) X M U
        (t * (completedCoefficientMap l F G j X).hom.app U s) x) ∧
  (∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
    (completedDerivedScalarExtension l F G j X).map (completedScalarCounit l E F ι X P.obj) ≫
        completedScalarCounit l F G j X ((completedOrdinaryScalarComplex l E F ι X).obj P.obj) ≫
        DerivedCategory.Q.map
          ((scalarAssociatorComplex l E X F ι G j d.sheaf).hom.app P.obj) =
      d.derived.hom.app (DerivedCategory.Q.obj P.obj) ≫
        completedScalarCounit l E G (j.comp ι) X P.obj)

/-- Ordinary scalar associators with exactly the prescribed balanced normalization.
Source: Stacks 06YY, 07A4; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the balanced map t tensor (s tensor x) mapped to t*j(s) tensor x has inverse
u tensor x mapped to u tensor (1 tensor x). The two maps commute with restrictions
and differentials. Sheafification preserves their inverse equations. Ordinary extension
preserves flat-term K-flat complexes, so localization with the specified counits gives
the unique derived comparison. Local generation and the localization equivalence prove
uniqueness of the entire package. -/
theorem associatorData_existsUnique :
    ∃! a : AssociatorData l E X F ι G j, IsAssociatorNormalized l E X F ι G j a := by
  delta AssociatorData IsAssociatorNormalized AssociatorData.sheaf
    AssociatorData.derived scalarAssociatorComplex
  exact CompletedScalarAssociator.exists_unique l E X F ι G j

/-- The normalized ordinary scalar associator, including its representative.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def associatorData : AssociatorData l E X F ι G j :=
  (associatorData_existsUnique l E X F ι G j).exists.choose

section DerivedUnitProof

/-- The ordinary derived multiplication unitor, fixed by the recorded chain unitor.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: multiplication and x mapped to 1 tensor x are inverse on module sheaves.
They commute with differentials and restrictions. Localization with the canonical
K-flat counit gives the unique derived unitor with the displayed normalization. -/
theorem ordinaryUnit_existsUnique :
    ∃! e : completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X ≅ 𝟭 _,
      ∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
        e.hom.app (DerivedCategory.Q.obj P.obj) =
          completedScalarCounit l E E (AlgHom.id ℚ_[l] E) X P.obj ≫
            DerivedCategory.Q.map ((completedScalarIdentityMultiplication l E X).hom.app P.obj) :=
              by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨e, he⟩ := ordinaryUnitOnComplexes_exists l E X
    refine ⟨e, fun P ↦ he P.obj, ?_⟩
    intro e' he'
    let Q := integralOperationsGoodLocalization l E X
    let W := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E X).ι
    have : Q.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E X
    apply Iso.ext
    apply (Localization.fullyFaithfulWhiskeringLeft Q W _).map_injective
    apply NatTrans.ext
    funext P
    exact (he' P).trans (he P.obj).symm

end DerivedUnitProof

/-- The ordinary multiplication unitor with its prescribed representative.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def ordinaryUnit :
    completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X ≅
      𝟭 (DerivedCategory (integralTowerModules l E X)) :=
  (ordinaryUnit_existsUnique l E X).exists.choose

attribute [local irreducible] associatorData ordinaryUnit

/-- The derived associator normalization holds on every complex, not only on good ones.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the normalized associator is the one built from the composed extension-restriction
adjunctions, whose representative formula holds on all complexes; uniqueness identifies
it with `associatorData`. -/
theorem associatorData_derived_normalized
    (P : CochainComplex (integralTowerModules l E X) ℤ) :
    (completedDerivedScalarExtension l F G j X).map (completedScalarCounit l E F ι X P) ≫
        completedScalarCounit l F G j X ((completedOrdinaryScalarComplex l E F ι X).obj P) ≫
        DerivedCategory.Q.map
          ((scalarAssociatorComplex l E X F ι G j (associatorData l E X F ι G j).sheaf).hom.app P) =
      (associatorData l E X F ι G j).derived.hom.app (DerivedCategory.Q.obj P) ≫
        completedScalarCounit l E G (j.comp ι) X P := by
  sorry

/-- The ordinary unitor is multiplication after the universal counit, on every complex.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: `ordinaryUnitOnComplexes_exists` gives a unitor with this formula on all complexes;
it satisfies the good-complex normalization, so it is `ordinaryUnit` by uniqueness. -/
theorem ordinaryUnit_hom_app_Q (P : CochainComplex (integralTowerModules l E X) ℤ) :
    (ordinaryUnit l E X).hom.app (DerivedCategory.Q.obj P) =
      completedScalarCounit l E E (AlgHom.id ℚ_[l] E) X P ≫
        DerivedCategory.Q.map ((completedScalarIdentityMultiplication l E X).hom.app P) := by
  sorry


/-- The ordinary associator with an identity first step is the extension of the unitor.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: on pure tensors both sheaf maps send t tensor (s tensor x) to t*s tensor x.
The universal counits are invertible for finite free extensions, so the derived
equation follows from the chain equation on good complexes and localization. -/
theorem associatorData_derived_source_unit (K : DerivedCategory (integralTowerModules l E X)) :
    (associatorData l E X E (AlgHom.id ℚ_[l] E) F ι).derived.hom.app K =
      (completedDerivedScalarExtension l E F ι X).map ((ordinaryUnit l E X).hom.app K) := by
  sorry

/-- The ordinary associator with an identity second step is the unitor.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: on pure tensors both sheaf maps send t tensor (s tensor x) to t*s tensor x.
Invertible universal counits and localization give the derived equation. -/
theorem associatorData_derived_target_unit (K : DerivedCategory (integralTowerModules l E X)) :
    (associatorData l E X F ι F (AlgHom.id ℚ_[l] F)).derived.hom.app K =
      (ordinaryUnit l F X).hom.app ((completedDerivedScalarExtension l E F ι X).obj K) := by
  sorry

/-- The ordinary associators satisfy the pentagon.
Source: Stacks 06YY, 07A4; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: for three transitions both routes send u tensor (t tensor (s tensor x)) to
u*k(t)*k(j(s)) tensor x. Ordinary extension preserves good complexes and its universal
counits are invertible, so the counit normalizations transport this chain identity to
the derived pentagon on good complexes; localization concludes. -/
theorem associatorData_derived_pentagon
    (H : Type u) [Field H] [Algebra ℚ_[l] H] [FiniteDimensional ℚ_[l] H]
    (k : G →ₐ[ℚ_[l]] H) (K : DerivedCategory (integralTowerModules l E X)) :
    (completedDerivedScalarExtension l G H k X).map
        ((associatorData l E X F ι G j).derived.hom.app K) ≫
      (associatorData l E X G (j.comp ι) H k).derived.hom.app K =
    (associatorData l F X G j H k).derived.hom.app
        ((completedDerivedScalarExtension l E F ι X).obj K) ≫
      (associatorData l E X F ι H (k.comp j)).derived.hom.app K := by
  sorry

end CompletedLineTensor
end WeilConjectures
