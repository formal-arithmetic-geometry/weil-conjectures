/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralScalarData
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionWellDefined
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
import all WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionWellDefined
import WeilConjectures.AlgebraicGeometry.ConnectedAdicIntegralBasis
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.BasedTensorEvaluation
import all WeilConjectures.AlgebraicGeometry.CompletedIntegralFiniteFree
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Limits.HasLimits

/-! # Finite free sections and tensor comparison at the geometric point

Source: Bhatt--Scholze, Lemma 4.2.12 (p. 30), Lemma 6.8.2(1) (pp. 58--59),
and the explicit finite-basis calculation in the DAG; Stacks, Tag 03EK
(blueprint: lem-weil-point-finite-free-sections-tensor).

The data structure spells out all clauses of the assertion. Finite products represent
finite direct sums. Tensor factors are written in the order used by change of rings,
namely scalar tensor section. All coefficient maps and sheafified tensors are the
published constructions. Site and coefficient universes are independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall


universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures

attribute [local irreducible] limit
section PublicTypes
attribute [local irreducible] completedScalarRelativeDegree integralScalarIntegerInclusion
attribute [local irreducible] Padic.coefficientExtensionIntegers

/-- The final object s to s of the small pro-etale site, with the presheaf variance.
Source: DAG statement (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeFinal (k : Type t) [Field k] :=
  op (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of k))))

variable (k : Type t) [Field k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Evaluation at the final object, transported by the displayed constant-value ring
identification. No sectionwise tensor assertion is part of this definition.
Source: DAG statement (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeEvaluation
    (e : Padic.coefficientExtensionIntegers l E ≃+*
      (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k))).obj.obj
        (pointFiniteFreeFinal k)) :=
  SheafOfModules.evaluation.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k)))
      (pointFiniteFreeFinal k) ⋙ ModuleCat.restrictScalars e.toRingHom

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Ordinary module scalar extension, using the recorded inclusion of valuation rings.
Source: DAG statement (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeModuleTensor :=
  ModuleCat.extendScalars.{u, u, max u (t + 1)} (integralScalarIntegerInclusion l E L ι)

/-- Additivity from the existing extension-restriction adjunction.
Source: Stacks 03EK (blueprint: lem-weil-point-finite-free-sections-tensor). -/
instance pointFiniteFreeModuleTensor_additive :
    (pointFiniteFreeModuleTensor.{t, u} l E L ι).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{max u (t + 1), u, u}
    (integralScalarIntegerInclusion l E L ι)).left_adjoint_additive

/-- Forget commutativity in the actual completed coefficient inclusion.
Source: DAG statement (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeRingMap :
    completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k)) ⟶
      completedIntegralCoefficientSheafUnrestricted l L (Spec (.of k)) :=
  (sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
    (forget₂ CommRingCat RingCat)).map
      (completedCoefficientMap l E L ι (Spec (.of k)))

/-- Restriction of scalars along the canonical completed coefficient inclusion.
Source: DAG statement (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeRestriction :=
  SheafOfModules.restrictScalars.{max u (t + 1)} (pointFiniteFreeRingMap k l E L ι)

/-- Restriction keeps zero maps on the underlying module sheaves.
Source: Stacks 03DA (blueprint: lem-weil-point-finite-free-sections-tensor). -/
instance pointRestriction_zero :
    (show integralTowerModules l L (Spec (.of k)) ⥤ integralTowerModules l E (Spec (.of k))
      from pointFiniteFreeRestriction k l E L ι).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- The scalar-extension evaluation functor keeps zero maps.
Source: Stacks 03EK (blueprint: lem-weil-point-finite-free-sections-tensor). -/
instance pointEvaluation_zero
    (e : Padic.coefficientExtensionIntegers l L ≃+*
      (completedIntegralCoefficientSheafUnrestricted l L (Spec (.of k))).obj.obj
        (pointFiniteFreeFinal k)) :
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙
      pointFiniteFreeEvaluation k l L e).PreservesZeroMorphisms where
  map_zero F G := by
    change ((pointFiniteFreeEvaluation k l L e).map
      ((completedOrdinaryScalarExtension l E L ι (Spec (.of k))).map (0 : F ⟶ G))) = 0
    set_option backward.isDefEq.respectTransparency false in
      rw [Functor.map_zero]
    rfl

end PublicTypes
end WeilConjectures
end

@[expose] public noncomputable section
universe a w v c
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max a w}]
  [HasSheafify J AddCommGrpCat.{max a w}]

/-- Evaluation followed by transport across a coefficient ring equivalence.
Source: Stacks 03EK (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeCoreEvaluation (R : Sheaf J CommRingCat.{w}) (one : Cᵒᵖ)
    {A : Type a} [CommRing A] (e : A ≃+* R.obj.obj one) :=
  SheafOfModules.evaluation.{max a w}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) one ⋙
      ModuleCat.restrictScalars e.toRingHom

variable (A B : Type a) [CommRing A] [CommRing B]
  (R S : Sheaf J CommRingCat.{w}) (one : Cᵒᵖ)
  (f : A →+* B) (φ : R ⟶ S) (d : ℕ)

set_option hygiene false in
local notation "rR" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
set_option hygiene false in
local notation "rS" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj S
set_option hygiene false in
local notation "ringMap" => (sheafCompose J (forget₂ CommRingCat RingCat)).map φ

variable (O : SheafOfModules.{max a w} rR ⥤ SheafOfModules.{max a w} rS) [O.Additive]
  (τ : ∀ (F : SheafOfModules.{max a w} rR) (U : Cᵒᵖ),
    S.obj.obj U → F.val.obj U → (O.obj F).val.obj U)
  (cE : ∀ U : Cᵒᵖ, A → R.obj.obj U) (cL : ∀ U : Cᵒᵖ, B → S.obj.obj U)
  (qE : (A ≃+* R.obj.obj one) → Prop) (qL : (B ≃+* S.obj.obj one) → Prop)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The explicit finite-basis sections comparison over abstract coefficient data.
Every field is a clause of the point comparison; using parameters keeps its public
projections independent of the representation of completed coefficient rings.
Source: Stacks 03EK (blueprint: lem-weil-point-finite-free-sections-tensor). -/
structure PointFiniteFreeSectionsTensorCore where
  coefficientE : A ≃+* R.obj.obj one
  coefficientL : B ≃+* S.obj.obj one
  constantE : ∀ a, coefficientE a = cE one a
  constantL : ∀ a, coefficientL a = cL one a
  quotientE : qE coefficientE
  quotientL : qL coefficientL
  coefficient_compatibility : ∀ a,
    φ.hom.app one
      (coefficientE a) = coefficientL (f a)
  basis : Fin d → B
  integral_basis : Function.Bijective
    (fun a : Fin d →
        A ↦
      ∑ i, f (a i) * basis i)
  sheafBasis :
    (SheafOfModules.restrictScalars ringMap).obj
        (SheafOfModules.unit rS) ≅
      ∏ᶜ (fun _ : Fin d ↦
        SheafOfModules.unit rR)
  sheafBasis_inverse : ∀ U x,
    sheafBasis.inv.val.app U x = ∑ i,
      φ.hom.app U
        ((Pi.π (fun _ : Fin d ↦
          SheafOfModules.unit
            rR) i).val.app U x) *
        cL U (basis i)
  coordinates : ∀ F : SheafOfModules.{max a w} rR,
    (SheafOfModules.restrictScalars ringMap).obj
        (O.obj F) ≅
      ∏ᶜ (fun _ : Fin d ↦ F)
  coordinates_tensor : ∀ (F : SheafOfModules.{max a w} rR) U a n i,
    (Pi.π (fun _ : Fin d ↦ F) i).val.app U
      ((coordinates F).hom.val.app U
        (τ F U a n)) =
      ((Pi.π (fun _ : Fin d ↦
        SheafOfModules.unit rR) i).val.app U
            (sheafBasis.hom.val.app U a)) • n
  coordinates_inverse : ∀ (F : SheafOfModules.{max a w} rR) U x,
    (coordinates F).inv.val.app U x = ∑ i,
      τ F U
        (cL U (basis i))
        ((Pi.π (fun _ : Fin d ↦ F) i).val.app U x)
  comparison :
    pointFiniteFreeCoreEvaluation R one coefficientE ⋙ ModuleCat.extendScalars.{a, a, max a w} f ≅
      O ⋙
        pointFiniteFreeCoreEvaluation S one coefficientL
  comparison_tensor : ∀ (F : SheafOfModules.{max a w} rR) a n,
    comparison.hom.app F
      (a ⊗ₜ[A,f] n) =
      τ F one
        (coefficientL a) n
  comparison_coordinates : ∀ (F : SheafOfModules.{max a w} rR)
    (n : Fin d →
      (pointFiniteFreeCoreEvaluation R one coefficientE).obj F) i,
    (Pi.π (fun _ : Fin d ↦ F) i).val.app
        one
      ((coordinates F).hom.val.app one
        (comparison.hom.app F (∑ j,
          basis j ⊗ₜ[A,f] n j))) = n i
  comparison_inverse : ∀ (F : SheafOfModules.{max a w} rR) x,
    comparison.inv.app F x = ∑ i,
      basis i ⊗ₜ[A,f]
        (@id ((pointFiniteFreeCoreEvaluation R one coefficientE).obj F)
          ((Pi.π (fun _ : Fin d ↦ F) i).val.app
            one
              ((coordinates F).hom.val.app one x)))
  comparison_unique : ∀ (F : SheafOfModules.{max a w} rR)
    (g : ((pointFiniteFreeCoreEvaluation R one coefficientE ⋙
      ModuleCat.extendScalars.{a, a, max a w} f).obj F) ⟶
      ((O ⋙
        pointFiniteFreeCoreEvaluation S one coefficientL).obj F)),
    (∀ a n, g (a ⊗ₜ[A,f] n) =
        τ F one
          (coefficientL a) n) → g = comparison.hom.app F
  sheaf_additive : O.Additive
  sheaf_limits : PreservesFiniteLimits
    O
  sheaf_colimits : PreservesFiniteColimits
    O
  module_additive : (ModuleCat.extendScalars.{a, a, max a w} f).Additive
  module_limits : PreservesFiniteLimits (ModuleCat.extendScalars.{a, a, max a w} f)
  module_colimits : PreservesFiniteColimits (ModuleCat.extendScalars.{a, a, max a w} f)
  restriction_detects_exactness : ∀ K : ShortComplex (SheafOfModules.{max a w} rS),
    K.Exact ↔ (K.map (SheafOfModules.restrictScalars ringMap)).Exact
  complexes :
    (pointFiniteFreeCoreEvaluation R one coefficientE ⋙
      ModuleCat.extendScalars.{a, a, max a w} f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
    (O ⋙
      pointFiniteFreeCoreEvaluation S one coefficientL).mapHomologicalComplex (ComplexShape.up ℤ)
  complexes_hom : ∀ (K : CochainComplex (SheafOfModules.{max a w} rR) ℤ) j,
    (complexes.hom.app K).f j = comparison.hom.app (K.X j)
  complexes_inv : ∀ (K : CochainComplex (SheafOfModules.{max a w} rR) ℤ) j,
    (complexes.inv.app K).f j = comparison.inv.app (K.X j)



end WeilConjectures
end

@[expose] public noncomputable section
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

variable (k : Type t) [Field k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The core record specialized to the published completed coefficient constructions.
Source: Bhatt--Scholze 4.2.12 and 6.8.2(1); Stacks 03EK
(blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev PointFiniteFreeSectionsTensorCoreData :=
  PointFiniteFreeSectionsTensorCore.{u, max u (t + 1), t, t + 1}
    (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionIntegers l L)
    (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k)))
    (completedIntegralCommRingSheafUnrestricted l L (Spec (.of k)))
    (pointFiniteFreeFinal k) (integralScalarIntegerInclusion l E L ι)
    (completedCoefficientMap l E L ι (Spec (.of k)))
    (completedScalarRelativeDegree l E L ι)
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))
    (completedScalarTensorSection l E L ι (Spec (.of k)))
    (integralScalarConstant l E (Spec (.of k)))
    (integralScalarConstant l L (Spec (.of k)))
    (fun e : Padic.coefficientExtensionIntegers l E ≃+*
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))).obj.obj
          (pointFiniteFreeFinal k) ↦ ∀ n a,
      (completedIntegralCommRingProjectionUnrestricted l E (Spec (.of k)) n).hom.app
        (pointFiniteFreeFinal k) (e a) =
          integralScalarFiniteConstant l E (Spec (.of k)) n (pointFiniteFreeFinal k) a)
    (fun e : Padic.coefficientExtensionIntegers l L ≃+*
        (completedIntegralCommRingSheafUnrestricted l L (Spec (.of k))).obj.obj
          (pointFiniteFreeFinal k) ↦ ∀ n a,
      (completedIntegralCommRingProjectionUnrestricted l L (Spec (.of k)) n).hom.app
        (pointFiniteFreeFinal k) (e a) =
          integralScalarFiniteConstant l L (Spec (.of k)) n (pointFiniteFreeFinal k) a)




set_option backward.isDefEq.respectTransparency false in
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The complete assertion: normalized coefficient identifications, a common global
basis, local tensor coordinates, the unique linear natural comparison, exactness,
and its unbounded termwise complex comparison. Each field is a clause of the node.
The inverse formulas fix every coordinate isomorphism, rather than postulating an
unrelated abstract isomorphism. The choice of basis is confined to these coordinates.
Source: Bhatt--Scholze 4.2.12 and 6.8.2(1), Stacks 03EK; DAG statement
(blueprint: lem-weil-point-finite-free-sections-tensor). -/
structure PointFiniteFreeSectionsTensorData where
  coefficientE : Padic.coefficientExtensionIntegers l E ≃+*
    (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k))).obj.obj
      (pointFiniteFreeFinal k)
  coefficientL : Padic.coefficientExtensionIntegers l L ≃+*
    (completedIntegralCoefficientSheafUnrestricted l L (Spec (.of k))).obj.obj
      (pointFiniteFreeFinal k)
  constantE : ∀ a, coefficientE a =
    integralScalarConstant l E (Spec (.of k)) (pointFiniteFreeFinal k) a
  constantL : ∀ a, coefficientL a =
    integralScalarConstant l L (Spec (.of k)) (pointFiniteFreeFinal k) a
  quotientE : ∀ n a,
    (completedIntegralCommRingProjectionUnrestricted l E (Spec (.of k)) n).hom.app
      (pointFiniteFreeFinal k) (coefficientE a) =
        integralScalarFiniteConstant l E (Spec (.of k)) n (pointFiniteFreeFinal k) a
  quotientL : ∀ n a,
    (completedIntegralCommRingProjectionUnrestricted l L (Spec (.of k)) n).hom.app
      (pointFiniteFreeFinal k) (coefficientL a) =
        integralScalarFiniteConstant l L (Spec (.of k)) n (pointFiniteFreeFinal k) a
  coefficient_compatibility : ∀ a,
    (completedCoefficientMap l E L ι (Spec (.of k))).hom.app (pointFiniteFreeFinal k)
      (coefficientE a) = coefficientL (integralScalarIntegerInclusion l E L ι a)
  basis : Fin (completedScalarRelativeDegree l E L ι) → Padic.coefficientExtensionIntegers l L
  integral_basis : Function.Bijective
    (fun a : Fin (completedScalarRelativeDegree l E L ι) →
        Padic.coefficientExtensionIntegers l E ↦
      ∑ i, integralScalarIntegerInclusion l E L ι (a i) * basis i)
  sheafBasis :
    (pointFiniteFreeRestriction k l E L ι).obj
        (SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l L (Spec (.of k)))) ≅
      ∏ᶜ (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
        SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k))))
  sheafBasis_inverse : ∀ U x,
    sheafBasis.inv.val.app U x = ∑ i,
      (pointFiniteFreeRingMap k l E L ι).hom.app U
        ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
          SheafOfModules.unit
            (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k)))) i).val.app U x) *
        integralScalarConstant l L (Spec (.of k)) U (basis i)
  coordinates : ∀ F : integralTowerModules l E (Spec (.of k)),
    (pointFiniteFreeRestriction k l E L ι).obj
        ((completedOrdinaryScalarExtension l E L ι (Spec (.of k))).obj F) ≅
      ∏ᶜ (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F)
  coordinates_tensor : ∀ (F : integralTowerModules l E (Spec (.of k))) U a n i,
    (Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app U
      ((coordinates F).hom.val.app U
        (completedScalarTensorSection l E L ι (Spec (.of k)) F U a n)) =
      ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
        SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k)))) i).val.app U
            (sheafBasis.hom.val.app U a)) • n
  coordinates_inverse : ∀ (F : integralTowerModules l E (Spec (.of k))) U x,
    (coordinates F).inv.val.app U x = ∑ i,
      completedScalarTensorSection l E L ι (Spec (.of k)) F U
        (integralScalarConstant l L (Spec (.of k)) U (basis i))
        ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app U x)
  comparison :
    pointFiniteFreeEvaluation k l E coefficientE ⋙ pointFiniteFreeModuleTensor.{t, u} l E L ι ≅
      completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙
        pointFiniteFreeEvaluation k l L coefficientL
  comparison_tensor : ∀ (F : integralTowerModules l E (Spec (.of k))) a n,
    comparison.hom.app F
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l E, integralScalarIntegerInclusion l E L ι] n) =
      completedScalarTensorSection l E L ι (Spec (.of k)) F (pointFiniteFreeFinal k)
        (coefficientL a) n
  comparison_coordinates : ∀ (F : integralTowerModules l E (Spec (.of k)))
    (n : Fin (completedScalarRelativeDegree l E L ι) →
      (pointFiniteFreeEvaluation k l E coefficientE).obj F) i,
    (Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app
        (pointFiniteFreeFinal k)
      ((coordinates F).hom.val.app (pointFiniteFreeFinal k)
        (comparison.hom.app F (∑ j,
          basis j ⊗ₜ[Padic.coefficientExtensionIntegers l E,
            integralScalarIntegerInclusion l E L ι] n j))) = n i
  comparison_inverse : ∀ (F : integralTowerModules l E (Spec (.of k))) x,
    comparison.inv.app F x = ∑ i,
      basis i ⊗ₜ[Padic.coefficientExtensionIntegers l E,
        integralScalarIntegerInclusion l E L ι]
        (@id ((pointFiniteFreeEvaluation k l E coefficientE).obj F)
          ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app
            (pointFiniteFreeFinal k)
              ((coordinates F).hom.val.app (pointFiniteFreeFinal k) x)))
  comparison_unique : ∀ (F : integralTowerModules l E (Spec (.of k)))
    (f : ((pointFiniteFreeEvaluation k l E coefficientE ⋙
      pointFiniteFreeModuleTensor.{t, u} l E L ι).obj F) ⟶
      ((completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙
        pointFiniteFreeEvaluation k l L coefficientL).obj F)),
    (∀ a n, f (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
      integralScalarIntegerInclusion l E L ι] n) =
        completedScalarTensorSection l E L ι (Spec (.of k)) F (pointFiniteFreeFinal k)
          (coefficientL a) n) → f = comparison.hom.app F
  sheaf_additive : (completedOrdinaryScalarExtension l E L ι (Spec (.of k))).Additive
  sheaf_limits : PreservesFiniteLimits
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))
  sheaf_colimits : PreservesFiniteColimits
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))
  module_additive : (pointFiniteFreeModuleTensor.{t, u} l E L ι).Additive
  module_limits : PreservesFiniteLimits (pointFiniteFreeModuleTensor.{t, u} l E L ι)
  module_colimits : PreservesFiniteColimits (pointFiniteFreeModuleTensor.{t, u} l E L ι)
  restriction_detects_exactness : ∀ S : ShortComplex (integralTowerModules l L (Spec (.of k))),
    S.Exact ↔ (S.map (pointFiniteFreeRestriction k l E L ι)).Exact
  complexes :
    (pointFiniteFreeEvaluation k l E coefficientE ⋙
      pointFiniteFreeModuleTensor.{t, u} l E L ι).mapHomologicalComplex (ComplexShape.up ℤ) ≅
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙
      pointFiniteFreeEvaluation k l L coefficientL).mapHomologicalComplex (ComplexShape.up ℤ)
  complexes_hom : ∀ (K : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ) j,
    (complexes.hom.app K).f j = comparison.hom.app (K.X j)
  complexes_inv : ∀ (K : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ) j,
    (complexes.inv.app K).f j = comparison.inv.app (K.X j)

end WeilConjectures
end

noncomputable section
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] limit

attribute [local irreducible] completedScalarChangeData completedCoefficientMap
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
attribute [local irreducible] integralScalarConstant completedOrdinaryScalarExtension
attribute [local irreducible] completedScalarTensorSection
attribute [local irreducible] SheafOfModules.basedTensorProductSections


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L] [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

section ScalarTransport
universe rA rR
variable {A B : Type rA} {R S : Type rR}
  [CommRing A] [CommRing B] [CommRing R] [CommRing S]

@[irreducible] private def pointTensorTransport (eA : A ≃+* R) (eB : B ≃+* S)
    (f : A →+* B) (g : R →+* S) (hc : ∀ a, g (eA a) = eB (f a))
    (M : ModuleCat.{max rA rR} R) :
    (ModuleCat.extendScalars f).obj ((ModuleCat.restrictScalars eA.toRingHom).obj M) ≅
      (ModuleCat.restrictScalars eB.toRingHom).obj ((ModuleCat.extendScalars g).obj M) := by
  letI : RingHomInvPair eA.toRingHom eA.symm.toRingHom :=
    ⟨eA.symm_toRingHom_comp_toRingHom, eA.toRingHom_comp_symm_toRingHom⟩
  letI : RingHomInvPair eA.symm.toRingHom eA.toRingHom :=
    ⟨eA.toRingHom_comp_symm_toRingHom, eA.symm_toRingHom_comp_toRingHom⟩
  let fB : (ModuleCat.restrictScalars f).obj (ModuleCat.of B B) ≃ₛₗ[eA.toRingHom]
      (ModuleCat.restrictScalars g).obj (ModuleCat.of S S) :=
    { eB.toAddEquiv with
      map_smul' := fun a b ↦ by
        change B at b
        change eB (f a * b) = g (eA a) * eB b
        rw [map_mul, hc] }
  let fM : (ModuleCat.restrictScalars eA.toRingHom).obj M ≃ₛₗ[eA.toRingHom] M :=
    { AddEquiv.refl _ with map_smul' := fun _ _ ↦ rfl }
  let q := TensorProduct.congr fB fM
  let q' : (ModuleCat.extendScalars f).obj
      ((ModuleCat.restrictScalars eA.toRingHom).obj M) →ₗ[B]
      (ModuleCat.restrictScalars eB.toRingHom).obj ((ModuleCat.extendScalars g).obj M) :=
    { toFun := q
      map_add' := q.map_add
      map_smul' := fun b x ↦ by
        induction x using TensorProduct.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | add x y hx hy => simp only [smul_add, map_add, hx, hy]
        | tmul a n =>
          change B at a
          change eB (b * a) ⊗ₜ[R, g] n = eB b • (eB a ⊗ₜ[R, g] n)
          rw [map_mul]
          rfl }
  exact (LinearEquiv.ofBijective q' q.bijective).toModuleIso

private theorem pointTensorTransport_tmul (eA : A ≃+* R) (eB : B ≃+* S)
    (f : A →+* B) (g : R →+* S) (hc : ∀ a, g (eA a) = eB (f a))
    (M : ModuleCat.{max rA rR} R) (a : B) (n : M) :
    (pointTensorTransport.{rA, rR} eA eB f g hc M).hom (a ⊗ₜ[A,f] n) =
      eB a ⊗ₜ[R, g] n := by
  unfold pointTensorTransport
  rfl
private def pointModuleNaturalIso {D : Type*} [Category D] (f : A →+* B)
    (F : D ⥤ ModuleCat.{max rA rR} A) (G : D ⥤ ModuleCat.{max rA rR} B)
    (c : ∀ X, (ModuleCat.extendScalars f).obj (F.obj X) ≅ G.obj X)
    (hc : ∀ {X Y} (g : X ⟶ Y) (n : F.obj X),
      (c Y).hom ((1 : B) ⊗ₜ[A,f] F.map g n) =
        G.map g ((c X).hom ((1 : B) ⊗ₜ[A,f] n))) :
    F ⋙ ModuleCat.extendScalars f ≅ G :=
  NatIso.ofComponents c (by
    intro X Y g
    apply ModuleCat.ExtendScalars.hom_ext
    intro n
    exact (congrArg (fun z ↦ (c Y).hom z)
      (ModuleCat.ExtendScalars.map_tmul f (F.map g) 1 n)).trans (hc g n))

private theorem pointCoordinateSum (f : A →+* B) (d : ℕ)
    (b : Module.Basis (Fin d) A
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))
    (M : ModuleCat.{max rA rR} A) (N : Type*) [AddCommGroup N]
    (c : (ModuleCat.extendScalars f).obj M →+ N) (p : N →+ M)
    (i : Fin d) (hp : ∀ a n, p (c (a ⊗ₜ[A,f] n)) = b.equivFun a i • n)
    (n : Fin d → M) :
    p (c (∑ j : Fin d, b j ⊗ₜ[A,f] n j)) = n i := by
  rw [map_sum, map_sum]
  simp only [hp, Module.Basis.equivFun_self]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

private theorem pointModuleInverse (f : A →+* B) (d : ℕ) (b : Fin d → B)
    (M : ModuleCat.{max rA rR} A) (N : ModuleCat.{max rA rR} B)
    (c : (ModuleCat.extendScalars f).obj M ≅ N) (q : N → (Fin d → M))
    (hq : Function.Injective q)
    (hr : ∀ n, q (c.hom (∑ i : Fin d, b i ⊗ₜ[A,f] n i)) = n) (x : N) :
    c.inv x = ∑ i : Fin d, b i ⊗ₜ[A,f] (q x i) := by
  apply c.toLinearEquiv.injective
  exact (c.inv_hom_id_apply x).trans (hq (hr (q x))).symm

private theorem pointModuleTensorLimits (f : A →+* B) (d : ℕ)
    (b : Module.Basis (Fin d) A
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{rA, rA, max rA rR} f) := by
  let T := ModuleCat.extendScalars.{rA, rA, max rA rR} f
  let V := ModuleCat.restrictScalars.{max rA rR} f
  let P : ModuleCat.{max rA rR} A ⥤ ModuleCat.{max rA rR} A :=
    Functor.pi' (fun _ : Fin d ↦ 𝟭 _) ⋙ Pi.functor (Fin d)
  let q (M : ModuleCat.{max rA rR} A) :=
    TensorProduct.comm A ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) M ≪≫ₗ
      b.equivFun.lTensor M ≪≫ₗ TensorProduct.piScalarRight A A M (Fin d)
  have hq (M : ModuleCat.{max rA rR} A) (a : B) (n : M) (i : Fin d) :
      q M (a ⊗ₜ[A,f] n) i = b.equivFun a i • n := by
    change (TensorProduct.piScalarRightHom A A M (Fin d))
      (n ⊗ₜ[A] b.equivFun a) i = _
    exact congrArg (fun z ↦ z i)
      (TensorProduct.piScalarRightHom_tmul A A M (Fin d) n (b.equivFun a))
  let app (M : ModuleCat.{max rA rR} A) : (T ⋙ V).obj M ≅ P.obj M :=
    (q M).toModuleIso ≪≫ (ModuleCat.piIsoPi (fun _ : Fin d ↦ M)).symm
  let eq : T ⋙ V ≅ P := NatIso.ofComponents app (by
    intro M N g
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a n
    apply (ModuleCat.piIsoPi (fun _ : Fin d ↦ N)).toLinearEquiv.injective
    funext i
    have hp (M : ModuleCat.{max rA rR} A) (z : (T ⋙ V).obj M) :
        (ModuleCat.piIsoPi (fun _ : Fin d ↦ M)).hom ((app M).hom z) = q M z := by
      exact (ModuleCat.piIsoPi (fun _ : Fin d ↦ M)).inv_hom_id_apply _
    change ((ModuleCat.piIsoPi (fun _ : Fin d ↦ N)).hom
      ((app N).hom ((T ⋙ V).map g (a ⊗ₜ[A,f] n)))) i = _
    rw [congrFun (hp N _) i]
    change (q N) ((ModuleCat.extendScalars f).map g (a ⊗ₜ[A,f] n)) i = _
    rw [ModuleCat.ExtendScalars.map_tmul, hq]
    change _ = (ModuleCat.piIsoPi (fun _ : Fin d ↦ N)).hom
      (Limits.Pi.map (fun _ : Fin d ↦ g) ((app M).hom (a ⊗ₜ[A,f] n))) i
    have hpN (y : ↑(∏ᶜ fun _ : Fin d ↦ N)) :
        (ModuleCat.piIsoPi (fun _ : Fin d ↦ N)).hom y i = (Pi.π (fun _ : Fin d ↦ N) i) y :=
      ConcreteCategory.congr_hom
        (ModuleCat.piIsoPi_hom_ker_subtype (fun _ : Fin d ↦ N) i) y
    rw [hpN]
    change _ = ((Limits.Pi.map (fun _ : Fin d ↦ g) ≫ Pi.π _ i)
      ((app M).hom (a ⊗ₜ[A,f] n)))
    rw [Pi.map_π]
    change _ = g ((Pi.π (fun _ : Fin d ↦ M) i) ((app M).hom (a ⊗ₜ[A,f] n)))
    have hpM (y : ↑(∏ᶜ fun _ : Fin d ↦ M)) :
        (Pi.π (fun _ : Fin d ↦ M) i) y = (ModuleCat.piIsoPi (fun _ : Fin d ↦ M)).hom y i :=
      (ConcreteCategory.congr_hom
        (ModuleCat.piIsoPi_hom_ker_subtype (fun _ : Fin d ↦ M) i) y).symm
    rw [hpM]
    rw [congrFun (hp M _) i, hq]
    exact (g.hom.map_smul _ _).symm)
  have : PreservesFiniteLimits P := (SheafOfModules.power_exact (ModuleCat.{max rA rR} A) d).1
  have : PreservesFiniteLimits (T ⋙ V) := preservesFiniteLimits_of_natIso eq.symm
  have : V.IsRightAdjoint :=
    ⟨_, ⟨ModuleCat.extendRestrictScalarsAdj.{max rA rR, rA, rA} f⟩⟩
  exact preservesFiniteLimits_of_reflects_of_preserves T V

end ScalarTransport

private theorem pointBasisCoordinates {A B : Type*} [CommRing A] [AddCommGroup B]
    [Module A B] {d : ℕ} (b : Module.Basis (Fin d) A B) (a : B) (c : Fin d → A)
    (h : a = ∑ i, c i • b i) : c = b.equivFun a := by
  apply b.equivFun.symm.injective
  exact (b.equivFun_symm_apply c).trans (h.symm.trans
    (b.equivFun.symm_apply_apply a).symm)

private theorem pointTransportSection
    {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}
    {M N P : SheafOfModules R} (p : M = N) (q : P = N)
    (U : Cᵒᵖ) (z : N.val.obj U) :
    (eqToHom (p.trans q.symm)).val.app U ((eqToHom p.symm).val.app U z) =
      (eqToHom q.symm).val.app U z := by
  subst p
  subst q
  rfl

section Normalize
universe w c v
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {R S : Sheaf J CommRingCat.{w}}
private theorem pointNormalizedEvaluation (one : C) (hOne : IsTerminal one)
    (φ : R ⟶ S) (d : ℕ) (b : Fin d → S.obj.obj (op one))
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))
    (he : ∀ U r, e.hom.val.app U
      ((SheafOfModules.basedTensorProductSections (R := R) d
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) U).inv r) =
      ∑ i : Fin d, φ.hom.app U (r i) * S.obj.map (hOne.from U.unop).op (b i))
    (O : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (hO : ∀ F, O.obj F = SheafOfModules.changeOfRings φ F)
    (hmapO : ∀ {F G} (f : F ⟶ G), O.map f = eqToHom (hO F) ≫
      SheafOfModules.changeOfRingsHom φ F f ≫ eqToHom (hO G).symm) :
    O.Additive ∧ PreservesFiniteLimits O ∧ PreservesFiniteColimits O ∧
    ∃ (coords : ∀ F, (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj (O.obj F) ≅
          ∏ᶜ fun _ : Fin d ↦ F)
      (θ : ∀ F U, (SheafOfModules.changeOfRingsPresheaf φ F).obj U ≅ (O.obj F).val.obj U),
      (∀ F U a n, (θ F U).hom (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] n) =
        (eqToHom (hO F).symm).val.app U
          ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ F).presheaf).app U
            (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] n))) ∧
      (∀ (F : SheafOfModules.{w}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) U a n i,
        (Pi.π (fun _ : Fin d ↦ F) i).val.app U
        ((coords F).hom.val.app U
          ((θ F U).hom (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] n))) =
        ((Pi.π (fun _ : Fin d ↦ SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) i).val.app U
          (e.inv.val.app U a)) • n) ∧
      (∀ (F : SheafOfModules.{w}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) U x,
        (coords F).inv.val.app U x = (θ F U).hom
        (∑ i : Fin d, S.obj.map (hOne.from U.unop).op (b i) ⊗ₜ[R.obj.obj U,
          (φ.hom.app U).hom] (Pi.π (fun _ : Fin d ↦ F) i).val.app U x)) := by
  obtain ⟨T, hT, hmap, hAdd, hLim, hColim, Φ, θ,
    _, hθ, hΦ, hΦinv, _, _, _, _, _⟩ :=
    (SheafOfModules.basedSheafTensorEvaluation (R := R) (S := S)).2.2
      one hOne φ d b e he
  let σ : T ≅ O := NatIso.ofComponents
    (fun F ↦ eqToIso ((hT F).trans (hO F).symm)) (by
      intro F G f
      dsimp
      rw [hmap, hmapO]
      simp only [eqToHom_trans, Category.assoc, eqToHom_trans_assoc])
  let Q := SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let coords (F : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    Q.mapIso (σ.app F).symm ≪≫ Φ.app F
  let θ' (F : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ) :=
    θ F U ≪≫ (SheafOfModules.evaluation
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) U).mapIso (σ.app F)
  have : O.Additive := Functor.additive_of_iso σ
  have : PreservesFiniteLimits O := preservesFiniteLimits_of_natIso σ
  have : PreservesFiniteColimits O := preservesFiniteColimits_of_natIso σ
  refine ⟨inferInstance, inferInstance, inferInstance, coords, θ', ?_, ?_, ?_⟩
  · intro F U a n
    refine (congrArg ((σ.hom.app F).val.app U) (hθ F U a n)).trans ?_
    dsimp only [σ, NatIso.ofComponents_hom_app, eqToIso.hom]
    exact pointTransportSection (hT F) (hO F) U _
  · intro F U a n i
    change (Pi.π (fun _ : Fin d ↦ F) i).val.app U
      ((Φ.hom.app F).val.app U ((σ.inv.app F).val.app U
        ((σ.hom.app F).val.app U ((θ F U).hom _)))) = _
    exact (congrArg (fun x ↦ (Pi.π (fun _ : Fin d ↦ F) i).val.app U
      ((Φ.hom.app F).val.app U x))
        (((SheafOfModules.evaluation
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) U).mapIso
            (σ.app F)).hom_inv_id_apply _)).trans
          (hΦ F U a n i)
  · intro F U x
    change (σ.hom.app F).val.app U ((Φ.inv.app F).val.app U x) = _
    exact congrArg ((σ.hom.app F).val.app U) (hΦinv F U x)
end Normalize

section CoreAssembly
universe aG wG cG vG
variable {C : Type cG} [Category.{vG} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max aG wG} RingCat.{max aG wG})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max aG wG}]
  [HasSheafify J AddCommGrpCat.{max aG wG}]

private theorem pointCoreFromBasis
    (A B : Type aG) [CommRing A] [CommRing B]
    (R S : Sheaf J CommRingCat.{max aG wG})
    (one : C) (hOne : IsTerminal one) (f : A →+* B) (φ : R ⟶ S) (d : ℕ)
    (b : Module.Basis (Fin d) A
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))
    (hb : Function.Bijective (fun a : Fin d → A ↦ ∑ i, f (a i) * (show B from b i)))
    (eE : A ≃+* R.obj.obj (op one)) (eL : B ≃+* S.obj.obj (op one))
    (cE : ∀ U : Cᵒᵖ, A → R.obj.obj U) (cL : ∀ U : Cᵒᵖ, B → S.obj.obj U)
    (qE : (A ≃+* R.obj.obj (op one)) → Prop)
    (qL : (B ≃+* S.obj.obj (op one)) → Prop)
    (hcE : ∀ a, eE a = cE (op one) a) (hcL : ∀ a, eL a = cL (op one) a)
    (hqE : qE eE) (hqL : qL eL)
    (hc : ∀ a, φ.hom.app (op one) (eE a) = eL (f a))
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))
    (he : ∀ U x, e.hom.val.app U x = ∑ i,
      φ.hom.app U ((Pi.π (fun _ : Fin d ↦ SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) i).val.app U x) * cL U (b i))
    (heglobal : ∀ x, e.hom.val.app (op one) x = eL (∑ i,
      f (eE.symm ((Pi.π (fun _ : Fin d ↦ SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) i).val.app
          (op one) x)) * (show B from b i)))
    (hconst : ∀ (U : Cᵒᵖ) (i : Fin d), S.obj.map (hOne.from U.unop).op (eL (b i)) = cL U (b i))
    (O : SheafOfModules.{max aG wG}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{max aG wG} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    [O.Additive]
    (hO : ∀ F, O.obj F = SheafOfModules.changeOfRings φ F)
    (hmapO : ∀ {F G} (g : F ⟶ G), O.map g = eqToHom (hO F) ≫
      SheafOfModules.changeOfRingsHom φ F g ≫ eqToHom (hO G).symm)
    (τ : ∀ (F : SheafOfModules.{max aG wG}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ),
      S.obj.obj U → F.val.obj U → (O.obj F).val.obj U)
    (hτ : ∀ F U a n, (eqToHom (hO F).symm).val.app U
      ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ F).presheaf).app U
        (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] n)) = τ F U a n)
    (hτnat : ∀ {F G} (g : F ⟶ G) U a n,
      (O.map g).val.app U (τ F U a n) = τ G U a (g.val.app U n)) :
    Nonempty (PointFiniteFreeSectionsTensorCore A B R S (op one) f φ d O τ cE cL qE qL) := by
  classical
  have he' (U : Cᵒᵖ) (r : Fin d → R.obj.obj U) :
      e.hom.val.app U
        ((SheafOfModules.basedTensorProductSections (R := R) d
          (SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) U).inv.hom r) =
        ∑ i, φ.hom.app U (r i) * S.obj.map (hOne.from U.unop).op (eL (b i)) := by
    let P := SheafOfModules.basedTensorProductSections (R := R) d
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) U
    have hr (i : Fin d) :
        (Pi.π (fun _ : Fin d ↦ SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) i).val.app U
            (P.inv.hom r) = r i :=
      (SheafOfModules.sections_coordinate (R := R) d _ U (P.inv.hom r) i).symm.trans
        (congrArg (fun z ↦ z i) (P.inv_hom_id_apply r))
    exact (he U (P.inv.hom r)).trans (Finset.sum_congr rfl (fun i _ ↦
      congrArg₂ (fun x y : S.obj.obj U ↦ x * y)
        (congrArg (fun x ↦ φ.hom.app U x) (hr i)) (hconst U i).symm))
  obtain ⟨hAdd, hLim, hColim, coords, θ', hθraw, hcoordsraw, hcoordsinvraw⟩ :=
    pointNormalizedEvaluation one hOne φ d (fun i ↦ eL (b i)) e he' O
      hO hmapO
  have : O.Additive := hAdd
  have hθ' (F : SheafOfModules.{max aG wG}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ) (a : S.obj.obj U)
      (n : F.val.obj U) :
      (θ' F U).hom (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] n) =
        τ F U a n :=
    (hθraw F U a n).trans (hτ F U a n)
  let Q := SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  have hcoords (F : SheafOfModules.{max aG wG}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ) (a : S.obj.obj U)
      (n : F.val.obj U) (i : Fin d) :
      (Pi.π (fun _ : Fin d ↦ F) i).val.app U
        ((coords F).hom.val.app U (τ F U a n)) =
        ((Pi.π (fun _ : Fin d ↦ SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) i).val.app U
            (e.inv.val.app U a)) • n :=
    (congrArg (fun z ↦ (Pi.π (fun _ : Fin d ↦ F) i).val.app U
      ((coords F).hom.val.app U z)) (hθ' F U a n)).symm.trans (hcoordsraw F U a n i)
  have hcoordsinv (F : SheafOfModules.{max aG wG}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ)
      (x : (∏ᶜ fun _ : Fin d ↦ F).val.obj U) :
      (coords F).inv.val.app U x = ∑ i,
        τ F U
          (cL U (b i))
          ((Pi.π (fun _ : Fin d ↦ F) i).val.app U x) := by
    refine (hcoordsinvraw F U x).trans ((map_sum (θ' F U).hom.hom _ _).trans ?_)
    exact Finset.sum_congr rfl (fun i _ ↦ (hθ' F U _ _).trans
      (congrArg (fun a ↦ τ F U a
        ((Pi.π (fun _ : Fin d ↦ F) i).val.app U x)) (hconst U i)))
  let compApp (F : SheafOfModules.{max aG wG}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
      (ModuleCat.extendScalars.{aG, aG, max aG wG} f).obj
        ((pointFiniteFreeCoreEvaluation R (op one) eE).obj F) ≅
      (pointFiniteFreeCoreEvaluation S (op one) eL).obj (O.obj F) :=
    pointTensorTransport.{aG, max aG wG}
      (R := R.obj.obj (op one))
      (S := S.obj.obj (op one)) eE eL f
      (φ.hom.app (op one)).hom hc (F.val.obj (op one)) ≪≫
        (ModuleCat.restrictScalars eL.toRingHom).mapIso (θ' F (op one))
  have hcomp (F : SheafOfModules.{max aG wG}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) a n :
      (compApp F).hom
        (a ⊗ₜ[A,f] n) =
      τ F (op one) (eL a) n := by
    change (θ' F (op one)).hom
      ((pointTensorTransport.{aG, max aG wG}
      (R := R.obj.obj (op one))
      (S := S.obj.obj (op one)) eE eL
        f
        (φ.hom.app (op one)).hom hc
        (F.val.obj (op one))).hom _) = _
    rw [pointTensorTransport_tmul]
    exact hθ' F (op one) (eL a) n
  clear_value compApp
  let comp : pointFiniteFreeCoreEvaluation R (op one) eE ⋙
      ModuleCat.extendScalars.{aG, aG, max aG wG} f ≅
      O ⋙ pointFiniteFreeCoreEvaluation S (op one) eL :=
    pointModuleNaturalIso.{aG, max aG wG}
      f
      (pointFiniteFreeCoreEvaluation R (op one) eE)
      (O ⋙ pointFiniteFreeCoreEvaluation S (op one) eL) compApp (by
        intro F G f n
        exact (hcomp G (1 : B)
          (f.val.app _ n)).trans
            ((hτnat f _ (eL 1) n).symm.trans
              (congrArg (fun z ↦ (O.map f).val.app _ z)
                (hcomp F (1 : B) n).symm)))
  have hcoeff (a : B) (i : Fin d) :
      (Pi.π (fun _ : Fin d ↦ SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) i).val.app
          (op one) (e.inv.val.app (op one) (eL a)) =
        eE (b.equivFun a i) := by
    let z := e.inv.val.app (op one) (eL a)
    have hz := heglobal z
    have hi := (SheafOfModules.evaluation _ (op one)).mapIso e
      |>.inv_hom_id_apply (eL a)
    have hz' : a = ∑ j, f
        (eE.symm ((Pi.π (fun _ : Fin d ↦ SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) j).val.app
            (op one) z)) * (show B from b j) :=
      eL.injective (hi.symm.trans hz)
    have hrepr : (fun j ↦ eE.symm ((Pi.π (fun _ : Fin d ↦ SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) j).val.app
            (op one) z)) = b.equivFun a := by
      exact pointBasisCoordinates b a _ hz'
    exact (eE.apply_symm_apply _).symm.trans
      (congrArg eE (congrFun hrepr i))
  have hcompcoords (F : SheafOfModules.{max aG wG}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (n : Fin d → (pointFiniteFreeCoreEvaluation R (op one) eE).obj F) (i : Fin d) :
      (Pi.π (fun _ : Fin d ↦ F) i).val.app (op one)
        ((coords F).hom.val.app (op one)
          ((compApp F).hom (∑ j,
            b j ⊗ₜ[A,f] n j))) = n i := by
    let M := (pointFiniteFreeCoreEvaluation R (op one) eE).obj F
    let N := (pointFiniteFreeCoreEvaluation S (op one) eL).obj (O.obj F)
    let p : N →+ M :=
      (((Pi.π (fun _ : Fin d ↦ F) i).val.app (op one)).hom.toAddMonoidHom).comp
        ((coords F).hom.val.app (op one)).hom.toAddMonoidHom
    have hp (a : B) (n : M) :
        p ((compApp F).hom (a ⊗ₜ[A,f] n)) = b.equivFun a i • n := by
      have h1 := hcomp F a n
      have h2 := hcoords F (op one) (eL a) n i
      have h3 := hcoeff a i
      exact (congrArg p h1).trans (h2.trans
        (congrArg (fun a : ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.obj
          (op one) ↦ a • (show F.val.obj (op one) from n)) h3))
    exact pointCoordinateSum.{aG, max aG wG}
      f d b M N
      (compApp F).hom.hom.toAddMonoidHom p i hp n
  have hcompinv (F : SheafOfModules.{max aG wG}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (x : (pointFiniteFreeCoreEvaluation S (op one) eL).obj (O.obj F)) :
      (compApp F).inv x = ∑ i,
        b i ⊗ₜ[A,f]
          (@id ((pointFiniteFreeCoreEvaluation R (op one) eE).obj F)
            ((Pi.π (fun _ : Fin d ↦ F) i).val.app (op one)
              ((coords F).hom.val.app (op one) x))) := by
    let q : (pointFiniteFreeCoreEvaluation S (op one) eL).obj (O.obj F) →
        (Fin d → (pointFiniteFreeCoreEvaluation R (op one) eE).obj F) := fun x i ↦
      (Pi.π (fun _ : Fin d ↦ F) i).val.app (op one)
        ((coords F).hom.val.app (op one) x)
    have hq : Function.Injective q := by
      intro x y hxy
      apply ((SheafOfModules.evaluation
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (op one)).mapIso (coords F)).toLinearEquiv.injective
      exact SheafOfModules.sectionProduct_ext (R := R) d F _ _ _
        (fun i ↦ congrFun hxy i)
    exact pointModuleInverse.{aG, max aG wG}
      f d (fun i ↦ b i)
      ((pointFiniteFreeCoreEvaluation R (op one) eE).obj F)
      ((pointFiniteFreeCoreEvaluation S (op one) eL).obj (O.obj F))
      (compApp F) q hq (fun n ↦ funext (hcompcoords F n)) x
  have : PreservesFiniteLimits O := hLim
  have : PreservesFiniteColimits O := hColim
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{aG, aG, max aG wG} f) :=
    pointModuleTensorLimits.{aG, max aG wG}
      f d b
  have hres := (SheafOfModules.basedSheafTensorEvaluation
    (C := C) (R := R) (S := S)).1 φ
  let cx := NatIso.mapHomologicalComplex comp (ComplexShape.up ℤ)
  refine ⟨{
    coefficientE := eE
    coefficientL := eL
    constantE := hcE
    constantL := hcL
    quotientE := hqE
    quotientL := hqL
    coefficient_compatibility := hc
    basis := b
    integral_basis := hb
    sheafBasis := e.symm
    sheafBasis_inverse := he
    coordinates := coords
    coordinates_tensor := hcoords
    coordinates_inverse := hcoordsinv
    comparison := comp
    comparison_tensor := hcomp
    comparison_coordinates := hcompcoords
    comparison_inverse := hcompinv
    comparison_unique := ?_
    sheaf_additive := inferInstance
    sheaf_limits := inferInstance
    sheaf_colimits := inferInstance
    module_additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max aG wG, aG, aG} f).left_adjoint_additive
    module_limits := inferInstance
    module_colimits := inferInstance
    restriction_detects_exactness := ?_
    complexes := cx
    complexes_hom := fun _ _ ↦ rfl
    complexes_inv := fun _ _ ↦ rfl }⟩
  · intro F f hf
    apply ModuleCat.ExtendScalars.hom_ext
    intro n
    exact (hf (1 : B) n).trans
      (hcomp F (1 : B) n).symm
  · intro K
    exact K.exact_iff_image_eq_kernel.trans
      ((hres.2.2 _ _ _ K.f K.g).trans (K.map Q).exact_iff_image_eq_kernel.symm)

end CoreAssembly

private theorem pointCanonicalTensor (Y : Scheme.{t})
    (F : integralTowerModules l E Y) (U : Y.ProEtᵒᵖ)
    (a : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
    (n : F.val.obj U) :
    (eqToHom (completedOrdinaryScalarExtension_obj l E L ι Y F).symm).val.app U
      ((toSheafify (Scheme.ProEt.topology Y)
        (SheafOfModules.changeOfRingsPresheaf
          (completedCoefficientMap l E L ι Y) F).presheaf).app U
            (a ⊗ₜ[_, ((completedCoefficientMap l E L ι Y).hom.app U).hom] n)) =
      completedScalarTensorSection l E L ι Y F U a n := by
  unfold completedScalarTensorSection completedOrdinaryScalarExtension
  rfl



private theorem pointIntegralBasis :
    let := ι.toAlgebra
    let := (integralScalarIntegerInclusion l E L ι).toAlgebra
    Nonempty (Module.Basis (Fin (completedScalarRelativeDegree l E L ι))
      (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionIntegers l L)) := by
  exact integral_basis l E L ι

private theorem pointFiniteFreeCoreData (D : FiniteFieldDatum.{t}) :
    Nonempty (PointFiniteFreeSectionsTensorCoreData D.k l E L ι) := by
  classical
  let := ι.toAlgebra
  let := (integralScalarIntegerInclusion l E L ι).toAlgebra
  let X : Scheme.{t} := Spec (CommRingCat.of D.k)
  obtain ⟨b⟩ := pointIntegralBasis l E L ι
  have hb : Function.Bijective
      (fun a : Fin (completedScalarRelativeDegree l E L ι) →
          Padic.coefficientExtensionIntegers l E ↦
        ∑ i, integralScalarIntegerInclusion l E L ι (a i) * b i) := by
    have hh : (fun a ↦ ∑ i, integralScalarIntegerInclusion l E L ι (a i) * b i) =
        b.equivFun.symm := by
      funext a
      rw [Module.Basis.equivFun_symm_apply]
      rfl
    rw [hh]
    exact b.equivFun.symm.bijective
  obtain ⟨eE, eL, hcE, hcL, hqE, hqL, hc, hBasis⟩ :=
    connected_adic_integral_basis l E L ι X
  obtain ⟨e, he, hquot, heglobal⟩ := hBasis b hb
  clear hBasis hquot
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let S := completedIntegralCommRingSheafUnrestricted l L X
  let φ := completedCoefficientMap l E L ι X
  let d := completedScalarRelativeDegree l E L ι
  let one := Scheme.ProEt.mk (𝟙 X)
  let hOne := Scheme.ProEt.isTerminalMkId X
  have hconst (U : X.ProEtᵒᵖ) (i : Fin d) :
      S.obj.map (hOne.from U.unop).op (eL (b i)) =
        integralScalarConstant l L X U (b i) := by
    rw [hcL]
    exact integralScalarConstant_naturality l L X _ _
  exact pointCoreFromBasis.{u, t + 1, t + 1, t}
    (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionIntegers l L)
    R S one hOne (integralScalarIntegerInclusion l E L ι) φ d b hb eE eL
    (integralScalarConstant l E X) (integralScalarConstant l L X) _ _
    hcE hcL hqE hqL hc e he heglobal hconst
    (completedOrdinaryScalarExtension l E L ι X)
    (completedOrdinaryScalarExtension_obj l E L ι X)
    (completedOrdinaryScalarExtension_map l E L ι X)
    (completedScalarTensorSection l E L ι X) (pointCanonicalTensor l E L ι X)
    (fun g U a n ↦ completedScalarTensorSection_naturality l E L ι X g U a n)

private theorem pointFiniteFreeData (D : FiniteFieldDatum.{t}) :
    Nonempty (PointFiniteFreeSectionsTensorData D.k l E L ι) := by
  obtain ⟨c⟩ := pointFiniteFreeCoreData l E L ι D
  exact ⟨{
    coefficientE := c.coefficientE
    coefficientL := c.coefficientL
    constantE := c.constantE
    constantL := c.constantL
    quotientE := c.quotientE
    quotientL := c.quotientL
    coefficient_compatibility := c.coefficient_compatibility
    basis := c.basis
    integral_basis := c.integral_basis
    sheafBasis := c.sheafBasis
    sheafBasis_inverse := c.sheafBasis_inverse
    coordinates := c.coordinates
    coordinates_tensor := c.coordinates_tensor
    coordinates_inverse := c.coordinates_inverse
    comparison := c.comparison
    comparison_tensor := c.comparison_tensor
    comparison_coordinates := c.comparison_coordinates
    comparison_inverse := c.comparison_inverse
    comparison_unique := c.comparison_unique
    sheaf_additive := c.sheaf_additive
    sheaf_limits := c.sheaf_limits
    sheaf_colimits := c.sheaf_colimits
    module_additive := c.module_additive
    module_limits := c.module_limits
    module_colimits := c.module_colimits
    restriction_detects_exactness := c.restriction_detects_exactness
    complexes := c.complexes
    complexes_hom := c.complexes_hom
    complexes_inv := c.complexes_inv }⟩

-- The characteristic and algebraic-closure hypotheses record the paper’s conventions.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency true in
/-- The normalized integral basis gives the canonical section-tensor comparison.
Source: Bhatt--Scholze 4.2.12 and 6.8.2(1); Stacks 03EK
(blueprint: lem-weil-point-finite-free-sections-tensor).

Proof: choose an integral basis using the agreement of absolute values. Apply the
connected adic integral-basis theorem to Spec k, and transport the generic based
sheaf tensor evaluation isomorphisms along the normalized coefficient equivalences.
The ordinary module tensor coordinates give the inverse and preserve finite limits.
The pure-tensor formula gives naturality and uniqueness; restriction detects exactness.
Map the resulting natural isomorphism termwise to unbounded cochain complexes. -/
public theorem point_finite_free_sections_tensor
    (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E L : IntermediateField ℚ_[l] Ω)
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L] (h : E ≤ L) :
    Nonempty (PointFiniteFreeSectionsTensorData D.k l E L (IntermediateField.inclusion h)) :=
  pointFiniteFreeData l E L (IntermediateField.inclusion h) D

end WeilConjectures

end
