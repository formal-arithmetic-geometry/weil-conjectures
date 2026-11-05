/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralScalarData
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.SmoothPurity.Supporting.ConnectedAdicIntegralBasis
import all WeilConjectures.Algebra.Homology.SmoothPurity.BasedTensorEvaluation
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
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

variable (k : Type t) [Field k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

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

end ScalarTransport

section Normalize
universe w c v
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {R S : Sheaf J CommRingCat.{w}}
end Normalize

section CoreAssembly
universe aG wG cG vG
variable {C : Type cG} [Category.{vG} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max aG wG} RingCat.{max aG wG})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max aG wG}]
  [HasSheafify J AddCommGrpCat.{max aG wG}]

end CoreAssembly

end WeilConjectures

end
