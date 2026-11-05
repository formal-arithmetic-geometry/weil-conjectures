/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InvertibleTensorScalarExtensionDefinitions
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

/-!
# Binary scalar-extension comparisons

Source: Stacks Project, Tag 03EK.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC u m

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

set_option hygiene false in
local notation:max "Mod" R:arg =>
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
set_option hygiene false in
local notation:max "𝒪" R:arg => unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
set_option hygiene false in
local notation:max "𝒯" N:arg P:arg => (siteSheafTensorRight P).obj N

/-- Sectionwise multiplication identifies scalar extension of the unit with the target unit.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable def scalarExtensionUnitRawIso {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) :
    changeOfRingsPresheafOfUniverses α (𝒪 R) ≅ (𝒪 S).val :=
  PresheafOfModules.isoMk (fun U ↦ by
    let := (α.hom.app U).hom.toAlgebra
    exact (TensorProduct.AlgebraTensorModule.rid
      (R.obj.obj U) (S.obj.obj U) (S.obj.obj U)).toModuleIso) (by
    intro U V i
    let := (α.hom.app U).hom.toAlgebra
    let := (α.hom.app V).hom.toAlgebra
    apply ModuleCat.ExtendScalars.hom_ext
    intro a
    change (TensorProduct.AlgebraTensorModule.rid
        (R.obj.obj V) (S.obj.obj V) (S.obj.obj V))
        (changeOfRingsMapOfUniverses α (𝒪 R) i
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] a)) = _
    rw [changeOfRingsMap_tmulOfUniverses]
    change (α.hom.app V (R.obj.map i a)) * S.obj.map i 1 =
      S.obj.map i ((α.hom.app U a) * 1)
    simp only [map_one, mul_one]
    exact ConcreteCategory.congr_hom (α.hom.naturality i) a)

/-- Sheafify the explicit multiplication isomorphism and compose with the counit.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable def scalarExtensionUnitIso {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) :
    changeOfRingsOfUniverses α (𝒪 R) ≅ 𝒪 S :=
  (PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).mapIso
      (scalarExtensionUnitRawIso α) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).counit).app (𝒪 S)

/-- scalarSheafificationUnit for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node). -/
noncomputable def scalarSheafificationUnit
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}] {R : Sheaf J CommRingCat.{u}}
    (P : PresheafOfModules.{m} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    P ⟶ ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj P).val :=
  (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.app P

/-- scalarSheafificationUnit locallyInjective for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
instance scalarSheafificationUnit_locallyInjective
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}] {R : Sheaf J CommRingCat.{u}}
    (P : PresheafOfModules.{m} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.IsLocallyInjective J (scalarSheafificationUnit (J := J) P) := by
  change PresheafOfModules.IsLocallyInjective J (PresheafOfModules.toSheafify
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
    (CategoryTheory.toSheafify J P.presheaf))
  infer_instance

/-- scalarSheafificationUnit locallySurjective for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
instance scalarSheafificationUnit_locallySurjective
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}] {R : Sheaf J CommRingCat.{u}}
    (P : PresheafOfModules.{m} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.IsLocallySurjective J (scalarSheafificationUnit (J := J) P) := by
  change PresheafOfModules.IsLocallySurjective J (PresheafOfModules.toSheafify
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
    (CategoryTheory.toSheafify J P.presheaf))
  infer_instance

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarSheafification map unit for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
theorem scalarSheafification_map_unit
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}] {R : Sheaf J CommRingCat.{u}}
    {P Q : PresheafOfModules.{m} (R.obj ⋙ forget₂ CommRingCat RingCat)} (f : P ⟶ Q)
    (U : Cᵒᵖ) (x : P.obj U) :
    (((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).map f).val.app U)
      ((scalarSheafificationUnit P).app U x) = (scalarSheafificationUnit Q).app U (f.app U x) := by
  exact (congrArg (fun g ↦ g.app U x)
    ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.naturality f)).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtension_hom_ext for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtension_hom_ext
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {H : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj S)} (f g : changeOfRingsOfUniverses α N ⟶ H)
    (h : ∀ U s x, f.val.app U (scalarExtensionSection α N U s x) =
      g.val.app U (scalarExtensionSection α N U s x)) : f = g := by
  apply (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).homEquiv _ _ |>.injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact h U 1 x

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionSection_naturality for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionSection_naturality
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {U V : Cᵒᵖ} (i : U ⟶ V) (s : S.obj.obj U) (x : N.val.obj U) :
    (changeOfRingsOfUniverses α N).val.map i (scalarExtensionSection α N U s x) =
      scalarExtensionSection α N V (S.obj.map i s) (N.val.map i x) := by
  have h := (PresheafOfModules.naturality_apply
    (scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α N)) i
      (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)).symm
  exact h.trans (congrArg ((scalarSheafificationUnit
    (changeOfRingsPresheafOfUniverses α N)).app V)
      (changeOfRingsMap_tmulOfUniverses α N i s x))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtension_map_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtension_map_tmul
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    {N P : SheafOfModules.{m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)} (f : N ⟶ P)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :
    (changeOfRingsHomOfUniverses α N f).val.app U (scalarExtensionSection α N U s x) =
      scalarExtensionSection α P U s (f.val.app U x) := by
  exact scalarSheafification_map_unit
    ({ app := fun U ↦ (ModuleCat.extendScalars (α.hom.app U).hom).map (f.val.app U)
       naturality := changeOfRingsHom_naturalityOfUniverses α N f } :
      changeOfRingsPresheafOfUniverses α N ⟶ changeOfRingsPresheafOfUniverses α P)
    U (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionSection_smul for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionSection_smul
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s t : S.obj.obj U) (x : N.val.obj U) :
    s • scalarExtensionSection α N U t x = scalarExtensionSection α N U (s * t) x := by
  let η := ((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app
      (changeOfRingsPresheafOfUniverses α N)).app U
  exact (η.hom.map_smul s (t ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionSection_base_smul for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionSection_base_smul
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (a : R.obj.obj U) (x : N.val.obj U) :
    scalarExtensionSection α N U s (a • x) =
      scalarExtensionSection α N U (s * α.hom.app U a) x := by
  dsimp only [scalarExtensionSection]
  congr 1
  rw [TensorProduct.tmul_smul]
  exact congrArg (fun z : S.obj.obj U ↦ z ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)
    (mul_comm (α.hom.app U a) s)

section Coherence
variable {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (k : ∀ N P : Mod R, changeOfRingsOfUniverses α (𝒯 N P) ≅
      (siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N))
    (hk : ∀ N P U s x y, ((k N P).hom.val.app U)
      (scalarExtensionSection α (𝒯 N P) U s (siteSheafTensorTmul N P U x y)) =
      siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        (scalarExtensionSection α N U s x) (scalarExtensionSection α P U 1 y))

include hk

end Coherence

/-- scalarExtensionRawLift for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
-/
noncomputable def scalarExtensionRawLift
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) (H : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj S))
    (f : N ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj H) :
    changeOfRingsPresheafOfUniverses α N ⟶ H.val where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (α.hom.app U).hom (f.val.app U)
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (α.hom.app V).hom (f.val.app V)
        (changeOfRingsMapOfUniverses α N i
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)) = _
    rw [changeOfRingsMap_tmulOfUniverses, map_one]
    change (1 : S.obj.obj V) • (show H.val.obj V from f.val.app V (N.val.map i x)) =
      H.val.map i ((1 : S.obj.obj U) • (show H.val.obj U from f.val.app U x))
    simp only [one_smul]
    exact PresheafOfModules.naturality_apply f.val i x

/-- scalarExtensionLift for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
-/
noncomputable def scalarExtensionLift
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) (H : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj S))
    (f : N ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj H) :
    changeOfRingsOfUniverses α N ⟶ H :=
  ((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).homEquiv _ _).symm
      (scalarExtensionRawLift α N H f)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionLift_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionLift_tmul
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) (H : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj S))
    (f : N ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj H)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :
    (scalarExtensionLift α N H f).val.app U (scalarExtensionSection α N U s x) =
      s • (show H.val.obj U from f.val.app U x) := by
  have h := congrArg (fun g ↦ g.app U (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x))
    ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).homEquiv _ _
        |>.apply_symm_apply (scalarExtensionRawLift α N H f))
  refine h.trans ?_
  rfl

namespace ScalarExtensionTensorCore

variable {R S : Sheaf J CommRingCat.{u}} {α : R ⟶ S}

end ScalarExtensionTensorCore

end SheafOfModules
