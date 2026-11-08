/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Rank-one ordinary scalar comparisons

Source: Stacks Project, Tags 093J and 093M.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local irreducible] completedAdicChangeData completedAdicRing

section ConstantPresentation

variable {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{t + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
  {B : Type (t + 1)} [CommRing B] {R : Sheaf J RingCat.{t + 1}}
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

private def directConstant : ModuleCat.{t + 1} B ⥤ SheafOfModules.{t + 1} R :=
  Functor.const Cᵒᵖ ⋙ ProEtale.finiteCoefficientModulePresheaf C B ⋙
    PresheafOfModules.sheafification α

private def directConstantUnit (N : ModuleCat.{t + 1} B) :=
  (PresheafOfModules.sheafificationAdjunction α).unit.app
    ((ProEtale.finiteCoefficientModulePresheaf C B).obj ((Functor.const Cᵒᵖ).obj N))

private instance directConstant_preservesColimits :
    PreservesColimitsOfSize.{t + 1, t + 1} (directConstant α) := by
  let P := Functor.const Cᵒᵖ ⋙ ProEtale.finiteCoefficientModulePresheaf C B
  have : PreservesColimitsOfSize.{t + 1, t + 1} P := by
    constructor
    intro K _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun Z ↦ hc)⟩
  change PreservesColimitsOfSize.{t + 1, t + 1}
    (P ⋙ PresheafOfModules.sheafification α)
  infer_instance

private def directUnitRaw :
    (ProEtale.finiteCoefficientModulePresheaf C B).obj
      ((Functor.const Cᵒᵖ).obj (ModuleCat.of B B)) ⟶
        (PresheafOfModules.restrictScalars α).obj (SheafOfModules.unit R).val := by
  refine { app := ?_, naturality := ?_ }
  · intro Z
    refine ModuleCat.ofHom (X := ModuleCat.of B B)
      (Y := ((PresheafOfModules.restrictScalars α).obj (SheafOfModules.unit R).val).obj Z)
      { toFun := α.app Z
        map_add' := map_add _
        map_smul' := fun b x ↦ (α.app Z).hom.map_mul b x }
  · intro Z Z' i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    exact ConcreteCategory.congr_hom (α.naturality i) b

private def directUnitMap :
    (directConstant α).obj (ModuleCat.of B B) ⟶ SheafOfModules.unit R :=
  (PresheafOfModules.sheafificationHomEquiv α).symm (directUnitRaw α)

private lemma directUnitMap_unit :
    toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of B)) ≫
      (PresheafOfModules.toPresheaf _).map (directUnitMap α).val =
      whiskerRight α (forget₂ RingCat.{t + 1} AddCommGrpCat.{t + 1}) := by
  unfold directUnitMap
  erw [PresheafOfModules.comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom]
  rfl

private def directUnitIso :
    (directConstant α).obj (ModuleCat.of B B) ≅ SheafOfModules.unit R := by
  let g := (SheafOfModules.toSheaf R).map (directUnitMap α)
  have h : toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of B)) ≫ g.hom =
      whiskerRight α (forget₂ RingCat.{t + 1} AddCommGrpCat.{t + 1}) :=
    directUnitMap_unit α
  have hi : Presheaf.IsLocallyInjective J
      (whiskerRight α (forget₂ RingCat.{t + 1} AddCommGrpCat.{t + 1})) := by
    constructor
    intro Z x y hxy
    exact Presheaf.equalizerSieve_mem J α x y hxy
  have hs : Presheaf.IsLocallySurjective J
      (whiskerRight α (forget₂ RingCat.{t + 1} AddCommGrpCat.{t + 1})) := by
    constructor
    intro Z x
    exact Presheaf.imageSieve_mem J α x
  have : Presheaf.IsLocallyInjective J g.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J _ h
  have : Presheaf.IsLocallySurjective J g.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J h
  have : IsIso g := (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨inferInstance, inferInstance⟩
  have : IsIso (directUnitMap α) := isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)
  exact asIso (directUnitMap α)

variable {D : Type (t + 1)} [CommRing D] {S : Sheaf J RingCat.{t + 1}}
  (β : (Functor.const Cᵒᵖ).obj (RingCat.of D) ⟶ S.obj)
  [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
  (q : B →+* D) (p : R ⟶ S)
  (h : ∀ Z, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z)

include h in
private def directCoefficientRaw (N : ModuleCat.{t + 1} D) :
    (ProEtale.finiteCoefficientModulePresheaf C B).obj
      ((Functor.const Cᵒᵖ).obj ((ModuleCat.restrictScalars q).obj N)) ⟶
        (PresheafOfModules.restrictScalars α).obj
          ((SheafOfModules.restrictScalars p).obj ((directConstant β).obj N)).val := by
  let T := (SheafOfModules.restrictScalars p).obj ((directConstant β).obj N)
  refine { app := ?_, naturality := ?_ }
  · intro Z
    refine ModuleCat.ofHom
      (X := (ModuleCat.restrictScalars q).obj N)
      (Y := ((PresheafOfModules.restrictScalars α).obj T.val).obj Z)
      { toFun := (directConstantUnit β N).app Z
        map_add' := map_add _
        map_smul' := ?_ }
    intro b x
    have hs : (directConstantUnit β N).app Z (q b • x) =
        β.app Z (q b) • (show ((directConstant β).obj N).val.obj Z from
          (directConstantUnit β N).app Z x) :=
      ((directConstantUnit β N).app Z).hom.map_smul (q b) x
    change (directConstantUnit β N).app Z (q b • x) =
      p.hom.app Z (α.app Z b) •
        (show ((directConstant β).obj N).val.obj Z from (directConstantUnit β N).app Z x)
    rw [hs]
    rw [show β.app Z (q b) = p.hom.app Z (α.app Z b) from
      (ConcreteCategory.congr_hom (h Z) b).symm]
  · intro Z Z' i
    ext x
    exact ConcreteCategory.congr_hom ((directConstantUnit β N).naturality i) x

private def directCoefficientMap (N : ModuleCat.{t + 1} D) :
    (directConstant α).obj ((ModuleCat.restrictScalars q).obj N) ⟶
      (SheafOfModules.restrictScalars p).obj ((directConstant β).obj N) :=
  (PresheafOfModules.sheafificationHomEquiv α).symm (directCoefficientRaw α β q p h N)

attribute [local irreducible] directCoefficientMap

private lemma directCoefficientMap_unit (N : ModuleCat.{t + 1} D) :
    toSheafify J ((Functor.const Cᵒᵖ).obj
        ((forget₂ (ModuleCat.{t + 1} D) AddCommGrpCat.{t + 1}).obj N)) ≫
      (PresheafOfModules.toPresheaf _).map (directCoefficientMap α β q p h N).val =
    toSheafify J ((Functor.const Cᵒᵖ).obj
      ((forget₂ (ModuleCat.{t + 1} D) AddCommGrpCat.{t + 1}).obj N)) := by
  unfold directCoefficientMap
  erw [PresheafOfModules.comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom]
  rfl

private lemma directCoefficientMap_underlying (N : ModuleCat.{t + 1} D) :
    (SheafOfModules.toSheaf R).map (directCoefficientMap α β q p h N) =
      𝟙 ((constantSheaf J AddCommGrpCat.{t + 1}).obj
        ((forget₂ (ModuleCat.{t + 1} D) AddCommGrpCat.{t + 1}).obj N)) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _
    ((constantSheaf J AddCommGrpCat.{t + 1}).obj
      ((forget₂ (ModuleCat.{t + 1} D) AddCommGrpCat.{t + 1}).obj N)).property
  change toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of N)) ≫
      (PresheafOfModules.toPresheaf R.obj).map (directCoefficientMap α β q p h N).val =
    toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of N)) ≫ 𝟙 _
  convert! directCoefficientMap_unit α β q p h N using 1

private def directCoefficientIso :
    ModuleCat.restrictScalars q ⋙ directConstant α ≅
      directConstant β ⋙ SheafOfModules.restrictScalars p := by
  have (N : ModuleCat.{t + 1} D) : IsIso (directCoefficientMap α β q p h N) := by
    have hh : IsIso (𝟙 ((constantSheaf J AddCommGrpCat.{t + 1}).obj
        ((forget₂ (ModuleCat.{t + 1} D) AddCommGrpCat.{t + 1}).obj N))) := inferInstance
    have : IsIso ((SheafOfModules.toSheaf R).map
        (directCoefficientMap α β q p h N)) := by
      convert! hh using 1
      exact directCoefficientMap_underlying α β q p h N
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)
  refine NatIso.ofComponents (fun N ↦ asIso (directCoefficientMap α β q p h N)) ?_
  intro M N f
  apply (SheafOfModules.toSheaf R).map_injective
  simp only [Functor.map_comp, asIso_hom, directCoefficientMap_underlying]
  rfl

private lemma directCoefficientIso_hom_app (N : ModuleCat.{t + 1} D) :
    (directCoefficientIso α β q p h).hom.app N = directCoefficientMap α β q p h N := rfl

variable (V : C)
  [HasWeakSheafify (J.over V) AddCommGrpCat.{t + 1}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
  [Presheaf.IsLocallyInjective (J.over V) (whiskerLeft (Over.forget V).op α)]
  [Presheaf.IsLocallySurjective (J.over V) (whiskerLeft (Over.forget V).op α)]

private def overDirectMap (N : ModuleCat.{t + 1} B) :
    (directConstant (R := R.over V) (whiskerLeft (Over.forget V).op α)).obj N ⟶
      ((directConstant α).obj N).over V :=
  (PresheafOfModules.sheafificationHomEquiv (R := R.over V)
    (whiskerLeft (Over.forget V).op α)
    (F := ((directConstant α).obj N).over V)).symm
      ((PresheafOfModules.pushforward (F := Over.forget V) (𝟙 _)).map
        (directConstantUnit α N))

attribute [local irreducible] overDirectMap

end ConstantPresentation

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
section
variable {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{t + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
  {B : Type (t + 1)} [CommRing B] {R : Sheaf J RingCat.{t + 1}}
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

variable {D : Type (t + 1)} [CommRing D] {S : Sheaf J RingCat.{t + 1}}
  (β : (Functor.const Cᵒᵖ).obj (RingCat.of D) ⟶ S.obj)
  [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
  (q : B →+* D) (p : R ⟶ S)
  (h : ∀ Z, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z)

end
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
