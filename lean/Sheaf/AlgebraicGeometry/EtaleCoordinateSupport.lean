/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Sheaf.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek

/-!
# Sheaf support and normalized coordinate germ comparisons

Source: Stacks Project, Tag 09XP, and steps 1, 5, 7 of the relative normal-slice
argument (blueprint: def-pur-etale-coordinate-support).

The sheaf support functor is the kernel of the open-complement adjunction unit.
The supported-stalk and global-to-stalk maps are fixed by their kernel-inclusion
equations; their derived transformations use the published derived base-change API.

## Main declarations

- `Etale.coordinateSupportSheaf`: the sheaf kernel, with its inclusion.
- `Etale.coordinateSupportedStalkDerivationIso`: the stalk of derived support.
- `Etale.coordinateDerivedGlobalToStalk`: the normalized derived global-to-stalk comparison.
- `Etale.coordinateDerivedGlobalToStalk_restriction`: its etale restriction square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

attribute [instance] CategoryTheory.GrothendieckTopology.Point.sheafFiber_additive

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A]

/-- The sheaf of sections with closed support, defined by its actual kernel.
Source: Stacks 09XP, subsheaf H_Z (blueprint: def-pur-etale-coordinate-support). -/
def coordinateSupportSheaf (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  kernel (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i.openComplement.ι).unit

/-- The supported-sheaf inclusion is the canonical kernel inclusion.
Source: Stacks 09XP (blueprint: def-pur-etale-coordinate-support). -/
def coordinateSupportInclusion {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    coordinateSupportSheaf A i ⟶ 𝟭 _ :=
  kernel.ι _

/-- Additivity of the support kernel, needed for its derived functor.
Source: Stacks 09XP (blueprint: def-pur-etale-coordinate-support).
Proof: compose the addition equation with the monic kernel inclusion; the remaining
identity is additivity of the identity functor. Cancel that inclusion. -/
@[instance] theorem coordinateSupportSheaf_additive {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] : (coordinateSupportSheaf A i).Additive := by
  constructor
  intro F G f g
  have : Mono ((coordinateSupportInclusion A i).app G) := by
    dsimp [coordinateSupportInclusion]
    infer_instance
  apply (cancel_mono ((coordinateSupportInclusion A i).app G)).1
  simp only [Preadditive.add_comp, (coordinateSupportInclusion A i).naturality,
    Functor.id_map, Preadditive.comp_add]

/-- The underived supported stalk, using the recorded geometric fibre functor.
Source: Stacks 09XP and the pointed-neighbourhood colimit definition
(blueprint: def-pur-etale-coordinate-support). -/
def coordinateSupportedStalk {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  coordinateSupportSheaf A i ⋙ ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A))

/-- Additivity of the supported stalk.
Source: Stacks 09XP (blueprint: def-pur-etale-coordinate-support).
Proof: the support kernel is additive and the geometric fibre functor is additive;
their composite is therefore additive. -/
@[instance] theorem coordinateSupportedStalk_additive {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ X) : (coordinateSupportedStalk A i t).Additive := by
  unfold coordinateSupportedStalk
  infer_instance

/-- The supported-sheaf functor preserves injectives.
Source: Stacks 09XP, closed-support adjunction, and DAG step 1
(blueprint: def-pur-etale-coordinate-support).
Proof: the support kernel is `i_* i!`. The closed direct image is exact and is right
adjoint to exact inverse image. Thus both `i!` and `i_*` preserve injectives, by
adjunction to exact functors, and so does their composite. -/
@[instance] theorem coordinateSupportSheaf_preservesInjectives {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (coordinateSupportSheaf A i).PreservesInjectiveObjects := by
  let M := ModuleCat.{u + 1} A
  let j := i.openComplement.ι
  have hij : Set.range i.base = (Set.range j.base)ᶜ :=
    i.range_eq_compl_range_openComplement_ι
  let : (closedUpperShriek M i j).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (lowerStarClosedUpperShriekAdjunction M i j hij)
  let : (lowerStar M i).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction M i)
  constructor
  intro I hI
  let := hI
  have hu := isIso_upperStarLowerStarAdjunction_unit_app_of_isZero M i j hij
    (isZero_upperStar_sectionsWithSupport M j I)
  have hs : Injective ((sectionsWithSupport M j).obj I) :=
    Injective.of_iso
      (asIso ((upperStarLowerStarAdjunction M i).unit.app
        ((sectionsWithSupport M j).obj I))).symm
      (show Injective (((closedUpperShriek M i j) ⋙ lowerStar M i).obj I) from
        inferInstance)
  exact Injective.of_iso
    (PreservesKernel.iso ((evaluation _ _).obj I)
      (upperStarLowerStarAdjunction M j).unit).symm hs

/-- Deriving the supported stalk is canonically the stalk of derived sheaf support.
Source: Stacks 09XP and DAG step 1
(blueprint: def-pur-etale-coordinate-support). -/
def coordinateSupportedStalkDerivationIso {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ X) :
    (coordinateSupportedStalk A i t).rightDerivedFunctorPlus ≅
      (coordinateSupportSheaf A i).rightDerivedFunctorPlus ⋙
        ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).mapDerivedCategoryPlus :=
  Functor.rightDerivedFunctorPlusCompIso (coordinateSupportSheaf A i)
      ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)))

/-- The inclusion of supported germs into all germs.
Source: Stacks 09XP (blueprint: def-pur-etale-coordinate-support). -/
def coordinateSupportedStalkInclusion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ X) :
    coordinateSupportedStalk A i t ⟶
      ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)) :=
  Functor.whiskerRight (coordinateSupportInclusion A i) _

/-- Global supported sections are the already recorded kernel-of-restriction functor.
Source: Stacks 09XP (blueprint: def-pur-etale-coordinate-support). -/
abbrev coordinateGlobalSupport {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  Sheaf.supportedSectionsFunctor X.smallEtaleTopology (ModuleCat.{u + 1} A)
    (supportRestrictionArrow i)

/-- Restriction from global sections to a geometric germ, then the actual pullback-stalk
identification. Source: Stacks 09XP and the geometric stalk colimit
(blueprint: def-pur-etale-coordinate-support). -/
def coordinateGlobalGerm {X T : Scheme.{u}} (f : T ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) ⟶
      ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).obj
        ((upperStar (ModuleCat.{u + 1} A) f).obj F) :=
  (Scheme.pointSmallEtale (t ≫ f)).toPresheafFiber
      (Scheme.Etale.mk (𝟙 X)) (Over.homMk (t ≫ f) (by simp)) F.obj ≫
    (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) f t).inv.app F

private theorem supportPullback_isZero {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (f : T ⟶ X) (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsZero ((upperStar (ModuleCat.{u + 1} A) i'.openComplement.ι).obj
      ((upperStar (ModuleCat.{u + 1} A) f).obj ((coordinateSupportSheaf A i).obj F))) := by
  let M := ModuleCat.{u + 1} A
  let j := i.openComplement.ι
  let j' := i'.openComplement.ι
  have hr : Set.range (j' ≫ f).base ⊆ Set.range j.base := by
    rintro _ ⟨y, rfl⟩
    change f.base (j'.base y) ∈ Set.range i.openComplement.ι.base
    rw [← compl_compl (Set.range i.openComplement.ι.base),
      ← i.range_eq_compl_range_openComplement_ι]
    intro h
    have hy : j'.base y ∈ Set.range i'.base := hf.symm ▸ h
    rw [i'.range_eq_compl_range_openComplement_ι] at hy
    exact hy ⟨y, rfl⟩
  let g := IsOpenImmersion.lift j (j' ≫ f) hr
  have hg : g ≫ j = j' ≫ f := IsOpenImmersion.lift_fac j (j' ≫ f) hr
  have hs : IsZero ((upperStar M j).obj ((coordinateSupportSheaf A i).obj F)) :=
    (isZero_upperStar_sectionsWithSupport M j F).of_iso
      ((upperStar M j).mapIso (PreservesKernel.iso ((evaluation _ _).obj F)
        (upperStarLowerStarAdjunction M j).unit))
  exact ((upperStar M g).map_isZero hs).of_iso
    (((upperStarComp M j' f (j' ≫ f) rfl).symm ≪≫
      upperStarComp M g j (j' ≫ f) hg.symm).app ((coordinateSupportSheaf A i).obj F))

set_option backward.isDefEq.respectTransparency false in
private theorem supportPullback_zero {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (f : T ⟶ X) (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (upperStar (ModuleCat.{u + 1} A) f).map ((coordinateSupportInclusion A i).app F) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i'.openComplement.ι).unit.app
        ((upperStar (ModuleCat.{u + 1} A) f).obj F) = 0 := by
  let M := ModuleCat.{u + 1} A
  let j := i'.openComplement.ι
  let η := (upperStarLowerStarAdjunction M j).unit
  let a : (upperStar M f).obj ((coordinateSupportSheaf A i).obj F) ⟶
      (upperStar M f).obj F :=
    (upperStar M f).map ((coordinateSupportInclusion A i).app F)
  have hzero := (supportPullback_isZero A i i' f hf F).eq_of_src
    ((upperStar M j).map a) 0
  calc
    a ≫ η.app _ = η.app _ ≫ (lowerStar M j).map ((upperStar M j).map a) :=
      η.naturality a
    _ = 0 := by rw [hzero, Functor.map_zero, comp_zero]

set_option backward.isDefEq.respectTransparency false in
private def supportPullback {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (f : T ⟶ X) (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base) :
    coordinateSupportSheaf A i ⋙ upperStar (ModuleCat.{u + 1} A) f ⟶
      upperStar (ModuleCat.{u + 1} A) f ⋙ coordinateSupportSheaf A i' := by
  let M := ModuleCat.{u + 1} A
  let η := (upperStarLowerStarAdjunction M i'.openComplement.ι).unit
  let a := Functor.whiskerRight (coordinateSupportInclusion A i) (upperStar M f)
  let ev (F : Sheaf X.smallEtaleTopology M) :=
    (evaluation (Sheaf T.smallEtaleTopology M) (Sheaf T.smallEtaleTopology M)).obj
      ((upperStar M f).obj F)
  let k (F : Sheaf X.smallEtaleTopology M) :=
    KernelFork.mapIsLimit _ (kernelIsKernel η) (ev F)
  let l (F : Sheaf X.smallEtaleTopology M) :=
    KernelFork.IsLimit.lift' (k F) (a.app F) (supportPullback_zero A i i' f hf F)
  have hl (F : Sheaf X.smallEtaleTopology M) :
      (l F).1 ≫ (coordinateSupportInclusion A i').app ((upperStar M f).obj F) =
        a.app F := (l F).2
  exact {
    app F := (l F).1
    naturality F G φ := by
      have : Mono ((coordinateSupportInclusion A i').app ((upperStar M f).obj G)) := by
        dsimp [coordinateSupportInclusion]
        infer_instance
      apply (cancel_mono ((coordinateSupportInclusion A i').app
        ((upperStar M f).obj G))).1
      dsimp only [Functor.comp_map]
      rw [Category.assoc, hl, Category.assoc,
        show (coordinateSupportSheaf A i').map ((upperStar M f).map φ) ≫
            (coordinateSupportInclusion A i').app ((upperStar M f).obj G) =
          (coordinateSupportInclusion A i').app ((upperStar M f).obj F) ≫
            (upperStar M f).map φ from
          (coordinateSupportInclusion A i').naturality ((upperStar M f).map φ),
        ← Category.assoc, hl]
      exact a.naturality φ }

set_option backward.isDefEq.respectTransparency false in
private theorem supportPullback_inclusion {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (f : T ⟶ X) (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (supportPullback A i i' f hf).app F ≫
        (coordinateSupportInclusion A i').app ((upperStar (ModuleCat.{u + 1} A) f).obj F) =
      (upperStar (ModuleCat.{u + 1} A) f).map ((coordinateSupportInclusion A i).app F) := by
  let M := ModuleCat.{u + 1} A
  let η := (upperStarLowerStarAdjunction M i'.openComplement.ι).unit
  let ev := (evaluation (Sheaf T.smallEtaleTopology M)
    (Sheaf T.smallEtaleTopology M)).obj ((upperStar M f).obj F)
  exact (KernelFork.IsLimit.lift' (KernelFork.mapIsLimit _ (kernelIsKernel η) ev)
    ((upperStar M f).map ((coordinateSupportInclusion A i).app F))
    (supportPullback_zero A i i' f hf F)).2

set_option backward.isDefEq.respectTransparency false in
private theorem globalSupport_unit_zero {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    kernel.ι (F.obj.map (supportRestrictionArrow i).op) ≫
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        i.openComplement.ι).unit.app F).hom.app (op (Scheme.Etale.mk (𝟙 X))) = 0 := by
  let M := ModuleCat.{u + 1} A
  let j := i.openComplement.ι
  let adj := upperStarLowerStarAdjunction M j
  let adj' := localizationRestrictionLowerStarAdjunction M j inferInstance
  let c := adj.leftAdjointUniq adj'
  have hu : adj.unit.app F = adj'.unit.app F ≫ (lowerStar M j).map (c.inv.app F) := by
    have h := congrArg (fun k ↦ k ≫ (lowerStar M j).map (c.inv.app F))
      (adj.unit_leftAdjointUniq_hom_app adj' F)
    change (adj.unit.app F ≫ (lowerStar M j).map (c.hom.app F)) ≫
      (lowerStar M j).map (c.inv.app F) = _ at h
    rw [Category.assoc, ← Functor.map_comp] at h
    erw [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h
  rw [hu]
  change kernel.ι _ ≫ ((adj'.unit.app F).hom.app _) ≫ _ = 0
  have hz : kernel.ι (F.obj.map (supportRestrictionArrow i).op) ≫
      (adj'.unit.app F).hom.app (op (Scheme.Etale.mk (𝟙 X))) = 0 := by
    let U := Scheme.Etale.mk (𝟙 X)
    let V := (MorphismProperty.Over.pullback @Etale ⊤ j).obj U
    let W := (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj V
    let a : W ⟶ U :=
      (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance trivial).counit.app U
    let b : W ⟶ Scheme.Etale.mk j :=
      MorphismProperty.Over.homMk (pullback.snd U.hom j) (by simp [W, V])
    have hab : a = b ≫ supportRestrictionArrow i := by
      apply MorphismProperty.Over.Hom.ext
      change pullback.fst (𝟙 X) j = pullback.snd (𝟙 X) j ≫ j
      simpa using (pullback.condition (f := 𝟙 X) (g := j))
    change kernel.ι _ ≫ F.obj.map a.op = 0
    rw [hab, op_comp, F.obj.map_comp, ← Category.assoc, kernel.condition, zero_comp]
  rw [← Category.assoc, hz, zero_comp]

set_option backward.isDefEq.respectTransparency false in
private def globalSupportSection {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (coordinateGlobalSupport A i).obj F ⟶
      ((coordinateSupportSheaf A i).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X))) := by
  let M := ModuleCat.{u + 1} A
  let ev := (evaluation (Sheaf X.smallEtaleTopology M)
      (Sheaf X.smallEtaleTopology M)).obj F ⋙ sheafToPresheaf X.smallEtaleTopology M ⋙
    (evaluation X.Etaleᵒᵖ M).obj (op (Scheme.Etale.mk (𝟙 X)))
  exact (KernelFork.IsLimit.lift'
    (KernelFork.mapIsLimit _ (kernelIsKernel
      (upperStarLowerStarAdjunction M i.openComplement.ι).unit) ev)
    (kernel.ι (F.obj.map (supportRestrictionArrow i).op)) (globalSupport_unit_zero A i F)).1

set_option backward.isDefEq.respectTransparency false in
private theorem globalSupportSection_inclusion {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    globalSupportSection A i F ≫ ((coordinateSupportInclusion A i).app F).hom.app
        (op (Scheme.Etale.mk (𝟙 X))) =
      kernel.ι (F.obj.map (supportRestrictionArrow i).op) := by
  let M := ModuleCat.{u + 1} A
  let ev := (evaluation (Sheaf X.smallEtaleTopology M)
      (Sheaf X.smallEtaleTopology M)).obj F ⋙ sheafToPresheaf X.smallEtaleTopology M ⋙
    (evaluation X.Etaleᵒᵖ M).obj (op (Scheme.Etale.mk (𝟙 X)))
  exact (KernelFork.IsLimit.lift'
    (KernelFork.mapIsLimit _ (kernelIsKernel
      (upperStarLowerStarAdjunction M i.openComplement.ι).unit) ev)
    (kernel.ι (F.obj.map (supportRestrictionArrow i).op)) (globalSupport_unit_zero A i F)).2

set_option backward.isDefEq.respectTransparency false in
private theorem globalGerm_naturality {X T : Scheme.{u}} (f : T ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)} (φ : F ⟶ G) :
    coordinateGlobalGerm A f t F ≫
        ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).map
          ((upperStar (ModuleCat.{u + 1} A) f).map φ) =
      φ.hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫ coordinateGlobalGerm A f t G := by
  unfold coordinateGlobalGerm
  erw [Category.assoc, ← (upperStarCompSheafFiberIso _ f t).inv.naturality φ,
    ← Category.assoc]
  erw [(Scheme.pointSmallEtale (t ≫ f)).toPresheafFiber_naturality φ.hom]
  exact Category.assoc _ _ _

private def globalSupportedGerm {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (f : T ⟶ X) (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (coordinateGlobalSupport A i).obj F ⟶
      (coordinateSupportedStalk A i' t).obj ((upperStar (ModuleCat.{u + 1} A) f).obj F) :=
  globalSupportSection A i F ≫ coordinateGlobalGerm A f t ((coordinateSupportSheaf A i).obj F) ≫
    ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).map
      ((supportPullback A i i' f hf).app F)

set_option backward.isDefEq.respectTransparency false in
private theorem globalSupportedGerm_inclusion {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (f : T ⟶ X) (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    globalSupportedGerm A i i' f hf t F ≫ (coordinateSupportedStalkInclusion A i' t).app
        ((upperStar (ModuleCat.{u + 1} A) f).obj F) =
      kernel.ι (F.obj.map (supportRestrictionArrow i).op) ≫ coordinateGlobalGerm A f t F := by
  let Φ := (Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)
  change (globalSupportSection A i F ≫ coordinateGlobalGerm A f t
    ((coordinateSupportSheaf A i).obj F) ≫ Φ.map ((supportPullback A i i' f hf).app F)) ≫
      Φ.map ((coordinateSupportInclusion A i').app ((upperStar _ f).obj F)) = _
  rw [Category.assoc, Category.assoc, ← Φ.map_comp,
    supportPullback_inclusion]
  erw [globalGerm_naturality]
  rw [← Category.assoc, globalSupportSection_inclusion]
  rfl

/-- Pullback of a supported global section is the unique supported germ with the specified
underlying germ. The support equality is the inverse-image condition on closed pairs.
Source: Stacks 09XP, kernel construction (blueprint: def-pur-etale-coordinate-support).
Proof: pull back the restriction equation to the inverse-image complement. The germ
therefore lies in the support kernel. Exactness of the geometric fibre functor
identifies its kernel with the fibre of the kernel sheaf. The kernel universal property
gives existence, naturality, and uniqueness. -/
theorem coordinateGlobalToStalk_existsUnique {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (f : T ⟶ X) (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ∃! m : coordinateGlobalSupport A i ⟶
        upperStar (ModuleCat.{u + 1} A) f ⋙ coordinateSupportedStalk A i' t,
      ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
        m.app F ≫ (coordinateSupportedStalkInclusion A i' t).app
            ((upperStar (ModuleCat.{u + 1} A) f).obj F) =
          kernel.ι (F.obj.map (supportRestrictionArrow i).op) ≫
            coordinateGlobalGerm A f t F := by
  let M := ModuleCat.{u + 1} A
  let Φ := (Scheme.pointSmallEtale t).sheafFiber (A := M)
  have hmono (F : Sheaf X.smallEtaleTopology M) :
      Mono ((coordinateSupportedStalkInclusion A i' t).app ((upperStar M f).obj F)) := by
    dsimp [coordinateSupportedStalkInclusion, coordinateSupportInclusion]
    infer_instance
  let m : coordinateGlobalSupport A i ⟶ upperStar M f ⋙ coordinateSupportedStalk A i' t := {
    app F := globalSupportedGerm A i i' f hf t F
    naturality F G φ := by
      apply (cancel_mono
        ((coordinateSupportedStalkInclusion A i' t).app ((upperStar M f).obj G))).1
      change ((coordinateGlobalSupport A i).map φ ≫ _) ≫ _ =
        (globalSupportedGerm A i i' f hf t F ≫
          (coordinateSupportedStalk A i' t).map ((upperStar M f).map φ)) ≫ _
      rw [Category.assoc, globalSupportedGerm_inclusion, Category.assoc,
        (coordinateSupportedStalkInclusion A i' t).naturality]
      rw [← Category.assoc (globalSupportedGerm A i i' f hf t F),
        globalSupportedGerm_inclusion, Category.assoc, globalGerm_naturality,
        ← Category.assoc]
      dsimp only [coordinateGlobalSupport, Sheaf.supportedSectionsFunctor]
      simp only [kernel.map, kernel.lift_ι, Category.assoc] }
  refine ⟨m, globalSupportedGerm_inclusion A i i' f hf t, ?_⟩
  intro n hn
  apply NatTrans.ext
  funext F
  apply (cancel_mono
    ((coordinateSupportedStalkInclusion A i' t).app ((upperStar M f).obj F))).1
  exact (hn F).trans (globalSupportedGerm_inclusion A i i' f hf t F).symm


/-- The canonical, kernel-normalized map on supported germs, with no arbitrary isomorphism
chosen. Source: Stacks 09XP (blueprint: def-pur-etale-coordinate-support). -/
def coordinateGlobalToStalk {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (f : T ⟶ X) (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    coordinateGlobalSupport A i ⟶
      upperStar (ModuleCat.{u + 1} A) f ⋙ coordinateSupportedStalk A i' t :=
  (coordinateGlobalToStalk_existsUnique A i i' f hf t).choose

/-- Derive the canonical pullback-to-supported-germ map using the right-derived base-change
construction. Source: Stacks 09XP and DAG steps 1, 5
(blueprint: def-pur-etale-coordinate-support). -/
def coordinateDerivedGlobalToStalk {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (f : T ⟶ X) (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    (coordinateGlobalSupport A i).rightDerivedFunctorPlus ⟶
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus ⋙
        (coordinateSupportedStalk A i' t).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := coordinateGlobalSupport A i) (G' := coordinateSupportedStalk A i' t)
      (β := upperStar (ModuleCat.{u + 1} A) f) (γ := 𝟭 (ModuleCat.{u + 1} A))
      ((Functor.rightUnitor _).hom ≫ coordinateGlobalToStalk A i i' f hf t)

/-- Restriction of a supported germ is uniquely fixed by restriction of the underlying
germ. Source: Stacks 09XP and DAG steps 5, 7
(blueprint: def-pur-etale-coordinate-support).
Proof: the inverse-image support condition identifies the two complement kernels.
Exact stalks preserve this kernel. The pullback-stalk isomorphism carries one inclusion
to the other; factor through the kernel and cancel its monic inclusion for uniqueness. -/
theorem coordinateStalkRestriction_existsUnique {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (e : T ⟶ X) [Etale e]
    (he : Set.range i'.base = e.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ∃! m : coordinateSupportedStalk A i (t ≫ e) ⟶
        upperStar (ModuleCat.{u + 1} A) e ⋙ coordinateSupportedStalk A i' t,
      m ≫ Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) e)
          (coordinateSupportedStalkInclusion A i' t) =
        coordinateSupportedStalkInclusion A i (t ≫ e) ≫
          (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) e t).inv := by
  let M := ModuleCat.{u + 1} A
  let Φ := (Scheme.pointSmallEtale t).sheafFiber (A := M)
  let c := upperStarCompSheafFiberIso M e t
  let m : coordinateSupportedStalk A i (t ≫ e) ⟶
      upperStar M e ⋙ coordinateSupportedStalk A i' t :=
    Functor.whiskerLeft (coordinateSupportSheaf A i) c.inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (supportPullback A i i' e he) Φ ≫
      (Functor.associator _ _ _).hom
  have hm : m ≫ Functor.whiskerLeft (upperStar M e)
      (coordinateSupportedStalkInclusion A i' t) =
    coordinateSupportedStalkInclusion A i (t ≫ e) ≫ c.inv := by
    apply NatTrans.ext
    funext F
    change (c.inv.app ((coordinateSupportSheaf A i).obj F) ≫
      Φ.map ((supportPullback A i i' e he).app F)) ≫
        Φ.map ((coordinateSupportInclusion A i').app ((upperStar M e).obj F)) =
      ((Scheme.pointSmallEtale (t ≫ e)).sheafFiber (A := M)).map
        ((coordinateSupportInclusion A i).app F) ≫ c.inv.app F
    rw [Category.assoc, ← Φ.map_comp]
    exact (congrArg (fun k ↦ c.inv.app ((coordinateSupportSheaf A i).obj F) ≫ Φ.map k)
      (supportPullback_inclusion A i i' e he F)).trans
        (c.inv.naturality ((coordinateSupportInclusion A i).app F)).symm
  refine ⟨m, hm, ?_⟩
  intro n hn
  apply NatTrans.ext
  funext F
  have : Mono ((coordinateSupportedStalkInclusion A i' t).app ((upperStar M e).obj F)) := by
    dsimp [coordinateSupportedStalkInclusion, coordinateSupportInclusion]
    infer_instance
  apply (cancel_mono
    ((coordinateSupportedStalkInclusion A i' t).app ((upperStar M e).obj F))).1
  exact congr_app (hn.trans hm.symm) F


/-- The actual restriction map of supported germs, fixed by its inclusion equation.
Source: Stacks 09XP (blueprint: def-pur-etale-coordinate-support). -/
def coordinateStalkRestriction {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (e : T ⟶ X) [Etale e]
    (he : Set.range i'.base = e.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    coordinateSupportedStalk A i (t ≫ e) ⟶
      upperStar (ModuleCat.{u + 1} A) e ⋙ coordinateSupportedStalk A i' t :=
  (coordinateStalkRestriction_existsUnique A i i' e he t).choose

/-- Derive literal etale restriction on supported germs.
Source: Stacks 09XP and DAG step 7
(blueprint: def-pur-etale-coordinate-support). -/
def coordinateDerivedStalkRestriction {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (e : T ⟶ X) [Etale e]
    (he : Set.range i'.base = e.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    (coordinateSupportedStalk A i (t ≫ e)).rightDerivedFunctorPlus ⟶
      (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategoryPlus ⋙
        (coordinateSupportedStalk A i' t).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := coordinateSupportedStalk A i (t ≫ e))
      (G' := coordinateSupportedStalk A i' t)
      (β := upperStar (ModuleCat.{u + 1} A) e) (γ := 𝟭 (ModuleCat.{u + 1} A))
      ((Functor.rightUnitor _).hom ≫ coordinateStalkRestriction A i i' e he t)

/-- The exact inverse-image composition isomorphism on bounded-below complexes.
Source: inverse-image composition and DAG step 7
(blueprint: def-pur-etale-coordinate-support). -/
def coordinateDerivedPullbackComp {X T V : Scheme.{u}} (f : T ⟶ X) (e : V ⟶ T) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategoryPlus ≅
      (upperStar (ModuleCat.{u + 1} A) (e ≫ f)).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso
    (upperStar (ModuleCat.{u + 1} A) f) (upperStar (ModuleCat.{u + 1} A) e)).symm ≪≫
    (Functor.mapDerivedCategoryPlusNatIso
      (upperStarComp (ModuleCat.{u + 1} A) e f (e ≫ f) rfl)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackGerm_formula {X T : Scheme.{u}} (f : T ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (U : X.Etale)
    (x : (Scheme.pointSmallEtale (t ≫ f)).fiber.obj U) :
    (Scheme.pointSmallEtale (t ≫ f)).toPresheafFiber U x F.obj ≫
        (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) f t).inv.app F =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app F).hom.app
          (op U) ≫
        (Scheme.pointSmallEtale t).toPresheafFiber (f.Etale.obj U)
          ((Scheme.pointSmallEtaleFiberEtaleIso f t).inv.app U x)
          ((upperStar (ModuleCat.{u + 1} A) f).obj F).obj := by
  simp only [upperStarCompSheafFiberIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) (ModuleCat.{u + 1} A)
      (X.smallGrothendieckTopology (P := @Etale))
      (T.smallGrothendieckTopology (P := @Etale)))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f) F
  have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op U)
  rw [← Category.assoc, ← huU]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem globalGerm_comp {X T V : Scheme.{u}} (f : T ⟶ X) (e : V ⟶ T)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ V)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    coordinateGlobalGerm A f (t ≫ e) F ≫
        (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) e t).inv.app
          ((upperStar (ModuleCat.{u + 1} A) f).obj F) ≫
        ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).map
          ((upperStarComp (ModuleCat.{u + 1} A) e f (e ≫ f) rfl).inv.app F) =
      coordinateGlobalGerm A (e ≫ f) t F := by
  let M := ModuleCat.{u + 1} A
  let U := Scheme.Etale.mk (𝟙 X)
  let x : (Scheme.pointSmallEtale ((t ≫ e) ≫ f)).fiber.obj U :=
    Over.homMk ((t ≫ e) ≫ f) (by simp [U])
  let y := (Scheme.pointSmallEtaleFiberEtaleIso f (t ≫ e)).inv.app U x
  let z := (Scheme.pointSmallEtaleFiberEtaleIso e t).inv.app (f.Etale.obj U) y
  let w : (Scheme.pointSmallEtale (t ≫ (e ≫ f))).fiber.obj U :=
    Over.homMk (t ≫ (e ≫ f)) (by simp [U])
  let v := (Scheme.pointSmallEtaleFiberEtaleIso (e ≫ f) t).inv.app U w
  let c := upperStarComp M e f (e ≫ f) rfl
  let Φ := (Scheme.pointSmallEtale t).sheafFiber (A := M)
  apply (cancel_mono (Φ.map (c.hom.app F))).1
  change (coordinateGlobalGerm A f (t ≫ e) F ≫
    (upperStarCompSheafFiberIso M e t).inv.app ((upperStar M f).obj F) ≫
    Φ.map (c.inv.app F)) ≫ Φ.map (c.hom.app F) = _
  rw [Category.assoc, Category.assoc, ← Φ.map_comp, Iso.inv_hom_id_app]
  erw [Φ.map_id, Category.comp_id]
  change ((Scheme.pointSmallEtale ((t ≫ e) ≫ f)).toPresheafFiber U x F.obj ≫
    (upperStarCompSheafFiberIso M f (t ≫ e)).inv.app F) ≫
    (upperStarCompSheafFiberIso M e t).inv.app ((upperStar M f).obj F) =
    ((Scheme.pointSmallEtale (t ≫ (e ≫ f))).toPresheafFiber U w F.obj ≫
      (upperStarCompSheafFiberIso M (e ≫ f) t).inv.app F) ≫ Φ.map (c.hom.app F)
  rw [pullbackGerm_formula, Category.assoc, pullbackGerm_formula,
    pullbackGerm_formula]
  have hn := (Scheme.pointSmallEtale t).toPresheafFiber_naturality (c.hom.app F).hom
    ((e ≫ f).Etale.obj U) v
  change _ = _ ≫ (Scheme.pointSmallEtale t).toPresheafFiber _ v _ ≫ Φ.map (c.hom.app F)
  erw [← Category.assoc, hn]
  rw [← Category.assoc]
  have hu := upperStarComp_hom_app_unit_app M e f F (e ≫ f) rfl
  have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op U)
  change ((upperStarLowerStarAdjunction M (e ≫ f)).unit.app F).hom.app (op U) ≫
      (c.hom.app F).hom.app (op ((e ≫ f).Etale.obj U)) =
    (((upperStarLowerStarAdjunction M f).unit.app F).hom.app (op U) ≫
      ((upperStarLowerStarAdjunction M e).unit.app ((upperStar M f).obj F)).hom.app
        (op (f.Etale.obj U))) ≫
      ((lowerStarComp M e f (e ≫ f) rfl).hom.app _).hom.app (op U) at huU
  erw [huU]
  erw [lowerStarComp_hom_app_hom_app M e f (e ≫ f) rfl]
  have hvz : (Scheme.pointSmallEtale t).fiber.map
      ((MorphismProperty.Over.pullbackComp e f (e ≫ f) rfl).hom.app U) v = z := by
    have : IsIso ((e.Etale.obj (f.Etale.obj U)).hom) := by
      change IsIso (pullback.snd (pullback.snd (𝟙 X) f) e)
      infer_instance
    apply Over.OverMorphism.ext
    apply (cancel_mono (e.Etale.obj (f.Etale.obj U)).hom).1
    exact (Over.w _).trans (Over.w _).symm
  have hg := (Scheme.pointSmallEtale t).toPresheafFiber_w
    ((MorphismProperty.Over.pullbackComp e f (e ≫ f) rfl).hom.app U) v
    ((upperStar M e).obj ((upperStar M f).obj F)).obj
  rw [hvz] at hg
  exact (congrArg (fun k ↦
    (((upperStarLowerStarAdjunction M f).unit.app F).hom.app (op U) ≫
      ((upperStarLowerStarAdjunction M e).unit.app ((upperStar M f).obj F)).hom.app
        (op (f.Etale.obj U))) ≫ k) hg.symm).trans (Category.assoc _ _ _).symm


set_option backward.isDefEq.respectTransparency false in
private theorem supportedGlobalGerm_comp
    {Z X Z' T Z'' V : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ T) [IsClosedImmersion i'] (i'' : Z'' ⟶ V) [IsClosedImmersion i'']
    (f : T ⟶ X) (e : V ⟶ T) [Etale e]
    (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    (he : Set.range i''.base = e.base ⁻¹' Set.range i'.base)
    (hef : Set.range i''.base = (e ≫ f).base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ V)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (coordinateGlobalToStalk A i i' f hf (t ≫ e)).app F ≫
        (coordinateStalkRestriction A i' i'' e he t).app
          ((upperStar (ModuleCat.{u + 1} A) f).obj F) ≫
        (coordinateSupportedStalk A i'' t).map
          ((upperStarComp (ModuleCat.{u + 1} A) e f (e ≫ f) rfl).inv.app F) =
      (coordinateGlobalToStalk A i i'' (e ≫ f) hef t).app F := by
  let M := ModuleCat.{u + 1} A
  let Φ := (Scheme.pointSmallEtale t).sheafFiber (A := M)
  let c := upperStarComp M e f (e ≫ f) rfl
  let I := coordinateSupportedStalkInclusion A i'' t
  have : Mono (I.app ((upperStar M (e ≫ f)).obj F)) := by
    dsimp [I, coordinateSupportedStalkInclusion, coordinateSupportInclusion]
    infer_instance
  apply (cancel_mono (I.app ((upperStar M (e ≫ f)).obj F))).1
  rw [Category.assoc, Category.assoc, I.naturality (c.inv.app F)]
  rw [← Category.assoc, ← Category.assoc]
  have hr := congr_app
    (coordinateStalkRestriction_existsUnique A i' i'' e he t).choose_spec.1
    ((upperStar M f).obj F)
  change (coordinateStalkRestriction A i' i'' e he t).app _ ≫ I.app _ =
    (coordinateSupportedStalkInclusion A i' (t ≫ e)).app _ ≫
      (upperStarCompSheafFiberIso M e t).inv.app _ at hr
  have hr' := congrArg (fun k ↦
    ((coordinateGlobalToStalk A i i' f hf (t ≫ e)).app F ≫ k) ≫
      Φ.map (c.inv.app F)) hr
  change ((coordinateGlobalToStalk A i i' f hf (t ≫ e)).app F ≫
    ((coordinateStalkRestriction A i' i'' e he t).app ((upperStar M f).obj F) ≫
      I.app ((upperStar M e).obj ((upperStar M f).obj F)))) ≫ Φ.map (c.inv.app F) = _
  rw [hr']
  rw [← Category.assoc]
  erw [(coordinateGlobalToStalk_existsUnique A i i' f hf (t ≫ e)).choose_spec.1 F]
  rw [Category.assoc, Category.assoc, globalGerm_comp]
  exact ((coordinateGlobalToStalk_existsUnique A i i'' (e ≫ f) hef t).choose_spec.1 F).symm

set_option backward.isDefEq.respectTransparency false in
private theorem normalizedBaseChange_fac
    {B B' C : Type*} [Category B] [Category B'] [Category C]
    [Abelian B] [Abelian B'] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C]
    [EnoughInjectives B] [EnoughInjectives B']
    (G : B ⥤ C) (H : B' ⥤ C) (P : B ⥤ B')
    [G.Additive] [H.Additive] [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (m : G ⟶ P ⋙ H) (K : HomotopyCategory.Plus B) :
    G.rightDerivedFunctorPlusUnit.app K ≫
      ((Functor.rightUnitor _).inv ≫
        (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso C)).inv ≫
        Functor.rightDerivedFunctorPlusBaseChange
          ((Functor.rightUnitor G).hom ≫ m)).app (DerivedCategory.Plus.Qh.obj K) =
    DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus m).app K) ≫
      H.rightDerivedFunctorPlusUnit.app (P.mapHomotopyCategoryPlus.obj K) ≫
      H.rightDerivedFunctorPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  let l := Functor.rightDerivedFunctorPlusBaseChange ((Functor.rightUnitor G).hom ≫ m)
  have hn := (Functor.mapDerivedCategoryPlusIdIso C).inv.naturality
    (G.rightDerivedFunctorPlusUnit.app K)
  simp only [Functor.id_map] at hn
  simp only [NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.id_comp]
  erw [← Category.assoc, hn, Category.assoc]
  have hf := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac
    ((Functor.rightUnitor G).hom ≫ m)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at hf
  rw [hf]
  simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  rw [← Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh]
  simp only [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app,
    NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app,
    CategoryTheory.Functor.map_id]
  erw [Iso.inv_hom_id_app_assoc]
  simp only [NatTrans.mapHomotopyCategoryPlus_rightUnitor_hom_app,
    Category.id_comp]
  erw [Category.id_comp, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem exactComp_factors
    {B B' B'' : Type*} [Category B] [Category B'] [Category B'']
    [Abelian B] [Abelian B'] [Abelian B'']
    [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory B'']
    (P : B ⥤ B') (Q : B' ⥤ B'') (R : B ⥤ B'')
    [P.Additive] [Q.Additive] [R.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (c : R ≅ P ⋙ Q) (K : HomotopyCategory.Plus B) :
    Q.mapDerivedCategoryPlusFactorsh.inv.app (P.mapHomotopyCategoryPlus.obj K) ≫
      Q.mapDerivedCategoryPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app K) ≫
      ((Functor.mapDerivedCategoryPlusCompIso P Q).inv ≫
        (Functor.mapDerivedCategoryPlusNatIso c).inv).app (DerivedCategory.Plus.Qh.obj K) =
    DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus c.inv).app K) ≫
      R.mapDerivedCategoryPlusFactorsh.inv.app K := by
  have : PreservesFiniteLimits (P ⋙ Q) := comp_preservesFiniteLimits P Q
  have : PreservesFiniteColimits (P ⋙ Q) := comp_preservesFiniteColimits P Q
  have hc := Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh c K
  have hi : (Functor.mapDerivedCategoryPlusNatIso c).inv.app
      (DerivedCategory.Plus.Qh.obj K) ≫ R.mapDerivedCategoryPlusFactorsh.hom.app K =
    (P ⋙ Q).mapDerivedCategoryPlusFactorsh.hom.app K ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus c.inv).app K) := by
    apply (cancel_epi ((Functor.mapDerivedCategoryPlusNatIso c).hom.app _)).1
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rw [hc, Category.assoc, ← DerivedCategory.Plus.Qh.map_comp]
    rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.hom_inv_id]
    simp only [NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app,
      DerivedCategory.Plus.Qh.map_id]
    exact (Category.comp_id _).symm
  have hp : (Functor.mapDerivedCategoryPlusCompIso P Q).inv.app
      (DerivedCategory.Plus.Qh.obj K) ≫ (P ⋙ Q).mapDerivedCategoryPlusFactorsh.hom.app K =
    Q.mapDerivedCategoryPlus.map (P.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      Q.mapDerivedCategoryPlusFactorsh.hom.app (P.mapHomotopyCategoryPlus.obj K) := by
    apply (cancel_epi ((Functor.mapDerivedCategoryPlusCompIso P Q).hom.app _)).1
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    simpa only [Category.assoc] using
      (Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh P Q K).symm
  apply (cancel_mono (R.mapDerivedCategoryPlusFactorsh.hom.app K)).1
  simp only [NatTrans.comp_app, Category.assoc]
  rw [hi, reassoc_of% hp]
  rw [← Q.mapDerivedCategoryPlus.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Q.mapDerivedCategoryPlus.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem derivedGerm_comp
    {B B' B'' C : Type*} [Category B] [Category B'] [Category B''] [Category C]
    [Abelian B] [Abelian B'] [Abelian B''] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory B'']
    [HasDerivedCategory C]
    [EnoughInjectives B] [EnoughInjectives B'] [EnoughInjectives B'']
    (G : B ⥤ C) (H : B' ⥤ C) (L : B'' ⥤ C)
    (P : B ⥤ B') (Q : B' ⥤ B'') (R : B ⥤ B'')
    [G.Additive] [H.Additive] [L.Additive]
    [P.Additive] [Q.Additive] [R.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (c : R ≅ P ⋙ Q) (m : G ⟶ P ⋙ H) (n : H ⟶ Q ⋙ L) (r : G ⟶ R ⋙ L)
    (h : ∀ F, m.app F ≫ n.app (P.obj F) ≫ L.map (c.inv.app F) = r.app F)
    (a : G.rightDerivedFunctorPlus ⟶ P.mapDerivedCategoryPlus ⋙ H.rightDerivedFunctorPlus)
    (b : H.rightDerivedFunctorPlus ⟶ Q.mapDerivedCategoryPlus ⋙ L.rightDerivedFunctorPlus)
    (d : G.rightDerivedFunctorPlus ⟶ R.mapDerivedCategoryPlus ⋙ L.rightDerivedFunctorPlus)
    (ha : ∀ K, G.rightDerivedFunctorPlusUnit.app K ≫
      a.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus m).app K) ≫
        H.rightDerivedFunctorPlusUnit.app (P.mapHomotopyCategoryPlus.obj K) ≫
        H.rightDerivedFunctorPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app K))
    (hb : ∀ K, H.rightDerivedFunctorPlusUnit.app K ≫
      b.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus n).app K) ≫
        L.rightDerivedFunctorPlusUnit.app (Q.mapHomotopyCategoryPlus.obj K) ≫
        L.rightDerivedFunctorPlus.map (Q.mapDerivedCategoryPlusFactorsh.inv.app K))
    (hd : ∀ K, G.rightDerivedFunctorPlusUnit.app K ≫
      d.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus r).app K) ≫
        L.rightDerivedFunctorPlusUnit.app (R.mapHomotopyCategoryPlus.obj K) ≫
        L.rightDerivedFunctorPlus.map (R.mapDerivedCategoryPlusFactorsh.inv.app K)) :
    a ≫ Functor.whiskerLeft P.mapDerivedCategoryPlus b ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ((Functor.mapDerivedCategoryPlusCompIso P Q).inv ≫
        (Functor.mapDerivedCategoryPlusNatIso c).inv) L.rightDerivedFunctorPlus = d := by
  refine Functor.rightDerived_ext G.rightDerivedFunctorPlus G.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso B) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp]
  rw [← Category.assoc, ha, hd]
  have hn := b.naturality (P.mapDerivedCategoryPlusFactorsh.inv.app K)
  have hu := L.rightDerivedFunctorPlusUnit.naturality
    ((NatTrans.mapHomotopyCategoryPlus c.inv).app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn hu
  simp only [Category.assoc]
  rw [reassoc_of% hn, reassoc_of% (hb (P.mapHomotopyCategoryPlus.obj K))]
  rw [← L.rightDerivedFunctorPlus.map_comp_assoc,
    ← L.rightDerivedFunctorPlus.map_comp, Category.assoc]
  have hf := exactComp_factors P Q R c K
  simp only [NatTrans.comp_app] at hf
  rw [hf]
  rw [L.rightDerivedFunctorPlus.map_comp]
  erw [← reassoc_of% hu]
  have ht : m ≫ Functor.whiskerLeft P n ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight c.inv L = r := by
    ext F
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.id_comp] using h F
  have hh : (NatTrans.mapHomotopyCategoryPlus m).app K ≫
      (NatTrans.mapHomotopyCategoryPlus n).app (P.mapHomotopyCategoryPlus.obj K) ≫
      L.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus c.inv).app K) =
    (NatTrans.mapHomotopyCategoryPlus r).app K := by
    have ht' := congrArg (fun k ↦ (NatTrans.mapHomotopyCategoryPlus k).app K) ht
    simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app] at ht'
    have hn' : (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerLeft P n)).app K =
        (NatTrans.mapHomotopyCategoryPlus n).app (P.mapHomotopyCategoryPlus.obj K) := rfl
    have hc' : (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerRight c.inv L)).app K =
        L.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus c.inv).app K) := rfl
    have hassoc : (NatTrans.mapHomotopyCategoryPlus
        (Functor.associator P Q L).inv).app K = 𝟙 _ := by
      rfl
    rw [hn', hc', hassoc, Category.id_comp] at ht'
    exact ht'
  rw [← DerivedCategory.Plus.Qh.map_comp_assoc,
    ← DerivedCategory.Plus.Qh.map_comp_assoc]
  rw [Category.assoc, hh]

/-- The coordinate comparison commutes with every further etale restriction.
The three support equalities just express the three inverse-image closed pairs.
Source: Stacks 09XP and DAG step 7
(blueprint: def-pur-etale-coordinate-support).
Proof: before deriving, both composites have the same underlying global germ by the
composition law for pullback stalks. Uniqueness in the two kernel factorizations gives
the same natural transformation. Derive this equation; the derived composition
isomorphism is the specified exact inverse-image composition, giving this square. -/
theorem coordinateDerivedGlobalToStalk_restriction
    {Z X Z' T Z'' V : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ T) [IsClosedImmersion i'] (i'' : Z'' ⟶ V) [IsClosedImmersion i'']
    (f : T ⟶ X) (e : V ⟶ T) [Etale e]
    (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    (he : Set.range i''.base = e.base ⁻¹' Set.range i'.base)
    (hef : Set.range i''.base = (e ≫ f).base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ V) :
    coordinateDerivedGlobalToStalk A i i' f hf (t ≫ e) ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus
        (coordinateDerivedStalkRestriction A i' i'' e he t) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (coordinateDerivedPullbackComp A f e).hom
        (coordinateSupportedStalk A i'' t).rightDerivedFunctorPlus =
      coordinateDerivedGlobalToStalk A i i'' (e ≫ f) hef t := by
  let M := ModuleCat.{u + 1} A
  exact derivedGerm_comp
    (coordinateGlobalSupport A i) (coordinateSupportedStalk A i' (t ≫ e))
    (coordinateSupportedStalk A i'' t) (upperStar M f) (upperStar M e)
    (upperStar M (e ≫ f)) (upperStarComp M e f (e ≫ f) rfl)
    (coordinateGlobalToStalk A i i' f hf (t ≫ e))
    (coordinateStalkRestriction A i' i'' e he t)
    (coordinateGlobalToStalk A i i'' (e ≫ f) hef t)
    (supportedGlobalGerm_comp A i i' i'' f e hf he hef t)
    (coordinateDerivedGlobalToStalk A i i' f hf (t ≫ e))
    (coordinateDerivedStalkRestriction A i' i'' e he t)
    (coordinateDerivedGlobalToStalk A i i'' (e ≫ f) hef t)
    (normalizedBaseChange_fac (coordinateGlobalSupport A i)
      (coordinateSupportedStalk A i' (t ≫ e)) (upperStar M f)
      (coordinateGlobalToStalk A i i' f hf (t ≫ e)))
    (normalizedBaseChange_fac (coordinateSupportedStalk A i' (t ≫ e))
      (coordinateSupportedStalk A i'' t) (upperStar M e)
      (coordinateStalkRestriction A i' i'' e he t))
    (normalizedBaseChange_fac (coordinateGlobalSupport A i)
      (coordinateSupportedStalk A i'' t) (upperStar M (e ≫ f))
      (coordinateGlobalToStalk A i i'' (e ≫ f) hef t))

end AlgebraicGeometry.Etale
