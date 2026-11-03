/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleCondensedCoefficientFamily
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomCocycleNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.Derived.DerivedRepresentableTransport
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsShortExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed

/-! # Supported Hom for pulled-back condensed coefficients

Source: latest blueprint, lem-pur-supported-hom, evaluation and injective-resolution
construction (blueprint: lem-pur-supported-hom).
This interface uses internal modules over the actual pulled-back condensed ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale.CondensedRing.Admissible

/-- The existing internal-module category. Source: det-def-sf-operations
(blueprint: lem-pur-supported-hom). -/
abbrev Modules (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)

/-- The regular coefficient unit. Source: lem-pur-supported-hom
(blueprint: lem-pur-supported-hom). -/
abbrev unit (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :=
  Mod.regular (condensedRingObj Λ.X X)

/-- The underived closed direct image, placed in degree zero only afterwards.
Source: lem-pur-supported-hom (blueprint: lem-pur-supported-hom). -/
abbrev source (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  (CondensedRing.lowerStar Λ.X i).obj (unit Λ Z)

/-- Kernel of restriction on the underlying sections, derived in the module category.
Source: def-pur-support-cohomology (blueprint: lem-pur-supported-hom). -/
abbrev sections (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Modules Λ X ⥤ Ab.{u + 1} :=
  Mod.forget _ ⋙ Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X)
    Ab.{u + 1} (supportRestrictionArrow i)

/-- The integral generator of the regular coefficient. Source: evaluation on one
(blueprint: lem-pur-supported-hom). -/
def generator (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ condensedRingObj Λ.X X :=
  (Functor.Monoidal.εIso (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1})).inv ≫ η

/-- Integral generator of the supported unit. Source: the closed restriction of one
(blueprint: lem-pur-supported-hom). -/
def supportedGenerator (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (ProEtale.lowerStar Ab.{u + 1} i).obj
      ((constantSheaf (Scheme.ProEt.topology Z) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ (source Λ i).X :=
  (ProEtale.lowerStar Ab.{u + 1} i).map (generator Λ Z)

/-- The underived evaluation comparison. Source: supported-Hom proof, steps 1--4
(blueprint: lem-pur-supported-hom). -/
abbrev Evaluation (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  preadditiveCoyoneda.obj (op (source Λ i)) ≅ sections Λ i

/-- Evaluation sends a module map to its value at the supported coefficient one.
Source: supported-Hom proof, step 4 (blueprint: lem-pur-supported-hom). -/
def EvaluationSpec (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (e : Evaluation Λ i) : Prop :=
  ∀ (M : Modules Λ X) (f : source Λ i ⟶ M),
    kernel.ι (M.X.obj.map (supportRestrictionArrow i).op) (e.hom.app M f) =
      ((constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
        (MorphismProperty.Over.mkIdTerminal _ X)).homEquiv _ _
          (Scheme.proEtaleConstantDirectImageMap i Ab.{u + 1}
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ supportedGenerator Λ i ≫ f.hom))
              (ULift.up 1)

private def regularRestriction (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) : unit Λ X ⟶ source Λ i :=
  Mod.regularToComapRegular (condensedPushforwardHom Λ.X i)

private def moduleSectionEquiv (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) (M : Modules Λ X) :
    (unit Λ X ⟶ M) ≃+ M.X.obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
  (Mod.regularHomAddEquiv M).trans
    (Sheaf.unitHomEvalAddEquiv (MorphismProperty.Over.mkIdTerminal _ X) M.X)

private theorem regularRestriction_closed_isIso
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    IsIso ((ProEtale.upperStar Ab.{u + 1} i).map (regularRestriction Λ i).hom) := by
  let adj := ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i
  have := ProEtale.isIso_upperStarLowerStarAdjunction_counit Ab.{u + 1} i
  have : IsIso ((ProEtale.upperStar Ab.{u + 1} i).map
      (adj.unit.app (condensedRingObj Λ.X X))) := by
    have h := adj.left_triangle_components (condensedRingObj Λ.X X)
    have : IsIso ((ProEtale.upperStar Ab.{u + 1} i).map
        (adj.unit.app (condensedRingObj Λ.X X)) ≫ adj.counit.app _) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  change IsIso ((ProEtale.upperStar Ab.{u + 1} i).map
    (condensedPushforwardHom Λ.X i))
  unfold condensedPushforwardHom
  rw [Functor.map_comp]
  infer_instance

private theorem regularRestriction_epi
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [QuasiCompact i.openComplement.ι] : Epi (regularRestriction Λ i) := by
  let q := (regularRestriction Λ i).hom
  let j := i.openComplement.ι
  have hij : IsCompl (Set.range i.base) (Set.range j.base) := by
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl
  have hi := regularRestriction_closed_isIso Λ i
  have hz := ProEtale.isZero_upperStar_lowerStar_of_disjoint Ab.{u + 1} i j
    hij.disjoint (condensedRingObj Λ.X Z)
  have hci : IsZero ((ProEtale.upperStar Ab.{u + 1} i).obj (cokernel q)) :=
    (isZero_cokernel_of_epi ((ProEtale.upperStar Ab.{u + 1} i).map q)).of_iso
      (PreservesCokernel.iso _ q)
  have hcj : IsZero ((ProEtale.upperStar Ab.{u + 1} j).obj (cokernel q)) :=
    (IsZero.of_epi (cokernel.π ((ProEtale.upperStar Ab.{u + 1} j).map q)) hz).of_iso
      (PreservesCokernel.iso _ q)
  have hq : Epi q := Preadditive.epi_of_isZero_cokernel q
    (ProEtale.isZero_of_isZero_upperStar_of_isCompl_addCommGrp i j hij _ hci hcj)
  exact (Mod.forget _).epi_of_epi_map hq

private theorem moduleSectionEquiv_open_zero
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Modules Λ X) (f : unit Λ X ⟶ M)
    (hf : M.X.obj.map (supportRestrictionArrow i).op (moduleSectionEquiv Λ X M f) = 0) :
    (ProEtale.upperStar Ab.{u + 1} i.openComplement.ι).map f.hom = 0 := by
  let : MonObj (condensedRingObj Λ.X X) :=
    inferInstanceAs (MonObj ((upperStarFromPoint X).obj Λ.X))
  let j := i.openComplement.ι
  let G := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  let F := G.sheafPushforwardContinuous Ab.{u + 1}
    (Scheme.ProEt.topology i.openComplement.toScheme) (Scheme.ProEt.topology X)
  let hT := MorphismProperty.Over.mkIdTerminal (@WeaklyEtale) i.openComplement.toScheme
  let hX := MorphismProperty.Over.mkIdTerminal (@WeaklyEtale) X
  have hzero : F.map f.hom = 0 := by
    have h : ((F.mapMod (condensedRingObj Λ.X X)).map f) = 0 := by
      apply Mod.regular_hom_ext
      change Functor.LaxMonoidal.ε F ≫
        F.map (η[condensedRingObj Λ.X X]) ≫ F.map f.hom = _
      rw [← F.map_comp, Mod.zero_hom, comp_zero]
      apply Sheaf.unitHomEval_injective hT _
      rw [Sheaf.unitHomEval_ε_comp_sheafPushforwardContinuous_map G hX]
      let v : G.obj (Scheme.ProEt.mk (𝟙 i.openComplement.toScheme)) ⟶
          Scheme.ProEt.mk j := MorphismProperty.Over.homMk (𝟙 _) (by rfl)
      have hv : hX.from (G.obj (Scheme.ProEt.mk (𝟙 i.openComplement.toScheme))) =
          v ≫ supportRestrictionArrow i := hX.hom_ext _ _
      change M.X.obj.map
        (hX.from (G.obj (Scheme.ProEt.mk (𝟙 i.openComplement.toScheme)))).op
          (moduleSectionEquiv Λ X M f) = 0
      rw [hv, op_comp, M.X.obj.map_comp]
      change M.X.obj.map v.op
        (M.X.obj.map (supportRestrictionArrow i).op (moduleSectionEquiv Λ X M f)) = 0
      rw [hf, map_zero]
    exact congrArg Mod.Hom.hom h
  apply (cancel_mono ((ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).hom.app
    M.X)).1
  rw [zero_comp]
  rw [NatTrans.naturality]
  change _ ≫ F.map f.hom = 0
  rw [hzero, comp_zero]

private theorem generator_unit (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) :
    Functor.LaxMonoidal.ε (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
      generator Λ X = η[condensedRingObj Λ.X X] := by
  change (Functor.Monoidal.εIso (constantSheaf (Scheme.ProEt.topology X)
    Ab.{u + 1})).hom ≫ ((Functor.Monoidal.εIso
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1})).inv ≫ η) = _
  exact Iso.hom_inv_id_assoc _ _

private theorem integerSheaf_unit (X : Scheme.{u}) :
    Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
      (Functor.LaxMonoidal.ε (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1})).hom =
      toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
  let J := Scheme.ProEt.topology X
  have e : Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1}) ≫
      (sheafToPresheaf J Ab.{u + 1}).map
        (Functor.LaxMonoidal.ε (presheafToSheaf J Ab.{u + 1})) =
      (sheafificationAdjunction J Ab.{u + 1}).unit.app _ := by
    rw [← (sheafificationAdjunction J Ab.{u + 1}).unit_app_unit_comp_map_η,
      Category.assoc, Functor.Monoidal.map_η_ε]
    exact Category.comp_id _
  change Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1}) ≫
    (sheafToPresheaf J Ab.{u + 1}).map
      (Functor.LaxMonoidal.ε (constantSheaf J Ab.{u + 1})) = _
  rw [Sheaf.ε_constantSheaf]
  exact e

private theorem integerSheaf_directImage_unit {Z X : Scheme.{u}} (i : Z ⟶ X) :
    Functor.LaxMonoidal.ε (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
      Scheme.proEtaleConstantDirectImageMap i Ab.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
      Functor.LaxMonoidal.ε (ProEtale.lowerStar Ab.{u + 1} i) ≫
        (ProEtale.lowerStar Ab.{u + 1} i).map
          (Functor.LaxMonoidal.ε (constantSheaf (Scheme.ProEt.topology Z) Ab.{u + 1})) := by
  let J := Scheme.ProEt.topology X
  let K := Scheme.ProEt.topology Z
  let G := Scheme.proEtaleBaseChange i
  let r := Scheme.proEtaleConstantDirectImageMap i Ab.{u + 1}
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have hr : toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ r.hom =
      Functor.whiskerLeft G.op (toSheafify K ((Functor.const Z.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) :=
    Equiv.apply_symm_apply ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _) _
  have hleft : Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1}) ≫
      (Functor.LaxMonoidal.ε (constantSheaf J Ab.{u + 1}) ≫ r).hom =
      Functor.whiskerLeft G.op (toSheafify K ((Functor.const Z.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) := by
    rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc, integerSheaf_unit, hr]
  have hright : Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1}) ≫
      (Functor.LaxMonoidal.ε (ProEtale.lowerStar Ab.{u + 1} i) ≫
        (ProEtale.lowerStar Ab.{u + 1} i).map
          (Functor.LaxMonoidal.ε (constantSheaf K Ab.{u + 1}))).hom =
      Functor.whiskerLeft G.op (toSheafify K ((Functor.const Z.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) := by
    apply NatTrans.ext
    funext V
    change (Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1})).app V ≫
      (Functor.LaxMonoidal.ε (ProEtale.lowerStar Ab.{u + 1} i)).hom.app V ≫
        (Functor.LaxMonoidal.ε (constantSheaf K Ab.{u + 1})).hom.app (G.op.obj V) = _
    erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc]
    exact congr_app (integerSheaf_unit Z) (G.op.obj V)
  apply Sheaf.unitHomEval_injective (MorphismProperty.Over.mkIdTerminal _ X) _
  exact congrArg (fun k ↦ k.app (op (Scheme.ProEt.mk (𝟙 X))) (ULift.up (1 : ℤ)))
    (hleft.trans hright.symm)

private theorem regularRestriction_generator
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    generator Λ X ≫ (regularRestriction Λ i).hom =
      Scheme.proEtaleConstantDirectImageMap i Ab.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ supportedGenerator Λ i := by
  let F := ProEtale.lowerStar Ab.{u + 1} i
  let εX := Functor.LaxMonoidal.ε (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  let εZ := Functor.LaxMonoidal.ε (constantSheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
  apply (cancel_epi εX).1
  calc
    εX ≫ (generator Λ X ≫ (regularRestriction Λ i).hom) =
        η[condensedRingObj Λ.X X] ≫ (regularRestriction Λ i).hom := by
      rw [← Category.assoc, generator_unit]
    _ = Functor.LaxMonoidal.ε F ≫ F.map (η[condensedRingObj Λ.X Z]) :=
      IsMonHom.one_hom (condensedPushforwardHom Λ.X i)
    _ = Functor.LaxMonoidal.ε F ≫ F.map (εZ ≫ generator Λ Z) := by
      rw [generator_unit]
    _ = (Functor.LaxMonoidal.ε F ≫ F.map εZ) ≫ F.map (generator Λ Z) := by
      rw [Functor.map_comp, Category.assoc]
    _ = (εX ≫ Scheme.proEtaleConstantDirectImageMap i Ab.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ supportedGenerator Λ i := by
      rw [integerSheaf_directImage_unit]
      rfl
    _ = _ := Category.assoc _ _ _

private theorem regularRestriction_kernel_annihilates
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [QuasiCompact i.openComplement.ι] (M : Modules Λ X) (f : unit Λ X ⟶ M)
    (hf : M.X.obj.map (supportRestrictionArrow i).op (moduleSectionEquiv Λ X M f) = 0) :
    kernel.ι (regularRestriction Λ i) ≫ f = 0 := by
  let q := regularRestriction Λ i
  let j := i.openComplement.ι
  let Y : Bool → Scheme.{u} := fun b ↦ bif b then Z else i.openComplement.toScheme
  let g : ∀ b, Y b ⟶ X := fun b ↦ match b with | true => i | false => j
  have : ∀ b, QuasiCompact (g b) := by
    rintro (_ | _) <;> dsimp [g] <;> infer_instance
  have hg : ∀ x : X, ∃ b, x ∈ Set.range (g b) := by
    intro x
    by_cases hx : x ∈ Set.range i.base
    · exact ⟨true, hx⟩
    · exact ⟨false, ⟨⟨x, hx⟩, rfl⟩⟩
  apply (Mod.forget _).map_injective
  apply ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp g hg
    ((Mod.forget _).map (kernel.ι q ≫ f))
  rintro (_ | _)
  · change (ProEtale.upperStar Ab.{u + 1} j).map
      ((kernel.ι q).hom ≫ f.hom) = 0
    rw [Functor.map_comp, moduleSectionEquiv_open_zero Λ i M f hf, comp_zero]
  · change (ProEtale.upperStar Ab.{u + 1} i).map
      ((kernel.ι q).hom ≫ f.hom) = 0
    have hi := regularRestriction_closed_isIso Λ i
    have hk : (ProEtale.upperStar Ab.{u + 1} i).map (kernel.ι q).hom = 0 := by
      apply (cancel_mono ((ProEtale.upperStar Ab.{u + 1} i).map q.hom)).1
      rw [zero_comp, ← Functor.map_comp]
      change (ProEtale.upperStar Ab.{u + 1} i).map
        ((Mod.forget _).map (kernel.ι q ≫ q)) = 0
      rw [kernel.condition, Functor.map_zero, Functor.map_zero]
    rw [Functor.map_comp, hk, zero_comp]

private def rawEvaluation (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) (M : Modules Λ X) :
    (source Λ i ⟶ M) →+ M.X.obj.obj (op (Scheme.ProEt.mk (𝟙 X))) where
  toFun f := ((constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
    (MorphismProperty.Over.mkIdTerminal _ X)).homAddEquiv _ M.X
      (Scheme.proEtaleConstantDirectImageMap i Ab.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ supportedGenerator Λ i ≫ f.hom))
          (ULift.up 1)
  map_zero' := by
    simp only [Mod.zero_hom, comp_zero, map_zero]
    rfl
  map_add' f g := by
    simp only [Mod.add_hom, Preadditive.comp_add, map_add]
    rfl

private theorem sourceOpenSections_zero (Λ : Profinite.CondensedRing.{u})
    [IsCommMonObj Λ.X] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    IsZero ((source Λ i).X.obj.obj (op (Scheme.ProEt.mk i.openComplement.ι))) := by
  let V := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj
    (Scheme.ProEt.mk i.openComplement.ι)
  have : IsEmpty V.left := by
    change IsEmpty (pullback (C := Scheme.{u}) i.openComplement.ι i)
    apply Scheme.isEmpty_pullback
    rw [Scheme.Opens.range_ι]
    change Disjoint ((Set.range i.base)ᶜ) (Set.range i.base)
    exact disjoint_compl_left
  exact (Scheme.ProEt.isTerminalSectionsOfIsEmpty (unit Λ Z).X V).isZero

private theorem rawEvaluation_supported (Λ : Profinite.CondensedRing.{u})
    [IsCommMonObj Λ.X] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Modules Λ X) (f : source Λ i ⟶ M) :
    M.X.obj.map (supportRestrictionArrow i).op (rawEvaluation Λ i M f) = 0 := by
  let p := Scheme.proEtaleConstantDirectImageMap i Ab.{u + 1}
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ supportedGenerator Λ i
  let adj := constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
    (MorphismProperty.Over.mkIdTerminal _ X)
  have hn := adj.homEquiv_naturality_right p f.hom
  change adj.homEquiv _ _ (p ≫ f.hom) = adj.homEquiv _ _ p ≫
    f.hom.hom.app (op (Scheme.ProEt.mk (𝟙 X))) at hn
  change M.X.obj.map (supportRestrictionArrow i).op
    (adj.homEquiv _ _ (p ≫ f.hom) (ULift.up 1)) = 0
  rw [hn]
  change M.X.obj.map (supportRestrictionArrow i).op
    (f.hom.hom.app _ (adj.homEquiv _ _ p (ULift.up 1))) = 0
  have hn' := ConcreteCategory.congr_hom (f.hom.hom.naturality
    (supportRestrictionArrow i).op) (adj.homEquiv _ _ p (ULift.up 1))
  change f.hom.hom.app _ ((source Λ i).X.obj.map (supportRestrictionArrow i).op
    (adj.homEquiv _ _ p (ULift.up 1))) =
      M.X.obj.map (supportRestrictionArrow i).op
        (f.hom.hom.app _ (adj.homEquiv _ _ p (ULift.up 1))) at hn'
  rw [← hn']
  have hz := (sourceOpenSections_zero Λ i).eq_of_tgt
    ((source Λ i).X.obj.map (supportRestrictionArrow i).op) 0
  rw [hz, AddCommGrpCat.zero_apply, map_zero]

private theorem rawEvaluation_natural (Λ : Profinite.CondensedRing.{u})
    [IsCommMonObj Λ.X] {Z X : Scheme.{u}} (i : Z ⟶ X)
    {M N : Modules Λ X} (g : M ⟶ N) (f : source Λ i ⟶ M) :
    rawEvaluation Λ i N (f ≫ g) =
      g.hom.hom.app (op (Scheme.ProEt.mk (𝟙 X))) (rawEvaluation Λ i M f) := by
  let adj := constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
    (MorphismProperty.Over.mkIdTerminal _ X)
  let p := Scheme.proEtaleConstantDirectImageMap i Ab.{u + 1}
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ supportedGenerator Λ i ≫ f.hom
  have h := congrArg (fun k ↦ k (ULift.up 1)) (adj.homEquiv_naturality_right p g.hom)
  change adj.homEquiv _ _ (p ≫ g.hom) (ULift.up 1) =
    g.hom.hom.app (op (Scheme.ProEt.mk (𝟙 X)))
      (adj.homEquiv _ _ p (ULift.up (1 : ℤ))) at h
  change adj.homEquiv (AddCommGrpCat.of (ULift.{u + 1} ℤ)) N.X
    (Scheme.proEtaleConstantDirectImageMap i Ab.{u + 1}
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ supportedGenerator Λ i ≫
        (f.hom ≫ g.hom)) (ULift.up (1 : ℤ)) =
      g.hom.hom.app (op (Scheme.ProEt.mk (𝟙 X)))
        (adj.homEquiv _ _ p (ULift.up (1 : ℤ)))
  simpa only [p, Category.assoc] using h

private def evaluationMap (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    preadditiveCoyoneda.obj (op (source Λ i)) ⟶ sections Λ i where
  app M := kernel.lift _ (AddCommGrpCat.ofHom (rawEvaluation Λ i M)) (by
    ext f
    exact rawEvaluation_supported Λ i M f)
  naturality M N g := by
    apply equalizer.hom_ext
    simp only [Category.assoc, kernel.lift_ι]
    change (preadditiveCoyoneda.obj (op (source Λ i))).map g ≫
        AddCommGrpCat.ofHom (rawEvaluation Λ i N) =
      kernel.lift _ (AddCommGrpCat.ofHom (rawEvaluation Λ i M)) _ ≫
        kernel.map _ _ (g.hom.hom.app _) (g.hom.hom.app _)
          (g.hom.hom.naturality (supportRestrictionArrow i).op) ≫ kernel.ι _
    rw [kernel.lift_ι, ← Category.assoc, kernel.lift_ι]
    ext f
    exact rawEvaluation_natural Λ i g f

private theorem evaluationMap_apply (Λ : Profinite.CondensedRing.{u})
    [IsCommMonObj Λ.X] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Modules Λ X) (f : source Λ i ⟶ M) :
    kernel.ι (M.X.obj.map (supportRestrictionArrow i).op)
      ((evaluationMap Λ i).app M f) = rawEvaluation Λ i M f := by
  have h : (evaluationMap Λ i).app M ≫
      kernel.ι (M.X.obj.map (supportRestrictionArrow i).op) =
        AddCommGrpCat.ofHom (rawEvaluation Λ i M) := kernel.lift_ι _ _ _
  exact ConcreteCategory.congr_hom h f

private theorem evaluation_unique (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (e e' : Evaluation Λ i) (he : EvaluationSpec Λ i e) (he' : EvaluationSpec Λ i e') :
    e = e' := by
  apply Iso.ext
  ext M f
  apply (AddCommGrpCat.mono_iff_injective
    (kernel.ι (M.X.obj.map (supportRestrictionArrow i).op))).1 inferInstance
  exact (he M f).trans (he' M f).symm

private theorem regularEvaluation (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) (M : Modules Λ X) (f : unit Λ X ⟶ M) :
    ((constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
      (MorphismProperty.Over.mkIdTerminal _ X)).homEquiv _ _
        (generator Λ X ≫ f.hom)) (ULift.up 1) = moduleSectionEquiv Λ X M f := by
  have h : (constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
      (MorphismProperty.Over.mkIdTerminal _ X)).homEquiv _ _ (generator Λ X ≫ f.hom) =
      (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op (Scheme.ProEt.mk (𝟙 X))) ≫
          (generator Λ X ≫ f.hom).hom.app (op (Scheme.ProEt.mk (𝟙 X))) := by
    rw [Adjunction.homEquiv_unit]
    simp [constantSheafAdj, constantPresheafAdj]
    rfl
  rw [h, ← integerSheaf_unit]
  change ((Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology X)
    Ab.{u + 1}) ≫ (Functor.LaxMonoidal.ε (constantSheaf (Scheme.ProEt.topology X)
      Ab.{u + 1})).hom ≫ (generator Λ X ≫ f.hom).hom).app
        (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1) = _
  rw [← ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc, generator_unit]
  rfl

private theorem rawEvaluation_eq (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) (M : Modules Λ X) (f : source Λ i ⟶ M) :
    rawEvaluation Λ i M f = moduleSectionEquiv Λ X M (regularRestriction Λ i ≫ f) := by
  have h := regularEvaluation Λ X M (regularRestriction Λ i ≫ f)
  change ((constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
    (MorphismProperty.Over.mkIdTerminal _ X)).homEquiv _ _
      (generator Λ X ≫ (regularRestriction Λ i).hom ≫ f.hom)) (ULift.up 1) = _ at h
  rw [← Category.assoc, regularRestriction_generator, Category.assoc] at h
  exact h

private theorem evaluationMap_bijective (Λ : Profinite.CondensedRing.{u})
    [IsCommMonObj Λ.X] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [QuasiCompact i.openComplement.ι] (M : Modules Λ X) :
    Function.Bijective ((evaluationMap Λ i).app M) := by
  let q := regularRestriction Λ i
  have : Epi q := regularRestriction_epi Λ i
  constructor
  · intro f g h
    apply (cancel_epi q).1
    apply (moduleSectionEquiv Λ X M).injective
    rw [← rawEvaluation_eq, ← rawEvaluation_eq, ← evaluationMap_apply,
      ← evaluationMap_apply, h]
  · intro s
    let f := (moduleSectionEquiv Λ X M).symm
      (kernel.ι (M.X.obj.map (supportRestrictionArrow i).op) s)
    have hf : M.X.obj.map (supportRestrictionArrow i).op (moduleSectionEquiv Λ X M f) = 0 := by
      rw [AddEquiv.apply_symm_apply]
      exact ConcreteCategory.congr_hom (kernel.condition _) s
    let g := Abelian.epiDesc q f (regularRestriction_kernel_annihilates Λ i M f hf)
    refine ⟨g, ?_⟩
    apply (AddCommGrpCat.mono_iff_injective
      (kernel.ι (M.X.obj.map (supportRestrictionArrow i).op))).1 inferInstance
    rw [evaluationMap_apply, rawEvaluation_eq]
    change moduleSectionEquiv Λ X M (q ≫ g) = _
    rw [Abelian.comp_epiDesc]
    exact (moduleSectionEquiv Λ X M).apply_symm_apply _

private theorem completed_evaluation_existsUnique (Λ : Profinite.CondensedRing.{u})
    [IsCommMonObj Λ.X] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [QuasiCompact i.openComplement.ι] : ∃! e : Evaluation Λ i, EvaluationSpec Λ i e := by
  have (M : Modules Λ X) : IsIso ((evaluationMap Λ i).app M) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (evaluationMap_bijective Λ i M)
  have : IsIso (evaluationMap Λ i) := NatIso.isIso_of_isIso_app _
  let e : Evaluation Λ i := asIso (evaluationMap Λ i)
  have he : EvaluationSpec Λ i e := by
    intro M f
    exact evaluationMap_apply Λ i M f
  exact ⟨e, he, fun e' he' ↦ evaluation_unique Λ i e' e he' he⟩

/-- Evaluation on one uniquely determines the supported-sections comparison.
Source: lem-pur-supported-hom, steps 1--4 (blueprint: lem-pur-supported-hom).
The complementary open is quasi-compact, as required by Wei Yang #1412 item 7.
Proof: restrict the regular unit to the closed direct image. This map is epic:
its closed pullback is an isomorphism, its open target is zero, and the two
pullbacks detect zero cokernels. A section supported on the closed subset gives
a regular-module map whose open pullback vanishes. Its composite with the
kernel of restriction vanishes after both pullbacks, hence vanishes. Descend
uniquely along the epic restriction. The integral-unit calculation identifies
the descended map with the specified evaluation on one. Naturality of that
evaluation gives the natural isomorphism, and the kernel inclusion gives uniqueness. -/
theorem evaluation_existsUnique (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [QuasiCompact i.openComplement.ι] :
    ∃! e : Evaluation Λ i, EvaluationSpec Λ i e := by
  exact completed_evaluation_existsUnique Λ i

/-- The uniquely evaluation-normalized underived comparison.
Source: lem-pur-supported-hom, step 4 (blueprint: lem-pur-supported-hom). -/
def evaluation (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [QuasiCompact i.openComplement.ι] : Evaluation Λ i :=
  (evaluation_existsUnique Λ i).choose

/-- Actual derived kernel cohomology for bounded-below module complexes.
Source: def-pur-support-cohomology (blueprint: lem-pur-supported-hom). -/
abbrev H (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ) :=
  (sections Λ i).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor Ab.{u + 1} a

/-- The supported-Hom comparison in every integer degree.
Source: lem-pur-supported-hom (blueprint: lem-pur-supported-hom). -/
abbrev Identification (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  ∀ (K : DerivedCategory.Plus (Modules Λ X)) (a : ℤ),
    (H Λ i a).obj K ≃+
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (source Λ i) ⟶ K.obj⟦a⟧)

/-- Naturality and the injective-cocycle formula specify the actual comparison.
Source: supported-Hom proof, steps 5--6 (blueprint: lem-pur-supported-hom). -/
def IdentificationSpec (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [QuasiCompact i.openComplement.ι]
    (χ : Identification Λ i) : Prop :=
  (∀ (K L : DerivedCategory.Plus (Modules Λ X)) (v : K ⟶ L) (a : ℤ)
    (s : (H Λ i a).obj K),
    χ L a ((H Λ i a).map v s) = χ K a s ≫ (DerivedCategory.Plus.ι.map v)⟦a⟧') ∧
  (∀ (I : CochainComplex.Plus (Modules Λ X)) [∀ r : ℤ, Injective (I.obj.X r)]
    (a : ℤ) (f : source Λ i ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0)
    (s : (((sections Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).cycles a),
    (evaluation Λ i).hom.app (I.obj.X a) f =
      (((sections Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).iCycles a s →
    χ (DerivedCategory.Plus.Q.obj I) a
      (((sections Λ i).homologyRightDerivedFunctorPlusObjQIsoOfInjective I a).inv
        ((((sections Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).homologyπ a s)) =
      supportedHomLocalizedCocycle I.obj a f hf ≫
        ((DerivedCategory.quotientCompQhIso _).inv.app I.obj)⟦a⟧')

private lemma admissible_quotient_inv (K : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso A).inv.app K = 𝟙 _ :=
  CategoryTheory.Quotient.lift.isLift_inv _ _ _ K

private noncomputable def admissible_cycle
    (K : CochainComplex.Plus AddCommGrpCat.{v}) (a : ℤ)
    (x : AddMonoidHom.ker (K.obj.sc a).g.hom) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
      (DerivedCategory.Plus.Q.obj K) :=
  (DerivedCategory.Plus.homologyFunctorObjQIso K a).inv
    (K.obj.homologyπ a ((K.obj.sc a).abCyclesIso.inv x))

private lemma admissible_cycle_map
    {K J : CochainComplex.Plus AddCommGrpCat.{v}} (φ : K ⟶ J) (a : ℤ)
    (x : AddMonoidHom.ker (K.obj.sc a).g.hom)
    (y : AddMonoidHom.ker (J.obj.sc a).g.hom) (hxy : φ.hom.f a x.val = y.val) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
        (DerivedCategory.Plus.Q.map φ) (admissible_cycle K a x) = admissible_cycle J a y := by
  have hn : (DerivedCategory.Plus.homologyFunctorObjQIso K a).inv ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
        (DerivedCategory.Plus.Q.map φ) =
      HomologicalComplex.homologyMap φ.hom a ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso J a).inv := by
    apply (cancel_mono (DerivedCategory.Plus.homologyFunctorObjQIso J a).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality]
    simp
  unfold admissible_cycle
  rw [← AddCommGrpCat.comp_apply, hn, AddCommGrpCat.comp_apply]
  congr 1
  erw [← AddCommGrpCat.comp_apply, HomologicalComplex.homologyπ_naturality,
    AddCommGrpCat.comp_apply]
  congr 1
  apply (AddCommGrpCat.mono_iff_injective (J.obj.iCycles a)).1 inferInstance
  rw [← AddCommGrpCat.comp_apply, HomologicalComplex.cyclesMap_i,
    AddCommGrpCat.comp_apply]
  dsimp only [HomologicalComplex.iCycles]
  erw [ShortComplex.abCyclesIso_inv_apply_iCycles,
    ShortComplex.abCyclesIso_inv_apply_iCycles]
  exact hxy

private lemma admissible_homEquiv_naturality
    (P : A) (S : A ⥤ AddCommGrpCat.{v}) [S.Additive]
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    {X Y : DerivedCategory.Plus A} (g : X ⟶ Y) (a : ℤ)
    (α : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
      (S.rightDerivedFunctorPlus.obj X)) :
    representedTransportHomEquiv P S θ Y a
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
          (S.rightDerivedFunctorPlus.map g) α) =
      representedTransportHomEquiv P S θ X a α ≫
        ((DerivedCategory.Plus.ι (C := A)).map g)⟦a⟧' := by
  change representableTransportRoof P Y a
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
      ((rightDerivedFunctorPlusNatIso θ.symm).hom.app Y)
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
        (S.rightDerivedFunctorPlus.map g) α)) = _
  rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp,
    (rightDerivedFunctorPlusNatIso θ.symm).hom.naturality,
    Functor.map_comp, AddCommGrpCat.comp_apply]
  exact (Classical.choose_spec (exists_rhom_hom_derived_roof P)).1 X Y g a _

private lemma admissible_roof_injective
    (P : A) (I : CochainComplex.Plus A) (hi : ∀ k : ℤ, Injective (I.obj.X k))
    (a : ℤ) (f : P ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0) :
    representableTransportRoof P (DerivedCategory.Plus.Q.obj I) a
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
          ((preadditiveCoyoneda.obj (op P)).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient A).obj I))
          (admissible_cycle ((preadditiveCoyoneda.obj (op P)).mapCochainComplexPlus.obj I)
            a ⟨f, by
              change f ≫ I.obj.d a ((ComplexShape.up ℤ).next a) = 0
              rw [CochainComplex.next]
              exact hf⟩)) =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q ≫
      ((DerivedCategory.quotientCompQhIso A).hom.app I.obj)⟦a⟧' := by
  let := hi
  obtain ⟨n, hn⟩ := I.2
  let := hn
  let r : CochainComplex.KInjectiveResolutionChoice I.obj :=
    { complex := I.obj
      map := 𝟙 I.obj
      quasiIso := inferInstance
      isKInjective := CochainComplex.isKInjective_of_injective I.obj n }
  have h := (Classical.choose_spec (exists_rhom_hom_derived_roof P)).2
    I r I.2 hi a f hf
  have he : (DerivedCategory.Plus.ι (C := A)).preimageIso
      (X := DerivedCategory.Plus.Q.obj I) (Y := DerivedCategory.Plus.Q.obj I)
      ((DerivedCategory.quotientCompQhIso A).symm.app I.obj ≪≫
        asIso (DerivedCategory.Q.map (𝟙 I.obj)) ≪≫
        (DerivedCategory.quotientCompQhIso A).app I.obj) =
      Iso.refl (DerivedCategory.Plus.Q.obj I) := by
    apply Iso.ext
    apply (DerivedCategory.Plus.ι (C := A)).map_injective
    change (DerivedCategory.Plus.ι (C := A)).map
      ((DerivedCategory.Plus.ι (C := A)).preimage _) = 𝟙 _
    rw [Functor.map_preimage]
    simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, asIso_hom]
    erw [admissible_quotient_inv]
    erw [Category.id_comp, DerivedCategory.Q.map_id, Category.id_comp]
    rfl
  dsimp only [r] at h
  rw [he] at h
  simp only [Iso.refl_inv] at h
  erw [(preadditiveCoyoneda.obj (op P)).rightDerivedFunctorPlus.map_id,
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map_id,
    AddCommGrpCat.id_apply] at h
  have hid : inv (DerivedCategory.Q.map (𝟙 I.obj)) = 𝟙 _ := by
    apply (cancel_mono (DerivedCategory.Q.map (𝟙 I.obj))).mp
    erw [IsIso.inv_hom_id, Category.id_comp, DerivedCategory.Q.map_id]
  erw [hid, (shiftFunctor (DerivedCategory A) a).map_id, Category.id_comp] at h
  have hq : (DerivedCategory.quotientCompQhIso A).hom.app I.obj = 𝟙 _ :=
    CategoryTheory.Quotient.lift.isLift_hom _ _ _ I.obj
  rw [hq]
  erw [(shiftFunctor (DerivedCategory A) a).map_id]
  simpa only [representableTransportRoof, admissible_cycle,
    rightDerivedComplexWithResolution, mapCochainComplexPlus, Category.comp_id] using! h

private lemma admissible_unit_cycle_map
    (S T : A ⥤ AddCommGrpCat.{v}) [S.Additive] [T.Additive] (σ : S ⟶ T)
    (I : CochainComplex.Plus A) (a : ℤ)
    (x : AddMonoidHom.ker ((S.mapCochainComplexPlus.obj I).obj.sc a).g.hom)
    (y : AddMonoidHom.ker ((T.mapCochainComplexPlus.obj I).obj.sc a).g.hom)
    (hxy : σ.app (I.obj.X a) x.val = y.val) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
        ((rightDerivedFunctorPlusNatTrans σ).app (DerivedCategory.Plus.Q.obj I))
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
          (S.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj I))
          (admissible_cycle (S.mapCochainComplexPlus.obj I) a x)) =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
        (T.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj I))
        (admissible_cycle (T.mapCochainComplexPlus.obj I) a y) := by
  erw [← AddCommGrpCat.comp_apply, ← Functor.map_comp, rightDerivedFunctorPlusNatTrans_app,
    Functor.map_comp, AddCommGrpCat.comp_apply]
  congr 1
  let φ : S.mapCochainComplexPlus.obj I ⟶ T.mapCochainComplexPlus.obj I :=
    ObjectProperty.homMk ((NatTrans.mapHomologicalComplex σ (.up ℤ)).app I.obj)
  exact admissible_cycle_map φ a x y (by exact hxy)

private lemma admissible_represented_closed
    (P : A) (S : A ⥤ AddCommGrpCat.{v}) [S.Additive]
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (I : CochainComplex.Plus A) (a : ℤ) (f : P ⟶ I.obj.X a)
    (hf : f ≫ I.obj.d a (a + 1) = 0) :
    (θ.hom.app (I.obj.X a) f) ∈
      AddMonoidHom.ker ((S.mapCochainComplexPlus.obj I).obj.sc a).g.hom := by
  have h := ConcreteCategory.congr_hom (θ.hom.naturality (I.obj.d a (a + 1))) f
  change S.map (I.obj.d a ((ComplexShape.up ℤ).next a))
    (θ.hom.app (I.obj.X a) f) = 0
  rw [CochainComplex.next]
  change θ.hom.app (I.obj.X (a + 1)) (f ≫ I.obj.d a (a + 1)) =
    S.map (I.obj.d a (a + 1)) (θ.hom.app (I.obj.X a) f) at h
  rw [hf, map_zero] at h
  exact h.symm

private noncomputable def admissible_representedClass
    (P : A) (S : A ⥤ AddCommGrpCat.{v}) [S.Additive]
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (I : CochainComplex.Plus A) (a : ℤ) (f : P ⟶ I.obj.X a)
    (hf : f ≫ I.obj.d a (a + 1) = 0) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
      (S.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj I)) :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
    (S.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj I))
    (admissible_cycle (S.mapCochainComplexPlus.obj I) a
      ⟨θ.hom.app (I.obj.X a) f, admissible_represented_closed P S θ I a f hf⟩)

private lemma admissible_represented_norm
    (P : A) (S : A ⥤ AddCommGrpCat.{v}) [S.Additive]
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (I : CochainComplex.Plus A) (hi : ∀ k : ℤ, Injective (I.obj.X k))
    (a : ℤ) (f : P ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0) :
    representedTransportHomEquiv P S θ (DerivedCategory.Plus.Q.obj I) a
        (admissible_representedClass P S θ I a f hf) =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q ≫
      ((DerivedCategory.quotientCompQhIso A).hom.app I.obj)⟦a⟧' := by
  change representableTransportRoof P _ a
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
      ((rightDerivedFunctorPlusNatTrans θ.inv).app _)
      (admissible_representedClass P S θ I a f hf)) = _
  unfold admissible_representedClass
  rw [admissible_unit_cycle_map S (preadditiveCoyoneda.obj (op P)) θ.inv I a _
    ⟨f, by
      change f ≫ I.obj.d a ((ComplexShape.up ℤ).next a) = 0
      rw [CochainComplex.next]
      exact hf⟩ (by simp)]
  exact admissible_roof_injective P I hi a f hf

/-- All-admissible supported-Hom identification, with its evaluation/cocycle normalization.
Source: lem-pur-supported-hom, six proof steps (blueprint: lem-pur-supported-hom).
Proof: (1) use pulled-back coefficients to identify restrictions; (2) the closed
coefficient restriction is locally surjective; (3) its kernel is j_!Λ_U;
(4) evaluation gives the specified underived comparison; (5) apply it termwise
on a bounded-below injective resolution; (6) a supported cycle maps to the
single-source cocycle displayed above. Resolution comparison gives naturality
and independence, and these cocycles determine the comparison uniquely. -/
theorem supported_hom_existsUnique (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [QuasiCompact i.openComplement.ι] :
    ∃! χ : Identification Λ i, IdentificationSpec Λ i χ := by
  classical
  let S := sections Λ i
  let B := source Λ i
  let θ := evaluation Λ i
  let χ : Identification Λ i := fun K a ↦
    Functor.representedTransportHomEquiv B S θ K a
  have hχ : IdentificationSpec Λ i χ := by
    constructor
    · intro K L v a s
      exact admissible_homEquiv_naturality B S θ v a s
    · intro I hi a f hf s hs
      let SI := (S.mapHomologicalComplex (.up ℤ)).obj I.obj
      have hn := admissible_represented_norm B S θ I hi a f hf
      have hcycles :
          (SI.sc a).abCyclesIso.inv
            ⟨θ.hom.app (I.obj.X a) f,
              admissible_represented_closed B S θ I a f hf⟩ = s := by
        apply (AddCommGrpCat.mono_iff_injective (SI.iCycles a)).1 inferInstance
        dsimp only [HomologicalComplex.iCycles]
        erw [ShortComplex.abCyclesIso_inv_apply_iCycles]
        exact hs
      have hmodel :
          (S.homologyRightDerivedFunctorPlusObjQIsoOfInjective I a).inv =
            (DerivedCategory.Plus.homologyFunctorObjQIso
              (S.mapCochainComplexPlus.obj I) a).inv ≫
            (DerivedCategory.Plus.homologyFunctor Ab.{u + 1} a).map
              (S.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient _).obj I)) :=
        rfl
      change χ _ a _ = _ at hn
      dsimp only [admissible_representedClass, admissible_cycle] at hn
      erw [hcycles] at hn
      rw [hmodel, AddCommGrpCat.comp_apply]
      rw [supportedHomLocalizedCocycle_eq]
      rw [show (DerivedCategory.quotientCompQhIso (Modules Λ X)).inv.app I.obj = 𝟙 _ from
        CategoryTheory.Quotient.lift.isLift_inv _ _ _ I.obj]
      rw [show (DerivedCategory.quotientCompQhIso (Modules Λ X)).hom.app I.obj = 𝟙 _ from
        CategoryTheory.Quotient.lift.isLift_hom _ _ _ I.obj] at hn
      exact hn
  refine ⟨χ, hχ, ?_⟩
  intro χ' hχ'
  have hQ (I : CochainComplex.Plus (Modules Λ X))
      (hi : ∀ n : ℤ, Injective (I.obj.X n)) (a : ℤ)
      (x : (H Λ i a).obj (DerivedCategory.Plus.Q.obj I)) :
      χ' (DerivedCategory.Plus.Q.obj I) a x = χ (DerivedCategory.Plus.Q.obj I) a x := by
    let := hi
    let SI := (S.mapHomologicalComplex (.up ℤ)).obj I.obj
    let E := S.homologyRightDerivedFunctorPlusObjQIsoOfInjective I a
    obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective (SI.homologyπ a ≫ E.inv)).1
      inferInstance x
    let f : B ⟶ I.obj.X a := θ.inv.app _ (SI.iCycles a s)
    have heval : θ.hom.app (I.obj.X a) f = SI.iCycles a s :=
      (θ.app _).addCommGroupIsoToAddEquiv.apply_symm_apply _
    have hf : f ≫ I.obj.d a (a + 1) = 0 := by
      apply (θ.app (I.obj.X (a + 1))).addCommGroupIsoToAddEquiv.injective
      have hn := ConcreteCategory.congr_hom (θ.hom.naturality (I.obj.d a (a + 1))) f
      change θ.hom.app _ (f ≫ I.obj.d a (a + 1)) = S.map _ _ at hn
      change θ.hom.app _ (f ≫ I.obj.d a (a + 1)) = θ.hom.app _ 0
      erw [hn, heval, map_zero]
      exact ConcreteCategory.congr_hom (SI.iCycles_d a (a + 1)) s
    have h₁ := hχ'.2 I a f hf s heval
    have h₂ := hχ.2 I a f hf s heval
    change E.inv (SI.homologyπ a s) = x at hs
    rw [← hs]
    exact h₁.trans h₂.symm
  funext K a
  apply AddEquiv.ext
  intro x
  obtain ⟨n, hn⟩ := K.2
  have : K.IsGE n := (K.isGE_ι_obj_iff n).1 hn
  obtain ⟨J, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  let I := (InjectiveObject.ι (Modules Λ X)).mapCochainComplexPlus.obj J
  have hi (n : ℤ) : Injective (I.obj.X n) := (J.obj.X n).2
  let y := (H Λ i a).map e.inv x
  have hy : (H Λ i a).map e.hom y = x := by
    simp [y, ← AddCommGrpCat.comp_apply, ← Functor.map_comp]
  rw [← hy, hχ'.1 _ _ e.hom a y, hχ.1 _ _ e.hom a y, hQ I hi a y]

/-- The canonical all-admissible supported-Hom map, fixed on injective cocycles.
Source: lem-pur-supported-hom, step 6 (blueprint: lem-pur-supported-hom). -/
def supportedHom (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [QuasiCompact i.openComplement.ι] : Identification Λ i :=
  (supported_hom_existsUnique Λ i).choose

/-- Supported cohomology equals supported Hom for the standing finite-type scheme,
all admissible coefficients, all bounded-below complexes, and all integer degrees.
Source: latest blueprint lem-pur-supported-hom, entire statement and proof
(blueprint: lem-pur-supported-hom).
Proof: (1) resolve by bounded-below injectives; the kernel of restriction is
sections of the sheaf supported on the closed subset, giving derived supported
sections; (2) evaluation on the coefficient one identifies sections over the
closed scheme with Hom from its regular unit, and the displayed injective
cocycle formula realizes that identification in every degree; (3) the closed
support adjunction transposes this Hom to Hom from i_* of the unit on X.
All three comparisons are natural, and comparison of resolutions gives the
canonical derived identification specified by IdentificationSpec. -/
theorem supported_hom (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (_hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {Z X : Scheme.{u}} (b : X ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian b
    IdentificationSpec Λ i (supportedHom Λ i) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian b
  exact (supported_hom_existsUnique Λ i).choose_spec.1

end AlgebraicGeometry.ProEtale.CondensedRing.Admissible
