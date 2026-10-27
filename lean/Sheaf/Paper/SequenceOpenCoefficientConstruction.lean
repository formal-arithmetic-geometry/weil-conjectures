/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SequenceSiteOpenData
import all Sheaf.CategoryTheory.RingedOpenScalarAdjunction

/-! # Coherent coefficient comparisons for open extension

Source: Stacks Project, Tags 03DI, 03DJ and 05RU
(blueprint: lem-pur-sequence-open-coefficients).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe c v r u s
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace WeilConjectures.SemilinearSections

open SheafOfModules.RingedOpenScalar

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (U : C)

private def scalarComposition
    {R S T : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S) (ψ : S ⟶ T) :
    res ψ ⋙ res φ ≅ res (φ ≫ ψ) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun X ↦ Iso.refl _)))

private def overScalarComposition
    {R S T : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S) (ψ : S ⟶ T) :
    res ((J.overPullback CommRingCat.{max c v r} U).map ψ) ⋙
      res ((J.overPullback CommRingCat.{max c v r} U).map φ) ≅
    res ((J.overPullback CommRingCat.{max c v r} U).map (φ ≫ ψ)) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun X ↦ Iso.refl _)))

set_option maxHeartbeats 400000 in
-- The generator formula identifies two independently transported slice modules.
private theorem coefficient_summand
    {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
    (M : Mod.{max c v, v, max c v r} (J.over U) (S.over U))
    (X : (Over U)ᵒᵖ) (x : M.val.obj X) :
    ((sheafComparison.{c, v, r} U φ).inv.app M).val.app (op X.unop.left)
      (openExtensionSection.{c, v, r} J U R
        ((res ((J.overPullback CommRingCat.{max c v r} U).map φ)).obj M) X x) =
      openExtensionSection.{c, v, r} J U S M X x := by
  rw [openExtensionSection, openExtensionSection,
    (adjunctionGenerators.{c, v, r} U R).1,
    (adjunctionGenerators.{c, v, r} U S).1, sheafComparison_inv_app]
  exact sheafComparisonInv_generator.{c, v, r} U φ M (op X.unop.left) X.unop.hom x

set_option maxHeartbeats 1000000 in
-- Coherence checks compare scalar restrictions and sheafification transports.
/-- Normalized coefficient comparisons for ordinary open extension.
Source: Stacks 03DI and 03CY (blueprint: lem-pur-sequence-open-coefficients).
Proof: construct the comparison on the identical direct-sum extension presheaves
and extend it uniquely through module sheafification. It preserves every summand.
Restriction and composite restriction comparisons are the identity on sections.
The unit equation is the summand formula, and the counit equation follows by mates.
Composition and identity follow by testing maps from extension on the adjunction unit;
this test is injective by the Hom equivalence. Thus the comparisons are coherent for
arbitrary coefficient maps, including non-flat maps and zero rings. -/
theorem sequenceOpenCoefficients : Nonempty (SequenceOpenCoefficientData.{c, v, r} J U) := by
  refine ⟨{
    comparison := fun φ ↦ (sheafComparison.{c, v, r} U φ).symm
    summand := coefficient_summand.{c, v, r} J U
    restriction := fun φ ↦ restrictionIso.{c, v, r} U φ
    restriction_section := ?_
    unit := ?_
    counit := ?_
    composition := scalarComposition.{c, v, r} J
    composition_section := ?_
    overComposition := overScalarComposition.{c, v, r} J U
    overComposition_section := ?_
    comp := ?_
    identity := ?_ }⟩
  · intros
    rfl
  · intro R S φ M
    ext X x
    exact coefficient_summand J U φ M X x
  · intro R S φ N
    have hc := (sheafComparison_equations.{c, v, r} U φ).2 N
    apply (cancel_epi ((sheafComparison.{c, v, r} U φ).hom.app
      ((SheafOfModules.localizedSystemRestriction.{c, v, r} S U).obj N))).mp
    change _ = (sheafComparison.{c, v, r} U φ).hom.app _ ≫
      (sheafComparison.{c, v, r} U φ).inv.app _ ≫ _
    rw [Iso.hom_inv_id_app_assoc]
    exact hc
  · intros
    rfl
  · intros
    rfl
  · intro R S T φ ψ M
    apply ((SheafOfModules.localizedSystemAdjunction.{c, v, r} R U).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    ext X x
    have hn := (SheafOfModules.localizedSystemAdjunction.{c, v, r} R U).unit.naturality
      ((overScalarComposition.{c, v, r} J U φ ψ).hom.app M)
    have hn' := congrArg (fun f ↦ f.val.app X x) hn
    change openExtensionSection.{c, v, r} J U R _ X x =
      ((SheafOfModules.localizedSystemExtension.{c, v, r} R U).map
        ((overScalarComposition.{c, v, r} J U φ ψ).hom.app M)).val.app
          (op X.unop.left) (openExtensionSection.{c, v, r} J U R _ X x) at hn'
    change ((sheafComparison.{c, v, r} U (φ ≫ ψ)).inv.app M).val.app _
      (((SheafOfModules.localizedSystemExtension.{c, v, r} R U).map
        ((overScalarComposition.{c, v, r} J U φ ψ).hom.app M)).val.app _
          (openExtensionSection.{c, v, r} J U R _ X x)) =
      ((sheafComparison.{c, v, r} U ψ).inv.app M).val.app _
        (((sheafComparison.{c, v, r} U φ).inv.app _).val.app _
          (openExtensionSection.{c, v, r} J U R _ X x))
    have he := congrArg (fun z ↦
      ((sheafComparison.{c, v, r} U (φ ≫ ψ)).inv.app M).val.app
        (op X.unop.left) z) hn'.symm
    refine he.trans ?_
    exact (coefficient_summand.{c, v, r} J U (φ ≫ ψ) M X x).trans
      ((congrArg (fun z ↦ ((sheafComparison.{c, v, r} U ψ).inv.app M).val.app
          (op X.unop.left) z)
        (coefficient_summand.{c, v, r} J U φ
          ((sliceScalars.{c, v, r} U ψ).obj M) X x)).trans
        (coefficient_summand.{c, v, r} J U ψ M X x)).symm
  · intro R M X
    have hid : (sheafComparison.{c, v, r} U (𝟙 R)).inv.app M =
        (SheafOfModules.fullyFaithfulForget _).preimage
          (PresheafOfModules.homMk
            { app := fun Y ↦ AddCommGrpCat.ofHom (AddMonoidHom.id _)
              naturality := by intros; rfl } (by intros; rfl)) := by
      apply ((SheafOfModules.localizedSystemAdjunction.{c, v, r} R U).homEquiv _ _).injective
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
      ext Y y
      exact coefficient_summand.{c, v, r} J U (𝟙 R) M Y y
    change HEq (fun x ↦
      ((sheafComparison.{c, v, r} U (𝟙 R)).inv.app M).val.app X x) _
    erw [hid]
    rfl

end WeilConjectures.SemilinearSections
