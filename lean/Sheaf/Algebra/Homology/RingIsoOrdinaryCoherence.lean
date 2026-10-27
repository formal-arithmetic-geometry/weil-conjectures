/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Algebra.Homology.RingIsoTransportComparisons
import all Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison
import all Sheaf.Algebra.Homology.RingIsomorphismTensorTransport

/-! # Ordinary tensor coherence for normalized coefficient restriction

Source: Stacks Project, Tags 03D7 and 03EK. Pure tensors determine the comparison.

(blueprint: lem-pur-u2-ordinary-restriction-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.RingIsoTransport
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local semireducible] SheafOfModules.monoidalCategory
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)]

private theorem unit_section {R S : Sheaf J CommRingCat.{r}}
    (a : R ≅ S) (o : RingIsoTensorTransport a.symm)
    (U : Cᵒᵖ) (x : S.obj.obj U) :
    o.monoidal.toMonoidal.toLaxMonoidal.ε.val.app U x = a.inv.hom.app U x := by
  let : (scalarRestriction a.inv).Braided := o.monoidal
  have h := congrArg (fun f ↦ f.val.app U x)
    (Functor.Monoidal.ε_η (scalarRestriction a.inv))
  change o.monoidal.toMonoidal.toOplaxMonoidal.η.val.app U
    (o.monoidal.toMonoidal.toLaxMonoidal.ε.val.app U x) = x at h
  erw [o.unit_hom] at h
  exact (scalar_inv_hom a U _).symm.trans (congrArg (a.inv.hom.app U) h)

private theorem ordinaryId_unit (R : Sheaf J CommRingCat.{r})
    (o : RingIsoTensorTransport (Iso.refl R).symm) :
    let : (scalarRestriction (Iso.refl R).inv).Braided := o.monoidal
    Functor.LaxMonoidal.ε (scalarRestriction (Iso.refl R).inv) ≫
      (ordinaryId R).hom.app (𝟙_ _) = Functor.LaxMonoidal.ε (𝟭 (scalarModules J R)) := by
  let : (scalarRestriction (Iso.refl R).inv).Braided := o.monoidal
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact unit_section (Iso.refl R) o U x

private theorem ordinaryComp_unit {R S T : Sheaf J CommRingCat.{r}}
    (a : R ≅ S) (b : S ≅ T)
    (oa : RingIsoTensorTransport a.symm) (ob : RingIsoTensorTransport b.symm)
    (oc : RingIsoTensorTransport (a ≪≫ b).symm) :
    let : (scalarRestriction a.inv).Braided := oa.monoidal
    let : (scalarRestriction b.inv).Braided := ob.monoidal
    let : (scalarRestriction (a ≪≫ b).inv).Braided := oc.monoidal
    Functor.LaxMonoidal.ε (scalarRestriction a.inv ⋙ scalarRestriction b.inv) ≫
      (ordinaryComp a b).hom.app (𝟙_ _) =
        Functor.LaxMonoidal.ε (scalarRestriction (a ≪≫ b).inv) := by
  let : (scalarRestriction a.inv).Braided := oa.monoidal
  let : (scalarRestriction b.inv).Braided := ob.monoidal
  let : (scalarRestriction (a ≪≫ b).inv).Braided := oc.monoidal
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change oa.monoidal.toMonoidal.toLaxMonoidal.ε.val.app U
    (ob.monoidal.toMonoidal.toLaxMonoidal.ε.val.app U x) =
      oc.monoidal.toMonoidal.toLaxMonoidal.ε.val.app U x
  erw [unit_section a oa, unit_section b ob, unit_section (a ≪≫ b) oc]
  rfl

attribute [local irreducible] SheafOfModules.monoidalCategory

/-- The sectionwise identity comparison is monoidal for every normalized ordinary
restriction structure. Its unit and tensor equations hold on all local sections,
respectively on the pure tensors generating the sheaf tensor product.
Source: literature/stacks-project/sites-modules.tex; Tags 03D7 and 03EK; balanced tensor products
and normalized coefficient transport.
(blueprint: lem-pur-u2-ordinary-restriction-coherence). -/
theorem ordinaryId_monoidal (R : Sheaf J CommRingCat.{r})
    (o : RingIsoTensorTransport (Iso.refl R).symm) :
    let : (scalarRestriction (Iso.refl R).inv).Braided := o.monoidal
    NatTrans.IsMonoidal (ordinaryId R).hom := by
  let : (scalarRestriction (Iso.refl R).inv).Braided := o.monoidal
  refine ⟨?_, fun M N ↦ ?_⟩
  · exact ordinaryId_unit R o
  · apply ScalarHomOrdinary.pure_hom_ext R
    intro U x y
    change ((ordinaryId R).hom.app (M ⊗ N)).val.app U
      ((o.monoidal.toMonoidal.toLaxMonoidal.μ M N).val.app U
        (ScalarHomOrdinary.pure R _ _ U x y)) =
      (((ordinaryId R).hom.app M ⊗ₘ (ordinaryId R).hom.app N).val.app U)
        (ScalarHomOrdinary.pure R _ _ U x y)
    rw [o.pure_inv, ScalarHomOrdinary.pure_map]
    rfl

/-- The sectionwise composition comparison is monoidal for normalized restrictions.
Both unit maps apply the two inverse coefficient maps. Both tensor maps send a pure
tensor to the same pure tensor; generation proves equality of the sheaf morphisms.
Source: literature/stacks-project/sites-modules.tex; Tags 03D7 and 03EK; balanced tensor products
and normalized coefficient transport.
(blueprint: lem-pur-u2-ordinary-restriction-coherence). -/
theorem ordinaryComp_monoidal {R S T : Sheaf J CommRingCat.{r}}
    (a : R ≅ S) (b : S ≅ T)
    (oa : RingIsoTensorTransport a.symm) (ob : RingIsoTensorTransport b.symm)
    (oc : RingIsoTensorTransport (a ≪≫ b).symm) :
    let : (scalarRestriction a.inv).Braided := oa.monoidal
    let : (scalarRestriction b.inv).Braided := ob.monoidal
    let : (scalarRestriction (a ≪≫ b).inv).Braided := oc.monoidal
    NatTrans.IsMonoidal (ordinaryComp a b).hom := by
  let : (scalarRestriction a.inv).Braided := oa.monoidal
  let : (scalarRestriction b.inv).Braided := ob.monoidal
  let : (scalarRestriction (a ≪≫ b).inv).Braided := oc.monoidal
  refine ⟨?_, fun M N ↦ ?_⟩
  · exact ordinaryComp_unit a b oa ob oc
  · apply ScalarHomOrdinary.pure_hom_ext T
    intro U x y
    change ((ordinaryComp a b).hom.app (M ⊗ N)).val.app U
      ((oa.monoidal.toMonoidal.toLaxMonoidal.μ M N).val.app U
        ((ob.monoidal.toMonoidal.toLaxMonoidal.μ _ _).val.app U
          (ScalarHomOrdinary.pure T _ _ U x y))) =
      (oc.monoidal.toMonoidal.toLaxMonoidal.μ M N).val.app U
        ((((ordinaryComp a b).hom.app M ⊗ₘ (ordinaryComp a b).hom.app N).val.app U)
          (ScalarHomOrdinary.pure T _ _ U x y))
    rw [ob.pure_inv, oa.pure_inv, ScalarHomOrdinary.pure_map]
    exact (oc.pure_inv M N U x y).symm

end SheafOfModules.RingIsoTransport
