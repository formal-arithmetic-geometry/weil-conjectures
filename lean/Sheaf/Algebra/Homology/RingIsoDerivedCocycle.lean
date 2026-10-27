/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Algebra.Homology.RingIsoTransportComparisons
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle

/-! # The cocycle for derived coefficient restriction

Source: functoriality of localization, Stacks Project Tag 04VG.

(blueprint: lem-pur-u2-derived-restriction-cocycle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v r w
open CategoryTheory CategoryTheory.Limits
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryCompIso
  Functor.mapDerivedCategoryIdIso Functor.mapDerivedCategoryNatIso
namespace SheafOfModules.RingIsoTransport
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)]

private theorem derivedComp_hom {R S T : Sheaf J CommRingCat.{r}}
    (a : R ≅ S) (b : S ≅ T) :
    (derivedComp a b).hom =
      (Functor.mapDerivedCategoryCompIso (scalarRestriction a.inv)
        (scalarRestriction b.inv)).inv := by
  exact (congrArg (fun τ ↦
    (Functor.mapDerivedCategoryCompIso (scalarRestriction a.inv)
      (scalarRestriction b.inv)).inv ≫ τ)
    (Functor.mapDerivedCategoryNatIso_refl (F := scalarRestriction a.inv ⋙
      scalarRestriction b.inv))).trans (Category.comp_id _)

private theorem derivedId_hom (R : Sheaf J CommRingCat.{r}) :
    (derivedId R).hom = (Functor.mapDerivedCategoryIdIso (scalarModules J R)).hom := by
  exact (congrArg (fun τ ↦ τ ≫
    (Functor.mapDerivedCategoryIdIso (scalarModules J R)).hom)
    (Functor.mapDerivedCategoryNatIso_refl (F := 𝟭 (scalarModules J R)))).trans
      (Category.id_comp _)

attribute [local irreducible] derivedComp derivedId

/-- The left identity law for derived coefficient restriction is the left unit law
of the exact derived-functor compositor. The ordinary comparison is identity on
sections, so its image is an identity natural transformation.
Source: literature/stacks-project/categories.tex; literature/stacks-project/derived.tex; Tags
04VG/04VK and 015F; exact derived-functor unit and compositor coherence.
(blueprint: lem-pur-u2-derived-restriction-cocycle). -/
theorem derived_left_unit {R S : Sheaf J CommRingCat.{r}} (a : R ≅ S)
    (X : DerivedCategory (scalarModules J R)) :
    (derivedComp (Iso.refl R) a).hom.app X ≫
      (eqToIso (congrArg (fun c : R ≅ S ↦
        (scalarRestriction c.inv).mapDerivedCategory) (Iso.refl_trans a))).hom.app X =
    (scalarRestriction a.inv).mapDerivedCategory.map ((derivedId R).hom.app X) := by
  rw [derivedComp_hom, derivedId_hom]
  change (Functor.mapDerivedCategoryCompIso (𝟭 (scalarModules J R))
    (scalarRestriction a.inv)).inv.app X ≫ 𝟙 _ = _
  rw [Category.comp_id]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso (𝟭 (scalarModules J R))
    (scalarRestriction a.inv)).hom.app X)).1
  rw [Iso.hom_inv_id_app]
  exact (congr_app (Functor.mapDerivedCategoryCompIso_id_comp
    (scalarRestriction a.inv)) X).symm

/-- The right identity law follows from the right unit law of the exact
 derived-functor compositor, after identifying ordinary restriction by the identity.
Source: literature/stacks-project/categories.tex; literature/stacks-project/derived.tex; Tags
04VG/04VK and 015F; exact derived-functor unit and compositor coherence.
(blueprint: lem-pur-u2-derived-restriction-cocycle). -/
theorem derived_right_unit {R S : Sheaf J CommRingCat.{r}} (a : R ≅ S)
    (X : DerivedCategory (scalarModules J R)) :
    (derivedComp a (Iso.refl S)).hom.app X ≫
      (eqToIso (congrArg (fun c : R ≅ S ↦
        (scalarRestriction c.inv).mapDerivedCategory) (Iso.trans_refl a))).hom.app X =
    (derivedId S).hom.app ((scalarRestriction a.inv).mapDerivedCategory.obj X) := by
  rw [derivedComp_hom, derivedId_hom]
  change (Functor.mapDerivedCategoryCompIso (scalarRestriction a.inv)
    (𝟭 (scalarModules J S))).inv.app X ≫ 𝟙 _ = _
  rw [Category.comp_id]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso (scalarRestriction a.inv)
    (𝟭 (scalarModules J S))).hom.app X)).1
  rw [Iso.hom_inv_id_app]
  exact (congr_app (Functor.mapDerivedCategoryCompIso_comp_id
    (scalarRestriction a.inv)) X).symm

/-- The three-factor cocycle is the inverse of the associativity law for the exact
 derived-functor compositor. Ordinary restriction is strictly compositional on
 sections; the displayed ring-map reassociation therefore acts by an identity.
Source: literature/stacks-project/categories.tex; literature/stacks-project/derived.tex; Tags
04VG/04VK and 015F; exact derived-functor unit and compositor coherence.
(blueprint: lem-pur-u2-derived-restriction-cocycle). -/
theorem derived_assoc {R S T V : Sheaf J CommRingCat.{r}}
    (a : R ≅ S) (b : S ≅ T) (c : T ≅ V)
    (X : DerivedCategory (scalarModules J R)) :
    (scalarRestriction c.inv).mapDerivedCategory.map ((derivedComp a b).hom.app X) ≫
      (derivedComp (a ≪≫ b) c).hom.app X ≫
      (eqToIso (congrArg (fun d : R ≅ V ↦
        (scalarRestriction d.inv).mapDerivedCategory) (Iso.trans_assoc a b c))).hom.app X =
    (derivedComp b c).hom.app ((scalarRestriction a.inv).mapDerivedCategory.obj X) ≫
      (derivedComp a (b ≪≫ c)).hom.app X := by
  have hr : (eqToIso (congrArg (fun d : R ≅ V ↦
      (scalarRestriction d.inv).mapDerivedCategory) (Iso.trans_assoc a b c))).hom.app X =
        𝟙 _ := rfl
  erw [hr, Category.comp_id]
  unfold derivedComp Functor.exactDerivedRestrictionComposition
  exact Functor.mapDerivedCategoryCompNatIso_cocycle
    (ordinaryComp a b) (ordinaryComp (a ≪≫ b) c)
    (ordinaryComp b c) (ordinaryComp a (b ≪≫ c))
    (fun M ↦ by change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _; rfl) X

end SheafOfModules.RingIsoTransport
