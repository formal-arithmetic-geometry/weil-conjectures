/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.CategoryTheory.SheafTensor
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Coherence of exact scalar extension for sheaf module objects

Source: blueprint main-20261015, `sk-thm-sfb-qlbar-two-colimit`, proof (4) and the final
cocone paragraph; Stacks Tag 03CZ (blueprint: lem-sfb-flat-scalar-tower-coherence).

The comparisons are the existing `Mod.extendScalarsComp` (in the inverse orientation)
and `Mod.extendScalarsId`. The derived comparisons below apply the existing exact-functor
localization construction to these specified maps. The predicates package the clauses
without choosing a second tensor product or a second extension functor.
-/

@[expose] public section

universe u v uS vS w wA wB wC wR

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj

namespace CategoryTheory.Mod

/-- A specified comparison restricts to every preserved full subcategory, with precisely
its ambient components in both directions. Thus any equation between composites of these
components is an equation of restricted morphisms as well, by faithfulness of inclusion.
Source: blueprint proof (4), final cocone paragraph
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
def ScalarComparisonRestricts {D : Type u} [Category.{v} D]
    {E : Type uS} [Category.{vS} E] {F G : D ⥤ E} (e : F ≅ G) : Prop :=
  ∀ (P : ObjectProperty D) (Q : ObjectProperty E)
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (hG : ∀ X : P.FullSubcategory, Q (G.obj X.obj)),
    ∃ r : Q.lift (P.ι ⋙ F) hF ≅ Q.lift (P.ι ⋙ G) hG,
      (∀ X : P.FullSubcategory, (r.hom.app X).hom = e.hom.app X.obj) ∧
      (∀ X : P.FullSubcategory, (r.inv.app X).hom = e.inv.app X.obj)

section Ambient

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The two quotient-map equations expressing `c ⊗ (b ⊗ m) ↦ c ψ(b) ⊗ m`
and `c ⊗ m ↦ c ⊗ (1 ⊗ m)`, and restriction of this same comparison.
They assert equations of sheaf morphisms, so do not assume sections are pure tensors.
Source: Stacks 03CZ; blueprint proof (4)
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
def ScalarExtensionTensorLaws : Prop :=
  ∀ (A B C : H) [MonObj A] [MonObj B] [MonObj C]
    [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj C]
    (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g] (M : Mod H A),
    (C ◁ extendπ f M ≫ extendπ g ((extendScalars f).obj M) ≫
        ((extendScalarsComp f g).inv.app M).hom =
      (α_ C B M.X).inv ≫ (C ◁ g ≫ μ[C]) ▷ M.X ≫ extendπ (f ≫ g) M) ∧
    (extendπ (f ≫ g) M ≫ ((extendScalarsComp f g).hom.app M).hom =
      C ◁ extendUnitHom f M ≫ extendπ g ((extendScalars f).obj M)) ∧
    ScalarComparisonRestricts (extendScalarsComp f g).symm

/-- The identity extension has action as its map, and the two identity comparisons
are the corresponding unit identifications. Source: Stacks 03CZ; blueprint proof (4)
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
def ScalarExtensionUnitLaws : Prop :=
  (∀ (A : H) [MonObj A] [IsCommMonObj A] (M : Mod H A),
    extendπ (𝟙 A) M ≫ ((extendScalarsId (R := A)).hom.app M).hom = γ[A,M.X] ∧
    ((extendScalarsId (R := A)).inv.app M).hom = extendUnitHom (𝟙 A) M ∧
    ScalarComparisonRestricts (extendScalarsId (R := A))) ∧
  (∀ (A B : H) [MonObj A] [MonObj B] [IsCommMonObj A] [IsCommMonObj B]
    (f : A ⟶ B) [IsMonHom f] (M : Mod H A),
    (extendScalarsComp (𝟙 A) f).inv.app M ≫
        eqToHom (by simp only [Category.id_comp, Functor.id_obj]) =
      (extendScalars f).map ((extendScalarsId (R := A)).hom.app M) ∧
    (extendScalarsComp f (𝟙 B)).inv.app M ≫
        eqToHom (by simp only [Category.comp_id, Functor.id_obj]) =
      (extendScalarsId (R := B)).hom.app ((extendScalars f).obj M))

/-- The ordinary four-ring coherence equation. The final `eqToHom` only identifies
`(f ≫ g) ≫ h` with `f ≫ (g ≫ h)`; it is not a new comparison.
Source: Stacks 03CZ; blueprint proof (4)
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
def ScalarExtensionTowerLaws : Prop :=
  ∀ (A B C R : H) [MonObj A] [MonObj B] [MonObj C] [MonObj R]
    [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj C] [IsCommMonObj R]
    (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g]
    (h : C ⟶ R) [IsMonHom h] (M : Mod H A),
    (extendScalars h).map ((extendScalarsComp f g).inv.app M) ≫
        (extendScalarsComp (f ≫ g) h).inv.app M ≫
        eqToHom (by simp only [Category.assoc]) =
      (extendScalarsComp g h).inv.app ((extendScalars f).obj M) ≫
        (extendScalarsComp f (g ≫ h)).inv.app M

end Ambient

section Derived

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {A B C : H} [MonObj A] [MonObj B] [MonObj C]
  [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj C]
  [Abelian (Mod H A)] [Abelian (Mod H B)] [Abelian (Mod H C)]
  [HasDerivedCategory.{wA} (Mod H A)] [HasDerivedCategory.{wB} (Mod H B)]
  [HasDerivedCategory.{wC} (Mod H C)]
  (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g]
  [(extendScalars f).Additive] [(extendScalars g).Additive]
  [(extendScalars (f ≫ g)).Additive]
  [PreservesFiniteLimits (extendScalars f)] [PreservesFiniteColimits (extendScalars f)]
  [PreservesFiniteLimits (extendScalars g)] [PreservesFiniteColimits (extendScalars g)]
  [PreservesFiniteLimits (extendScalars (f ≫ g))]
  [PreservesFiniteColimits (extendScalars (f ≫ g))]

/-- The derived comparison obtained by applying the ordinary comparison in each degree
and localizing. This uses the canonical localization comparisons for composite exact
functors, rather than choosing an unspecified isomorphism.
Source: Stacks 015F and 04VG; blueprint proof (4)
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
noncomputable def flatDerivedScalarComp :
    (extendScalars f).mapDerivedCategory ⋙ (extendScalars g).mapDerivedCategory ≅
      (extendScalars (f ≫ g)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (extendScalars f) (extendScalars g)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (extendScalarsComp f g).symm

end Derived

section DerivedUnit

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (A : H) [MonObj A] [IsCommMonObj A] [Abelian (Mod H A)]
  [HasDerivedCategory.{wA} (Mod H A)]
  [(extendScalars (𝟙 A)).Additive]
  [PreservesFiniteLimits (extendScalars (𝟙 A))]
  [PreservesFiniteColimits (extendScalars (𝟙 A))]

/-- The derived identity comparison, obtained from the ordinary action map termwise.
Source: Stacks 015F and 04VG; blueprint proof (4)
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
noncomputable def flatDerivedScalarId :
    (extendScalars (𝟙 A)).mapDerivedCategory ≅ 𝟭 (DerivedCategory (Mod H A)) :=
  Functor.mapDerivedCategoryNatIso (extendScalarsId (R := A)) ≪≫
    Functor.mapDerivedCategoryIdIso (Mod H A)

end DerivedUnit

section DerivedLaws

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The four-ring equality on unbounded derived categories, for exact extensions along
all six maps of the tower. The comparison is the localized termwise comparison defined
above, also on preserved full subcategories.
Source: Stacks 015F and 04VG; blueprint proof (4)
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
def FlatDerivedScalarTowerLaws : Prop :=
  ∀ (A B C R : H) [MonObj A] [MonObj B] [MonObj C] [MonObj R]
    [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj C] [IsCommMonObj R]
    [Abelian (Mod H A)] [HasDerivedCategory.{wA} (Mod H A)]
    [Abelian (Mod H B)] [HasDerivedCategory.{wB} (Mod H B)]
    [Abelian (Mod H C)] [HasDerivedCategory.{wC} (Mod H C)]
    [Abelian (Mod H R)] [HasDerivedCategory.{wR} (Mod H R)]
    (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g]
    (h : C ⟶ R) [IsMonHom h]
    [(extendScalars (f)).Additive]
    [PreservesFiniteLimits (extendScalars (f))]
    [PreservesFiniteColimits (extendScalars (f))]
    [(extendScalars (g)).Additive]
    [PreservesFiniteLimits (extendScalars (g))]
    [PreservesFiniteColimits (extendScalars (g))]
    [(extendScalars (h)).Additive]
    [PreservesFiniteLimits (extendScalars (h))]
    [PreservesFiniteColimits (extendScalars (h))]
    [(extendScalars (f ≫ g)).Additive]
    [PreservesFiniteLimits (extendScalars (f ≫ g))]
    [PreservesFiniteColimits (extendScalars (f ≫ g))]
    [(extendScalars (g ≫ h)).Additive]
    [PreservesFiniteLimits (extendScalars (g ≫ h))]
    [PreservesFiniteColimits (extendScalars (g ≫ h))]
    [(extendScalars ((f ≫ g) ≫ h)).Additive]
    [PreservesFiniteLimits (extendScalars ((f ≫ g) ≫ h))]
    [PreservesFiniteColimits (extendScalars ((f ≫ g) ≫ h))]
    [(extendScalars (f ≫ g ≫ h)).Additive]
    [PreservesFiniteLimits (extendScalars (f ≫ g ≫ h))]
    [PreservesFiniteColimits (extendScalars (f ≫ g ≫ h))]
    (K : DerivedCategory (Mod H A)),
    ((extendScalars h).mapDerivedCategory.map ((flatDerivedScalarComp f g).hom.app K) ≫
        (flatDerivedScalarComp (f ≫ g) h).hom.app K ≫
        eqToHom (by simp only [Category.assoc]) =
      (flatDerivedScalarComp g h).hom.app ((extendScalars f).mapDerivedCategory.obj K) ≫
        (flatDerivedScalarComp f (g ≫ h)).hom.app K) ∧
    ScalarComparisonRestricts (flatDerivedScalarComp f g) ∧
    ScalarComparisonRestricts (flatDerivedScalarComp g h) ∧
    ScalarComparisonRestricts (flatDerivedScalarComp (f ≫ g) h) ∧
    ScalarComparisonRestricts (flatDerivedScalarComp f (g ≫ h))

/-- Both identity compatibilities after termwise extension and localization, including
restriction of the action identification to preserved full subcategories.
Source: Stacks 015F and 04VG; blueprint proof (4)
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
def FlatDerivedScalarUnitLaws : Prop :=
  ∀ (A B : H) [MonObj A] [MonObj B] [IsCommMonObj A] [IsCommMonObj B]
    [Abelian (Mod H A)] [HasDerivedCategory.{wA} (Mod H A)]
    [Abelian (Mod H B)] [HasDerivedCategory.{wB} (Mod H B)]
    (f : A ⟶ B) [IsMonHom f]
    [(extendScalars (f)).Additive]
    [PreservesFiniteLimits (extendScalars (f))]
    [PreservesFiniteColimits (extendScalars (f))]
    [(extendScalars (𝟙 A)).Additive]
    [PreservesFiniteLimits (extendScalars (𝟙 A))]
    [PreservesFiniteColimits (extendScalars (𝟙 A))]
    [(extendScalars (𝟙 B)).Additive]
    [PreservesFiniteLimits (extendScalars (𝟙 B))]
    [PreservesFiniteColimits (extendScalars (𝟙 B))]
    [(extendScalars (𝟙 A ≫ f)).Additive]
    [PreservesFiniteLimits (extendScalars (𝟙 A ≫ f))]
    [PreservesFiniteColimits (extendScalars (𝟙 A ≫ f))]
    [(extendScalars (f ≫ 𝟙 B)).Additive]
    [PreservesFiniteLimits (extendScalars (f ≫ 𝟙 B))]
    [PreservesFiniteColimits (extendScalars (f ≫ 𝟙 B))]
    (K : DerivedCategory (Mod H A)),
    ((flatDerivedScalarComp (𝟙 A) f).hom.app K ≫
        eqToHom (by simp only [Category.id_comp, Functor.id_obj]) =
      (extendScalars f).mapDerivedCategory.map ((flatDerivedScalarId A).hom.app K)) ∧
    ((flatDerivedScalarComp f (𝟙 B)).hom.app K ≫
        eqToHom (by simp only [Category.comp_id, Functor.id_obj]) =
      (flatDerivedScalarId B).hom.app ((extendScalars f).mapDerivedCategory.obj K)) ∧
    ScalarComparisonRestricts (flatDerivedScalarId A) ∧
    ScalarComparisonRestricts (flatDerivedScalarId B) ∧
    ScalarComparisonRestricts (flatDerivedScalarComp (𝟙 A) f) ∧
    ScalarComparisonRestricts (flatDerivedScalarComp f (𝟙 B))

end DerivedLaws

/-- Package of the ordinary tensor, unit and tower equations and their exact-derived
counterparts, on one fixed braided monoidal category. Coequalizers and tensor preservation
are quantified as proof-valued infrastructure: the sheaf tensor supplies them, and the
package works for any choices of their witnesses. Exactness and abelianness are assumed
only in the derived clauses, and only for the rings and maps in the particular tower.
Source: blueprint proof (4); Stacks 03CZ, 015F and 04VG
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
def FlatScalarTowerCoherence {H : Type u} [Category.{v} H]
    [MonoidalCategory H] [BraidedCategory H] : Prop :=
  HasCoequalizers H ∧
  (∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X) ∧
    PreservesColimitsOfSize.{0, 0} (tensorRight X)) ∧
  ∀ [HasCoequalizers H]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)],
    ScalarExtensionTensorLaws (H := H) ∧
    ScalarExtensionUnitLaws (H := H) ∧
    ScalarExtensionTowerLaws (H := H) ∧
    FlatDerivedScalarTowerLaws.{u, v, wA, wB, wC, wR} (H := H) ∧
    FlatDerivedScalarUnitLaws.{u, v, wA, wB} (H := H)

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_restricts {D : Type u} [Category.{v} D]
    {E : Type uS} [Category.{vS} E] {F G : D ⥤ E} (e : F ≅ G) :
    ScalarComparisonRestricts e := by
  intro P Q hF hG
  refine ⟨NatIso.ofComponents (fun X ↦ Q.isoMk (e.app X.obj)) ?_, ?_, ?_⟩
  · intro X Y f
    apply Q.ι.map_injective
    exact e.hom.naturality f.hom
  · intro X
    rfl
  · intro X
    rfl

section OrdinaryProof

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {A B C : H} [MonObj A] [MonObj B] [MonObj C]
  [IsCommMonObj A] [IsCommMonObj B]
  (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g]

set_option backward.isDefEq.respectTransparency false in
private theorem comp_hom_unit (M : Mod H A) :
    extendUnitHom (f ≫ g) M ≫ ((extendScalarsComp f g).hom.app M).hom =
      extendUnitHom f M ≫ extendUnitHom g ((extendScalars f).obj M) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (extendRestrictAdjunction (f ≫ g))
    (((extendRestrictAdjunction f).comp (extendRestrictAdjunction g)).ofNatIsoRight
      (comapComp f g).symm) M
  have hh := congrArg Hom.hom h
  simp only [Functor.id_obj, Functor.comp_obj, extendRestrictAdjunction,
    Adjunction.mkOfHomEquiv_unit_app, extendHomEquiv, Equiv.coe_fn_mk, Category.assoc,
    comp_hom', extendUnit_hom, comap_map_hom, id_hom', Adjunction.ofNatIsoRight_unit,
    Iso.symm_hom, NatTrans.comp_app, Adjunction.comp_unit_app, Functor.map_comp,
    Functor.whiskerLeft_app, comapComp_inv_app_hom] at hh
  change extendUnitHom (f ≫ g) M ≫ 𝟙 _ ≫
      ((extendScalarsComp f g).hom.app M).hom =
    extendUnitHom f M ≫ 𝟙 _ ≫ extendUnitHom g ((extendScalars f).obj M) ≫ 𝟙 _ ≫ 𝟙 _ at hh
  simpa only [Category.id_comp, Category.comp_id] using hh

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem comp_inv_unit (M : Mod H A) :
    extendUnitHom f M ≫ extendUnitHom g ((extendScalars f).obj M) ≫
      ((extendScalarsComp f g).inv.app M).hom = extendUnitHom (f ≫ g) M := by
  rw [← Category.assoc, ← comp_hom_unit f g M, Category.assoc, ← comp_hom']
  rw [Iso.hom_inv_id_app]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
omit [IsCommMonObj B] in
@[reassoc]
private theorem unit_naturality {M N : Mod H A} (p : M ⟶ N) :
    extendUnitHom f M ≫ ((extendScalars f).map p).hom =
      p.hom ≫ extendUnitHom f N := by
  have h := congrArg Hom.hom ((extendRestrictAdjunction f).unit.naturality p)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, extendRestrictAdjunction,
    Adjunction.mkOfHomEquiv_unit_app, extendHomEquiv, Equiv.coe_fn_mk, comp_hom',
    extendUnit_hom, comap_map_hom, id_hom', Functor.comp_map, extendScalars_map,
    Category.assoc] at h
  change p.hom ≫ extendUnitHom f N ≫ 𝟙 _ =
    extendUnitHom f M ≫ 𝟙 _ ≫ ((extendScalars f).map p).hom at h
  simpa only [Category.id_comp, Category.comp_id] using h.symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem comp_hom_tensor (M : Mod H A) :
    extendπ (f ≫ g) M ≫ ((extendScalarsComp f g).hom.app M).hom =
      C ◁ extendUnitHom f M ≫ extendπ g ((extendScalars f).obj M) := by
  rw [← whiskerLeft_extendUnitHom_smul' (f ≫ g) M, Category.assoc,
    act_hom, ← whiskerLeft_comp_assoc, comp_hom_unit, whiskerLeft_comp_assoc,
    whiskerLeft_extendUnitHom_smul']

set_option backward.isDefEq.respectTransparency false in
private theorem id_hom_unit (M : Mod H A) :
    extendUnitHom (𝟙 A) M ≫ ((extendScalarsId (R := A)).hom.app M).hom = 𝟙 M.X := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (extendRestrictAdjunction (𝟙 A)) (Adjunction.id.ofNatIsoRight (comapId A).symm) M
  have hh := congrArg Hom.hom h
  simp only [Functor.id_obj, Functor.comp_obj, extendRestrictAdjunction,
    Adjunction.mkOfHomEquiv_unit_app, extendHomEquiv, Equiv.coe_fn_mk, Category.assoc,
    comp_hom', extendUnit_hom, comap_map_hom, id_hom', Adjunction.ofNatIsoRight_unit,
    Adjunction.id_unit, Iso.symm_hom, Category.id_comp, Functor.whiskerLeft_app,
    comapId_inv_app_hom] at hh
  change extendUnitHom (𝟙 A) M ≫ 𝟙 _ ≫
    ((extendScalarsId (R := A)).hom.app M).hom = 𝟙 M.X at hh
  simpa only [Category.id_comp] using hh

set_option backward.isDefEq.respectTransparency false in
private theorem id_inv_unit (M : Mod H A) :
    ((extendScalarsId (R := A)).inv.app M).hom = extendUnitHom (𝟙 A) M := by
  apply (cancel_mono ((extendScalarsId (R := A)).hom.app M).hom).mp
  rw [← comp_hom', Iso.inv_hom_id_app, id_hom', id_hom_unit]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem comp_inv_tensor (M : Mod H A) :
    C ◁ extendπ f M ≫ extendπ g ((extendScalars f).obj M) ≫
        ((extendScalarsComp f g).inv.app M).hom =
      (α_ C B M.X).inv ≫ (C ◁ g ≫ μ[C]) ▷ M.X ≫ extendπ (f ≫ g) M := by
  change C ◁ extendπ f M ≫ extendπ g (extendScalarsObj f M) ≫
    ((extendScalarsComp f g).inv.app M).hom = _
  rw [← whiskerLeft_extendUnitHom_smul' f M, whiskerLeft_comp_assoc,
    whiskerLeft_smul_extendπ_assoc, associator_inv_naturality_right_assoc,
    whisker_exchange_assoc]
  change (α_ C B M.X).inv ≫ (C ◁ g ≫ μ[C]) ▷ M.X ≫
      C ◁ extendUnitHom f M ≫ extendπ g ((extendScalars f).obj M) ≫
      ((extendScalarsComp f g).inv.app M).hom = _
  rw [← comp_hom_tensor_assoc, ← comp_hom', Iso.hom_inv_id_app, id_hom']
  change (α_ C B M.X).inv ≫ (C ◁ g ≫ μ[C]) ▷ M.X ≫
    extendπ (f ≫ g) M ≫ 𝟙 _ = _
  rw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem id_hom_tensor (M : Mod H A) :
    extendπ (𝟙 A) M ≫ ((extendScalarsId (R := A)).hom.app M).hom = γ[A,M.X] := by
  rw [← whiskerLeft_extendUnitHom_smul' (𝟙 A) M, Category.assoc,
    act_hom, ← whiskerLeft_comp_assoc, id_hom_unit, whiskerLeft_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
omit [IsCommMonObj B] in
private theorem unit_transport {f' : A ⟶ B} [IsMonHom f'] (e : f = f') (M : Mod H A)
    (eM : (extendScalars f).obj M = (extendScalars f').obj M) :
    extendUnitHom f M ≫ (eqToHom eM).hom = extendUnitHom f' M := by
  subst f'
  simp only [eqToHom_refl, id_hom']
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
private theorem tower_laws : ScalarExtensionTowerLaws (H := H) := by
  intro A B C R _ _ _ _ _ _ _ _ f _ g _ h _ M
  apply (extendHomEquiv h _ _).injective
  apply (extendHomEquiv g _ _).injective
  apply (extendHomEquiv f _ _).injective
  apply hom_ext
  change extendUnitHom f M ≫ extendUnitHom g ((extendScalars f).obj M) ≫
      extendUnitHom h ((extendScalars g).obj ((extendScalars f).obj M)) ≫
      (((extendScalars h).map ((extendScalarsComp f g).inv.app M) ≫
        (extendScalarsComp (f ≫ g) h).inv.app M ≫ eqToHom _).hom) =
    extendUnitHom f M ≫ extendUnitHom g ((extendScalars f).obj M) ≫
      extendUnitHom h ((extendScalars g).obj ((extendScalars f).obj M)) ≫
      (((extendScalarsComp g h).inv.app ((extendScalars f).obj M) ≫
        (extendScalarsComp f (g ≫ h)).inv.app M).hom)
  simp only [comp_hom']
  rw [unit_naturality_assoc, comp_inv_unit_assoc, comp_inv_unit_assoc,
    unit_transport _ (Category.assoc f g h) M]
  rw [comp_inv_unit_assoc, comp_inv_unit]

set_option backward.isDefEq.respectTransparency false in
private theorem unit_laws : ScalarExtensionUnitLaws (H := H) := by
  constructor
  · intro A _ _ M
    exact ⟨id_hom_tensor M, id_inv_unit M, comparison_restricts _⟩
  · intro A B _ _ _ _ f _ M
    constructor
    · apply (extendHomEquiv f _ _).injective
      apply (extendHomEquiv (𝟙 A) _ _).injective
      apply hom_ext
      change extendUnitHom (𝟙 A) M ≫
        extendUnitHom f ((extendScalars (𝟙 A)).obj M) ≫
        (((extendScalarsComp (𝟙 A) f).inv.app M ≫ eqToHom _).hom) =
        extendUnitHom (𝟙 A) M ≫
        extendUnitHom f ((extendScalars (𝟙 A)).obj M) ≫
          ((extendScalars f).map ((extendScalarsId (R := A)).hom.app M)).hom
      simp only [comp_hom']
      rw [comp_inv_unit_assoc, unit_transport _ (Category.id_comp f) M,
        unit_naturality, ← Category.assoc, id_hom_unit, Category.id_comp]
      rfl
    · apply (extendHomEquiv (𝟙 B) _ _).injective
      apply (extendHomEquiv f _ _).injective
      apply hom_ext
      change extendUnitHom f M ≫ extendUnitHom (𝟙 B) ((extendScalars f).obj M) ≫
        (((extendScalarsComp f (𝟙 B)).inv.app M ≫ eqToHom _).hom) =
        extendUnitHom f M ≫ extendUnitHom (𝟙 B) ((extendScalars f).obj M) ≫
          ((extendScalarsId (R := B)).hom.app ((extendScalars f).obj M)).hom
      simp only [comp_hom']
      rw [comp_inv_unit_assoc, unit_transport _ (Category.comp_id f) M,
        id_hom_unit]
      exact (Category.comp_id _).symm

end OrdinaryProof

section DerivedProof

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {D₀ D₁ D₂ D₃ : Type*}
  [Category D₀] [Category D₁] [Category D₂] [Category D₃]
  [Abelian D₀] [Abelian D₁] [Abelian D₂] [Abelian D₃]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁]
  [HasDerivedCategory D₂] [HasDerivedCategory D₃]
  (F : D₀ ⥤ D₁) (G : D₁ ⥤ D₂) (H : D₂ ⥤ D₃)
  (U : D₀ ⥤ D₂) (V : D₁ ⥤ D₃) (T : D₀ ⥤ D₃)
  [F.Additive] [G.Additive] [H.Additive] [U.Additive] [V.Additive] [T.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]

set_option backward.isDefEq.respectTransparency false in
private theorem derive_coherence (a : U ≅ F ⋙ G) (b : T ≅ U ⋙ H)
    (c : V ≅ G ⋙ H) (d : T ≅ F ⋙ V)
    (hab : b ≪≫ Functor.isoWhiskerRight a H = d ≪≫ Functor.isoWhiskerLeft F c) :
    (Functor.mapDerivedCategoryTriangleIso b ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryTriangleIso a)
          H.mapDerivedCategory) =
      (Functor.mapDerivedCategoryTriangleIso d ≪≫
        Functor.isoWhiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryTriangleIso c)) := by
  apply Iso.ext
  have hm := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom) hab
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hm
  have hwr := Functor.mapDerivedCategoryNatIso_isoWhiskerRight a H
  have hwl := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F c
  have ha := Functor.mapDerivedCategoryCompIso_assoc F G H
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_comp,
    Functor.whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% hwr, ← reassoc_of% hwl, ← ha, reassoc_of% hm]

set_option backward.isDefEq.respectTransparency false in
private theorem derive_tower_transport (T' : D₀ ⥤ D₃) [T'.Additive]
    [PreservesFiniteLimits T'] [PreservesFiniteColimits T']
    (a : U ≅ F ⋙ G) (b : T ≅ U ⋙ H) (c : V ≅ G ⋙ H) (d : T' ≅ F ⋙ V)
    (e : T = T')
    (hab : ∀ X, H.map (a.inv.app X) ≫ b.inv.app X ≫
      eqToHom (congrArg (fun L ↦ L.obj X) e) = c.inv.app (F.obj X) ≫ d.inv.app X)
    (K : DerivedCategory D₀) :
    H.mapDerivedCategory.map ((Functor.mapDerivedCategoryTriangleIso a).inv.app K) ≫
        (Functor.mapDerivedCategoryTriangleIso b).inv.app K ≫
        eqToHom (by subst T'; rfl) =
      (Functor.mapDerivedCategoryTriangleIso c).inv.app (F.mapDerivedCategory.obj K) ≫
        (Functor.mapDerivedCategoryTriangleIso d).inv.app K := by
  subst T'
  have hi : (Functor.isoWhiskerRight a H).symm ≪≫ b.symm =
      (Functor.isoWhiskerLeft F c).symm ≪≫ d.symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, eqToHom_refl,
      Category.comp_id] using hab X
  have hf := congrArg Iso.symm hi
  change b ≪≫ Functor.isoWhiskerRight a H = d ≪≫ Functor.isoWhiskerLeft F c at hf
  have hd := derive_coherence F G H U V T a b c d hf
  have hk := congrArg (fun z ↦ z.inv.app K) hd
  simpa only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    eqToHom_refl, Category.comp_id] using hk

end DerivedProof

section DerivedUnitProof

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
  [HasDerivedCategory D] [HasDerivedCategory E]
  (F T : D ⥤ E) [F.Additive] [T.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]

set_option backward.isDefEq.respectTransparency false in
private theorem derive_left_unit (U : D ⥤ D) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (e : U ≅ 𝟭 D) (a : T ≅ U ⋙ F) (hT : T = F)
    (ha : ∀ X, a.inv.app X ≫ eqToHom (congrArg (fun L ↦ L.obj X) hT) =
      F.map (e.hom.app X)) (K : DerivedCategory D) :
    (Functor.mapDerivedCategoryTriangleIso a).inv.app K ≫
        eqToHom (by subst T; rfl) =
      F.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso D).hom.app K)
        := by
  subst T
  have heq : a.symm = Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    simpa only [Iso.symm_hom, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, eqToHom_refl, Functor.id_obj,
      Functor.comp_obj, Category.comp_id] using ha X
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e F) K
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp F) K
  have hi : (Functor.mapDerivedCategoryNatIso (Functor.leftUnitor F)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  have hh := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso z).hom.app K) heq
  simp only [Functor.mapDerivedCategoryNatIso_trans, hi, Category.comp_id] at hh
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hn hu
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_inv, NatTrans.comp_app,
    ← Functor.mapDerivedCategoryNatIso_symm, hh, Iso.trans_hom, Functor.map_comp,
    eqToHom_refl, Category.comp_id]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso U F).hom.app K),
    Iso.hom_inv_id_app_assoc, ← reassoc_of% hn, hu]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem derive_right_unit (U : E ⥤ E) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (e : U ≅ 𝟭 E) (a : T ≅ F ⋙ U) (hT : T = F)
    (ha : ∀ X, a.inv.app X ≫ eqToHom (congrArg (fun L ↦ L.obj X) hT) =
      e.hom.app (F.obj X)) (K : DerivedCategory D) :
    (Functor.mapDerivedCategoryTriangleIso a).inv.app K ≫
        eqToHom (by subst T; rfl) =
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso E).hom.app
        (F.mapDerivedCategory.obj K) := by
  subst T
  have heq : a.symm = Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    simpa only [Iso.symm_hom, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, eqToHom_refl, Functor.id_obj,
      Functor.comp_obj, Category.comp_id] using ha X
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F e) K
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_comp_id F) K
  have hi : (Functor.mapDerivedCategoryNatIso (Functor.rightUnitor F)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  have hh := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso z).hom.app K) heq
  simp only [Functor.mapDerivedCategoryNatIso_trans, hi, Category.comp_id] at hh
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at hn hu
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_inv, NatTrans.comp_app,
    ← Functor.mapDerivedCategoryNatIso_symm, hh, Iso.trans_hom,
    eqToHom_refl, Category.comp_id]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso F U).hom.app K),
    Iso.hom_inv_id_app_assoc, ← reassoc_of% hn, hu]
  exact (Category.comp_id _).symm

end DerivedUnitProof

section ScalarDerivedProof

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

set_option backward.isDefEq.respectTransparency false in
private theorem derived_tower_laws :
    FlatDerivedScalarTowerLaws.{u, v, wA, wB, wC, wR} (H := H) := by
  intro A B C R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f _ g _ h _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K
  refine ⟨?_, comparison_restricts _, comparison_restricts _,
    comparison_restricts _, comparison_restricts _⟩
  have e : extendScalars ((f ≫ g) ≫ h) = extendScalars (f ≫ g ≫ h) := by
    congr 1
    exact Category.assoc f g h
  have ht := derive_tower_transport (extendScalars f) (extendScalars g) (extendScalars h)
    (extendScalars (f ≫ g)) (extendScalars (g ≫ h)) (extendScalars ((f ≫ g) ≫ h))
    (extendScalars (f ≫ g ≫ h)) (extendScalarsComp f g) (extendScalarsComp (f ≫ g) h)
    (extendScalarsComp g h) (extendScalarsComp f (g ≫ h)) e
    (fun M ↦ tower_laws A B C R f g h M) K
  simpa only [flatDerivedScalarComp, Functor.mapDerivedCategoryTriangleIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryNatIso_symm] using ht

end ScalarDerivedProof

set_option backward.isDefEq.respectTransparency false in
private theorem derived_unit_laws {H : Type u} [Category.{v} H]
    [MonoidalCategory H] [BraidedCategory H] [HasCoequalizers H]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)] :
    FlatDerivedScalarUnitLaws.{u, v, wA, wB} (H := H) := by
  intro A B _ _ _ _ _ _ _ _ f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K
  refine ⟨?_, ?_, comparison_restricts _, comparison_restricts _,
    comparison_restricts _, comparison_restricts _⟩
  · have e : extendScalars (𝟙 A ≫ f) = extendScalars f := by
      congr 1
      exact Category.id_comp f
    have ht := derive_left_unit (extendScalars f) (extendScalars (𝟙 A ≫ f))
      (extendScalars (𝟙 A)) (extendScalarsId (R := A)) (extendScalarsComp (𝟙 A) f) e
      (fun M ↦ ((unit_laws (H := H)).2 A B f M).1) K
    simpa only [flatDerivedScalarComp, flatDerivedScalarId,
      Functor.mapDerivedCategoryTriangleIso, Iso.trans_inv, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_symm] using ht
  · have e : extendScalars (f ≫ 𝟙 B) = extendScalars f := by
      congr 1
      exact Category.comp_id f
    have ht := derive_right_unit (extendScalars f) (extendScalars (f ≫ 𝟙 B))
      (extendScalars (𝟙 B)) (extendScalarsId (R := B)) (extendScalarsComp f (𝟙 B)) e
      (fun M ↦ ((unit_laws (H := H)).2 A B f M).2) K
    simpa only [flatDerivedScalarComp, flatDerivedScalarId,
      Functor.mapDerivedCategoryTriangleIso, Iso.trans_inv, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_symm] using ht

/-- Canonical scalar-extension comparisons on abelian sheaves satisfy the tensor formulas,
all tower and identity equations, and their exact-derived and full-subcategory versions.

Source: blueprint main-20261015, `sk-thm-sfb-qlbar-two-colimit`, proof (4) and final
cocone paragraph; Stacks 03CZ, 0B65, 015F and 04VG
(blueprint: lem-sfb-flat-scalar-tower-coherence).

Proof, following the ten steps of the node:
1. The closed sheaf tensor preserves colimits on either side, and its Grothendieck
abelian category has coequalizers. The specified extensions are therefore defined.
2. Compose `extendHomEquiv` for two maps. Restriction along a composite has the same
underlying action as successive restriction. The composite bijection takes a map h to
h after the two extension units, m ↦ 1 ⊗ (1 ⊗ m).
3. Uniqueness of left adjoints, with its unit equation (Stacks 0B65), gives precisely
`extendScalarsComp.symm`, normalized by sending the composite unit to the direct unit.
4. The coequalizer balancing relation moves b into the outer factor. Linearity and the
normalization give c ⊗ (b ⊗ m) ↦ c g(b) ⊗ m. The inverse sends c ⊗ m to
c ⊗ (1 ⊗ m). These are the two quotient-map equations in `ScalarExtensionTensorLaws`.
5. Compose three Hom bijections. Both paths around the four-ring square become the
direct extension unit when precomposed with the three units. Injectivity of the
bijection gives their equality, with the displayed associativity transport.
6. For identity maps the action coequalizes the defining pair. Its composite with the
unit is the identity by unitality; the reverse composite is the identity by the Hom
bijection. Both identity comparisons have the same unit normalization, proving the
unit equations, including the all-identity case.
7. Under the additional abelian and exactness hypotheses, termwise extension preserves
quasi-isomorphisms and induces `mapDerivedCategory` on the unbounded localizations
(Stacks 015F). No boundedness or resolution hypothesis is needed.
8. Apply the ordinary comparison in every degree. Naturality makes a chain map with
chain-map inverse; tower and unit equalities hold degree by degree.
9. Extend the termwise isomorphisms through localization (Stacks 04VG), using
`mapDerivedCategoryCompIso` and `mapDerivedCategoryNatIso`. Their factorization equations
identify them with the maps in step 8. Faithfulness of precomposition with localization
on natural transformations proves the derived tower and identity equations.
10. At an object of a preserved full subcategory both endpoints lie in the target full
subcategory. Lift the comparison and its inverse by fullness. Their ambient components
are unchanged, giving `ScalarComparisonRestricts`. Naturality and all equations descend
by faithfulness, for ordinary and derived categories alike.
-/
theorem sheaf_flatScalarTowerCoherence
    {S : Type uS} [Category.{vS} S] [EssentiallySmall.{w} S]
    (J : GrothendieckTopology S) :
    @FlatScalarTowerCoherence.{_, _, wA, wB, wC, wR} (Sheaf J Ab.{w}) _
      (sfbSheafTensorStructure (A := Ab.{w}) J).monoidal
      (sfbSheafTensorStructure (A := Ab.{w}) J).symmetric.toBraidedCategory := by
  let t := sfbSheafTensorStructure (A := Ab.{w}) J
  let : MonoidalCategory (Sheaf J Ab.{w}) := t.monoidal
  let : BraidedCategory (Sheaf J Ab.{w}) := t.symmetric.toBraidedCategory
  have hc : HasCoequalizers (Sheaf J Ab.{w}) := inferInstance
  have hp : ∀ X : Sheaf J Ab.{w}, PreservesColimitsOfSize.{0, 0} (tensorLeft X) ∧
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := by
    intro X
    exact ⟨((sfbSheafTensor_properties (A := Ab.{w}) J).2.2 X).1,
      ((sfbSheafTensor_properties (A := Ab.{w}) J).2.2 X).2.1⟩
  refine ⟨hc, hp, ?_⟩
  intro _ _ _
  refine ⟨?_, unit_laws, tower_laws, derived_tower_laws, ?_⟩
  · intro A B C _ _ _ _ _ _ f _ g _ M
    exact ⟨comp_inv_tensor f g M, comp_hom_tensor f g M, comparison_restricts _⟩
  · exact derived_unit_laws

end CategoryTheory.Mod
