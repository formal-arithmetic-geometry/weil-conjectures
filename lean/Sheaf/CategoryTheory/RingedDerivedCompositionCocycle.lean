/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

/-! # Coherence of normalized ringed-topos derived composition

Source: Stacks Project, Cohomology on Sites, Tag 0D6E, with coherence extracted
from the total-derived universal property
(blueprint: lem-pur-ringed-derived-composition-cocycle).

The comparison is specified by the unit equation of
`ringedToposDerivedPushforwardComposition`, which uniquely characterizes its
K-injective normalized comparison. Composite ordinary direct images are represented
by composites of the module functors, exactly as in that dependency. No preservation
of K-injectives is assumed. Identity-underlying-topos coefficient changes are included
without any condition on their structural ring maps.

## Main statements

- `ringedDerivedComposition_cocycle`: associativity of the normalized comparison.
- `ringedDerivedComposition_units`: normalized identity comparisons and both unit laws.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- The cocycle law for the K-injective normalized direct-image comparisons.
Source: Stacks Project, Cohomology on Sites, Tag 0D6E
(blueprint: lem-pur-ringed-derived-composition-cocycle).

The six functors with their units are arbitrary representatives of the total right
derived functors. The four unit equations are the characterization of kappa in
`ringedToposDerivedPushforwardComposition`; thus they specify the comparisons in
that node, rather than extra compatibility assumptions on arbitrary isomorphisms.

Proof: choose K-injective I on the source, and resolutions j:f_*I→J, k:g_*J→K,
and t:g_*f_*I→T, using prop-pur-kinjective-resolutions-exist. The normalized
composition theorem makes g_*j a quasi-isomorphism. The Hom bijection into K-injectives
(lem-weil-pbc-kinjective-hom-derived) supplies the unique homotopy class u:T→K
with ut homotopic to k(g_*j). One composite is Q(h_*(k(g_*j))). For the other,
lem-sf-kinjective-derived-map-computation gives Q(h_*u)Q(h_*t), equal to that
expression since additive h_* preserves the homotopy. Naturality transports this
calculation along a K-injective resolution of any complex, proving equality of
natural transformations. This works unchanged for coefficient restrictions. -/
theorem ringedDerivedComposition_cocycle
    {C0 : Type u} [SmallCategory C0]
    {C1 : Type u} [SmallCategory C1]
    {C2 : Type u} [SmallCategory C2]
    {C3 : Type u} [SmallCategory C3]
    (J0 : GrothendieckTopology C0) (A0 : Sheaf J0 CommRingCat.{u})
    (J1 : GrothendieckTopology C1) (A1 : Sheaf J1 CommRingCat.{u})
    (J2 : GrothendieckTopology C2) (A2 : Sheaf J2 CommRingCat.{u})
    (J3 : GrothendieckTopology C3) (A3 : Sheaf J3 CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J2 (forget₂ CommRingCat.{u} RingCat.{u})).obj A2))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J3 (forget₂ CommRingCat.{u} RingCat.{u})).obj A3))]
    (f : RingedToposMorphism ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)
      ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1))
    (g : RingedToposMorphism ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)
      ((sheafCompose J2 (forget₂ CommRingCat.{u} RingCat.{u})).obj A2))
    (h : RingedToposMorphism ((sheafCompose J2 (forget₂ CommRingCat.{u} RingCat.{u})).obj A2)
      ((sheafCompose J3 (forget₂ CommRingCat.{u} RingCat.{u})).obj A3))
    (Rf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)))
    (Rg : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J2 (forget₂ CommRingCat.{u} RingCat.{u})).obj A2)))
    (Rh : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J2 (forget₂ CommRingCat.{u} RingCat.{u})).obj A2)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J3 (forget₂ CommRingCat.{u} RingCat.{u})).obj A3)))
    (Rgf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J2 (forget₂ CommRingCat.{u} RingCat.{u})).obj A2)))
    (Rhg : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J3 (forget₂ CommRingCat.{u} RingCat.{u})).obj A3)))
    (Rhgf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J3 (forget₂ CommRingCat.{u} RingCat.{u})).obj A3)))
    (ηf : (f.modules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rf)
    (ηg : (g.modules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rg)
    (ηh : (h.modules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rh)
    (ηgf : (f.modules ⋙ g.modules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rgf)
    (ηhg : (g.modules ⋙ h.modules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rhg)
    (ηhgf : ((f.modules ⋙ g.modules) ⋙ h.modules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rhgf)
    [Rf.IsRightDerivedFunctor ηf
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) (.up ℤ))]
    [Rg.IsRightDerivedFunctor ηg
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)) (.up ℤ))]
    [Rh.IsRightDerivedFunctor ηh
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J2 (forget₂ CommRingCat.{u} RingCat.{u})).obj A2)) (.up ℤ))]
    [Rgf.IsRightDerivedFunctor ηgf
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) (.up ℤ))]
    [Rhg.IsRightDerivedFunctor ηhg
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)) (.up ℤ))]
    [Rhgf.IsRightDerivedFunctor ηhgf
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) (.up ℤ))]
    (κgf : Rgf ≅ Rf ⋙ Rg) (κhg : Rhg ≅ Rg ⋙ Rh)
    (κh_gf : Rhgf ≅ Rgf ⋙ Rh) (κhg_f : Rhgf ≅ Rf ⋙ Rhg)
    (hκgf : ∀ M : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ℤ,
      ηgf.app M ≫ κgf.hom.app (DerivedCategory.Q.{w}.obj M) =
        ηg.app (((f.modules).mapHomologicalComplex (.up ℤ)).obj M) ≫
          Rg.map (ηf.app M))
    (hκhg : ∀ M : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)) ℤ,
      ηhg.app M ≫ κhg.hom.app (DerivedCategory.Q.{w}.obj M) =
        ηh.app (((g.modules).mapHomologicalComplex (.up ℤ)).obj M) ≫
          Rh.map (ηg.app M))
    (hκh_gf : ∀ M : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ℤ,
      ηhgf.app M ≫ κh_gf.hom.app (DerivedCategory.Q.{w}.obj M) =
        ηh.app (((f.modules ⋙ g.modules).mapHomologicalComplex (.up ℤ)).obj M) ≫
          Rh.map (ηgf.app M))
    (hκhg_f : ∀ M : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ℤ,
      ηhgf.app M ≫ κhg_f.hom.app (DerivedCategory.Q.{w}.obj M) =
        ηhg.app (((f.modules).mapHomologicalComplex (.up ℤ)).obj M) ≫
          Rhg.map (ηf.app M))
    : κh_gf.hom ≫ Functor.whiskerRight κgf.hom Rh ≫
        (Functor.associator Rf Rg Rh).hom =
      κhg_f.hom ≫ Functor.whiskerLeft Rf κhg.hom := by
  -- The normalization equations determine both composites by the universal property.
  apply Rhgf.rightDerived_ext ηhgf
    (HomologicalComplex.quasiIso _ (.up ℤ))
  apply NatTrans.ext
  funext M
  change ηhgf.app M ≫ (κh_gf.hom.app _ ≫
      Rh.map (κgf.hom.app _) ≫ 𝟙 _) =
    ηhgf.app M ≫ κhg_f.hom.app _ ≫ κhg.hom.app _
  rw [Category.comp_id, ← Category.assoc, hκh_gf M]
  have hgf := congrArg (fun a ↦ Rh.map a) (hκgf M)
  simp only [Functor.map_comp] at hgf
  rw [Category.assoc, hgf]
  conv_rhs => rw [← Category.assoc, hκhg_f M, Category.assoc]
  have hn := κhg.hom.naturality (ηf.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hn]
  conv_rhs => rw [← Category.assoc,
    hκhg ((f.modules.mapHomologicalComplex (.up ℤ)).obj M)]
  exact (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The normalized identity comparisons and both unit laws for derived direct image.
Source: Stacks Project, Cohomology on Sites, Tag 0D6E
(blueprint: lem-pur-ringed-derived-composition-cocycle).

Here the units eta0 and eta1 are written after the termwise identity direct-image
identification, so their source is exactly Q. The two kappa equations are the same
unit characterization as in `ringedToposDerivedPushforwardComposition`, after the
ordinary functor unitors. The epsilon equations specify the comparisons induced by
termwise identity direct image on every complex, including non-K-injectives.

Proof: for a resolution a:N→I, define epsilon at QN as the canonical resolution
identification followed by (Qa) inverse. The arbitrary-morphism formula of
lem-sf-kinjective-derived-map-computation proves naturality, and its transition formula
proves resolution independence. At K-injective I the identity resolution gives the
identity component. For the left unit law choose j:f_*I→J: the normalized kappa is
Qj and epsilon is (Qj) inverse, so they cancel. For the right unit law use I→I;
both factors are identities. Naturality transports both equalities to every derived
object. All resolutions are in their own coefficient categories, so no flatness or
isomorphism of the structural coefficient map is needed. -/
theorem ringedDerivedComposition_units
    {C0 : Type u} [SmallCategory C0]
    {C1 : Type u} [SmallCategory C1]
    (J0 : GrothendieckTopology C0) (A0 : Sheaf J0 CommRingCat.{u})
    (J1 : GrothendieckTopology C1) (A1 : Sheaf J1 CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1))]
    (f : RingedToposMorphism ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)
      ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1))
    (Rf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)))
    (R0 : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)))
    (R1 : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)))
    (ηf : (f.modules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rf)
    (η0 : DerivedCategory.Q.{w} (C := (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0))) ⟶
      DerivedCategory.Q.{w} ⋙ R0)
    (η1 : DerivedCategory.Q.{w} (C := (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1))) ⟶
      DerivedCategory.Q.{w} ⋙ R1)
    [Rf.IsRightDerivedFunctor ηf
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) (.up ℤ))]
    [R0.IsRightDerivedFunctor η0
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) (.up ℤ))]
    [R1.IsRightDerivedFunctor η1
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)) (.up ℤ))]
    (κleft : Rf ≅ Rf ⋙ R1) (κright : Rf ≅ R0 ⋙ Rf)
    (hκleft : ∀ M : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ℤ,
      ηf.app M ≫ κleft.hom.app (DerivedCategory.Q.{w}.obj M) =
        η1.app ((f.modules.mapHomologicalComplex (.up ℤ)).obj M) ≫ R1.map (ηf.app M))
    (hκright : ∀ M : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ℤ,
      ηf.app M ≫ κright.hom.app (DerivedCategory.Q.{w}.obj M) =
        ηf.app M ≫ Rf.map (η0.app M)) :
    ∃ (ε0 : R0 ≅ 𝟭 _) (ε1 : R1 ≅ 𝟭 _),
      (∀ M : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ℤ,
        η0.app M ≫ ε0.hom.app (DerivedCategory.Q.{w}.obj M) = 𝟙 _) ∧
      (∀ M : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)) ℤ,
        η1.app M ≫ ε1.hom.app (DerivedCategory.Q.{w}.obj M) = 𝟙 _) ∧
      κleft.hom ≫ Functor.whiskerLeft Rf ε1.hom ≫ (Functor.rightUnitor Rf).hom = 𝟙 Rf ∧
      κright.hom ≫ Functor.whiskerRight ε0.hom Rf ≫ (Functor.leftUnitor Rf).hom = 𝟙 Rf := by
  -- The identity derives the localization itself; compare it with each given representative.
  have identityComparison {C D : Type _} [Category C] [Category D]
      (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
      (R : D ⥤ D) (η : L ⟶ L ⋙ R) [R.IsRightDerivedFunctor η W] :
      ∃ ε : R ≅ 𝟭 D, ∀ M, η.app M ≫ ε.hom.app (L.obj M) = 𝟙 _ := by
    let : (𝟭 D).IsRightDerivedFunctor (Functor.rightUnitor L).inv W :=
      Functor.isRightDerivedFunctor_of_inverts W _ (Functor.rightUnitor L)
    let ε := R.rightDerivedUnique (𝟭 D) η (Functor.rightUnitor L).inv W
    refine ⟨ε, fun M ↦ ?_⟩
    simp [ε]
  obtain ⟨ε0, hε0⟩ := identityComparison DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) R0 η0
  obtain ⟨ε1, hε1⟩ := identityComparison DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) R1 η1
  refine ⟨ε0, ε1, hε0, hε1, ?_, ?_⟩
  · apply Rf.rightDerived_ext ηf (HomologicalComplex.quasiIso _ (.up ℤ))
    apply NatTrans.ext
    funext M
    change ηf.app M ≫ (κleft.hom.app _ ≫ ε1.hom.app _ ≫ 𝟙 _) = ηf.app M ≫ 𝟙 _
    rw [Category.comp_id, Category.comp_id, ← Category.assoc, hκleft M]
    have hn := ε1.hom.naturality (ηf.app M)
    dsimp only [Functor.id_map, Functor.comp_obj] at hn
    rw [Category.assoc, hn]
    change η1.app _ ≫ (ε1.hom.app _ ≫ ηf.app M) = ηf.app M
    rw [← Category.assoc, hε1, Category.id_comp]
  · apply Rf.rightDerived_ext ηf (HomologicalComplex.quasiIso _ (.up ℤ))
    apply NatTrans.ext
    funext M
    change ηf.app M ≫ (κright.hom.app _ ≫ Rf.map (ε0.hom.app _) ≫ 𝟙 _) =
      ηf.app M ≫ 𝟙 _
    rw [Category.comp_id, Category.comp_id, ← Category.assoc, hκright M]
    have hε := congrArg (fun a ↦ Rf.map a) (hε0 M)
    simp only [Functor.map_comp, Functor.map_id] at hε
    rw [Category.assoc, hε]
    exact Category.comp_id _

end CategoryTheory
