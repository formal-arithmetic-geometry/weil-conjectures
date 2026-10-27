/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Counit normalization of the site-transported closed adjoint

Source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/
lem-coef-finite-dualizing.md, closed-immersion calculation (*); the normalized Hom chain in
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-existence/
thm-sf-ambient-adjoint-class.proof.md
(blueprint: lem-coef-site-closed-counit-transport).

We retain the identity-open compactification in the notation. Its ordinary adjunction is
identified with the closed direct-image adjunction by the canonical identity-open
normalization, and the inverse compact-support comparison is the direct-image mate delta.
Thus the formula below is (*) with these canonical identifications displayed by the
compactification interface, rather than a separately chosen Hom equivalence.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem inclusion_comp_inv
    {B C D : Type*} [Category* B] [Category* C] [Category* D]
    [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    (V : B ⥤ C) (W : C ⥤ D) [V.Additive] [W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (K : DerivedCategory.Plus B) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso V W).inv.app K) =
      (Functor.mapDerivedCategoryCompIso V W).inv.app K.obj := by
  exact congrArg Iso.inv (show DerivedCategory.Plus.ι.mapIso
    ((Functor.mapDerivedCategoryPlusCompIso V W).app K) =
    (Functor.mapDerivedCategoryCompIso V W).app K.obj from
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app V W K))

set_option maxHeartbeats 600000 in
-- Keep the large comparison composites folded while matching their components.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor in
private theorem compact_comparison_eq (R : Type (u + 1)) [CommRing R] [Finite R]
    {Z P : Scheme.{u}} {f : Z ⟶ P} (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (fixedCompactSupportComparisonIso R c).hom.app L =
      (compactSupportSiteComparison R c).hom.app L := by
  let A := ModuleCat.{u + 1} R
  simp only [fixedCompactSupportComparisonIso,
    compactSupportSiteComparison, compactSupportSiteComparisonPlus,
    fixedDirectImageComparisonIso,
    Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    Functor.mapDerivedCategoryPlusCompatibility,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Functor.map_comp,
    CategoryTheory.Functor.map_id, Category.assoc]
  simp only [Functor.comp_map]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj]
  simp only [Category.id_comp, Category.comp_id]
  have ho : DerivedCategory.Plus.ι.map
      ((properOpenSiteExtensionIso R c.i).inv.app L) =
      ((Functor.mapDerivedCategoryCompIso
            (Etale.openImmersionLowerShriek A c.i) (comparisonUpperStar A c.Z)).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComparisonUpperStarIso A c.i) ≪≫
        Functor.mapDerivedCategoryCompIso (comparisonUpperStar A Z)
          (openImmersionLowerShriek A c.i)).inv.app L.obj := by
    have hh : DerivedCategory.Plus.ι.mapIso
        ((properOpenSiteExtensionIso R c.i).app L) =
        ((Functor.mapDerivedCategoryCompIso
            (Etale.openImmersionLowerShriek A c.i) (comparisonUpperStar A c.Z)).symm ≪≫
          Functor.mapDerivedCategoryNatIso
            (openImmersionLowerShriekComparisonUpperStarIso A c.i) ≪≫
          Functor.mapDerivedCategoryCompIso (comparisonUpperStar A Z)
            (openImmersionLowerShriek A c.i)).app L.obj := by
      apply Iso.ext
      simp only [properOpenSiteExtensionIso, Iso.app_hom, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app, Functor.mapIso_hom, Functor.map_comp,
        Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
        Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, inclusion_comp_inv]
      rfl
    exact congrArg Iso.inv hh
  have hn := (lowerStar A c.g).rightDerivedFunctorPlusCompatibility.inv.naturality
    ((properOpenSiteExtensionIso R c.i).inv.app L)
  simp only [Functor.comp_map] at hn
  rw [ho] at hn
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.map_comp, Category.assoc] at hn
  rw [Functor.mapDerivedCategoryNatIso_symm]
  have := isIso_fixedComparisonDirectImageMatePlus R c.g
  let tail := DerivedCategory.Plus.ι.map
      ((asIso (fixedComparisonDirectImageMatePlus R c.g)).inv.app
        ((Etale.openImmersionLowerShriek A c.i).mapDerivedCategoryPlus.obj L)) ≫
    (comparisonUpperStar A P).mapDerivedCategory.map
      ((Etale.lowerStar A c.g).rightDerivedFunctorPlusCompatibility.hom.app
        ((Etale.openImmersionLowerShriek A c.i).mapDerivedCategoryPlus.obj L))
  erw [Category.id_comp, Category.id_comp]
  simpa only [tail, A, Functor.comp_obj, ObjectProperty.ι_obj, Category.assoc] using
    congrArg (fun t ↦ t ≫ tail) hn

/-- The specified comparison-class adjunction transports the closed counit, and its
adjunct of a transported ordinary morphism is the transported ordinary adjunct.
Source: blueprint lem-coef-finite-dualizing.md, closed-immersion equation (*), and
thm-sf-ambient-adjoint-class.proof.md, displayed normalized Hom chain
(blueprint: lem-coef-site-closed-counit-transport).

Proof: put F = Ri_! for the identity-open compactification, identified canonically with
Ri_*. Its compact-support comparison is delta inverse. By homEquiv_normalized, the
bijection at the identity-open compactification sends g to S_Z beta(eta_F ≫ U_P(g delta)).
For g = delta inverse ≫ S_P(f), unit naturality gives eta_F ≫ U_P(S_P(f)) = f ≫ eta_H.
Target naturality of the ordinary adjunction then gives beta(f ≫ eta_H) =
beta(f) ≫ G(eta_H). Applying S_Z proves the second clause. The isomorphism eta_H
makes G(eta_H) an isomorphism; therefore J S_P H is bounded below of etale origin,
with representative G H and isomorphism alpha. The relative counit E is defined by
C.homEquiv inverse of the identity. Source naturality gives the transpose of
F_pro(alpha) ≫ E as alpha. Specialize the general formula to f = the ordinary counit,
whose transpose is the identity. Injectivity of C.homEquiv and cancellation of delta
inverse give the first clause. This uses only bounded-below H and G H; constructibility
is never used. -/
theorem siteClosedCounitTransport
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (n : ℕ) (_hn : 1 ≤ n)
    [Finite (Padic.coefficientExtensionRing l E n)]
    {Z P : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of D.k)) (aP : P ⟶ Spec (.of D.k))
    [IsSeparated aZ] [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [IsSeparated aP] [LocallyOfFiniteType aP] [QuasiCompact aP]
    (i : Z ⟶ P) [IsClosedImmersion i] (_hi : i ≫ aP = aZ) :
    let Λ := Padic.coefficientExtensionRing l E n
    let A := ModuleCat.{u + 1} Λ
    let c₀ := Compactification.ofIsProper i
    let S := fun T : Scheme.{u} ↦ (comparisonUpperStar A T).mapDerivedCategory
    let U := fun T : Scheme.{u} ↦ (comparisonLowerStar A T).rightDerivedFunctor
    let F := Etale.rightDerivedLowerShriekOfCompactification A c₀
    let Fpro := rightDerivedLowerShriekOfCompactification A c₀
    ∀ (G : _root_.DerivedCategory (Sheaf P.smallEtaleTopology A) ⥤
          _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
      (adj : F ⊣ G)
      (C : ComparisonClassAdjunction Λ i c₀ G adj
        (DerivedCategory.plusEtaleOrigin A Z) _root_.DerivedCategory.TStructure.t.plus)
      (H : DerivedCategory.Plus (Sheaf P.smallEtaleTopology A))
      (hIH : _root_.DerivedCategory.TStructure.t.plus (G.obj H.obj)),
    let J := U P ⋙ G ⋙ S Z
    let α := (S Z).map (G.map ((derivedComparisonAdjunction A P).unit.app H.obj))
    let δ := fun L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ↦
      ((compactSupportSiteComparison Λ c₀).app L).symm
    IsIso α ∧
    ∃ hJ : DerivedCategory.plusEtaleOrigin A Z (J.obj ((S P).obj H.obj)),
      let E := (C.homEquiv c₀ _ hJ _
        (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj H.property).plus).symm
          (𝟙 (J.obj ((S P).obj H.obj)))
      (δ ⟨G.obj H.obj, hIH⟩).hom ≫ Fpro.map α ≫ E =
        (S P).map (adj.counit.app H.obj) ∧
      ∀ (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A))
        (f : F.obj L.obj ⟶ H.obj),
        C.homEquiv c₀ _
            (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property) _
            (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj H.property).plus
            ((δ L).inv ≫ (S P).map f) =
          (S Z).map (adj.homEquiv L.obj H.obj f) ≫ α := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
    intro Λ A c₀ S U F Fpro G adj C H hIH
    let J := U P ⋙ G ⋙ S Z
    let α := (S Z).map (G.map ((derivedComparisonAdjunction A P).unit.app H.obj))
    let δ := fun L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ↦
      ((compactSupportSiteComparison Λ c₀).app L).symm
    have hunit := isIso_derivedComparisonAdjunction_unit_app A P H.obj H.property
    have hα : IsIso α := by dsimp only [α]; infer_instance
    have hJ : DerivedCategory.plusEtaleOrigin A Z (J.obj ((S P).obj H.obj)) :=
      (DerivedCategory.plusEtaleOrigin A Z).prop_of_iso (asIso α)
        (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hIH)
    have hcompat (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A)) :
        (fixedCompactSupportComparisonIso Λ c₀).hom.app L = (δ L).inv :=
      compact_comparison_eq Λ c₀ L
    have hformula (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A))
        (f : F.obj L.obj ⟶ H.obj) :
        C.homEquiv c₀ _
            (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property) _
            (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj H.property).plus
            ((δ L).inv ≫ (S P).map f) =
          (S Z).map (adj.homEquiv L.obj H.obj f) ≫ α := by
      have h := C.homEquiv_normalized L
        (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property) _
        (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj H.property).plus
        ((derivedComparisonAdjunction A P).homEquiv _ _ ((S P).map f))
      erw [Equiv.symm_apply_apply, hcompat] at h
      have heta : (derivedComparisonAdjunction A P).homEquiv _ _ ((S P).map f) =
          f ≫ (derivedComparisonAdjunction A P).unit.app H.obj := by
        change (derivedComparisonAdjunction A P).unit.app (F.obj L.obj) ≫
          (U P).map ((S P).map f) = _
        exact ((derivedComparisonAdjunction A P).unit.naturality f).symm
      rw [heta, adj.homEquiv_naturality_right, (S Z).map_comp] at h
      exact h
    refine ⟨hα, hJ, ?_, hformula⟩
    let E := (C.homEquiv c₀ _ hJ _
      (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj H.property).plus).symm
        (𝟙 (J.obj ((S P).obj H.obj)))
    have he : C.homEquiv c₀ _
        (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hIH) _
        (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj H.property).plus
        (Fpro.map α ≫ E) = α := by
      simpa only [E, Equiv.apply_symm_apply, Category.comp_id] using
        C.naturality_left c₀ _ _
          (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hIH) hJ _
          (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj H.property).plus α E
    have hc := hformula ⟨G.obj H.obj, hIH⟩ (adj.counit.app H.obj)
    have hcounit : adj.homEquiv (G.obj H.obj) H.obj (adj.counit.app H.obj) = 𝟙 _ := by
      rw [← adj.homEquiv_symm_id, Equiv.apply_symm_apply]
    rw [hcounit, CategoryTheory.Functor.map_id, Category.id_comp] at hc
    have heq := (C.homEquiv c₀ _
      (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hIH) _
      (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj H.property).plus).injective
        (he.trans hc.symm)
    change (δ ⟨G.obj H.obj, hIH⟩).hom ≫ Fpro.map α ≫ E = _
    rw [heq]
    simp only [Iso.hom_inv_id_assoc]

end AlgebraicGeometry.ProEtale
