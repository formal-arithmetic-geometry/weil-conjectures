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

-- Both constructions use the same proper mate. Restriction of the three exact
-- open-extension factors and naturality of the right-derived inclusion comparison
-- identify their components.
private theorem compactSupportComparison_eq (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    fixedCompactSupportComparisonIso Λ c = compactSupportSiteComparison Λ c := by
  apply Iso.ext
  apply NatTrans.ext
  funext L
  let A := ModuleCat.{u + 1} Λ
  let N := comparisonUpperStar A X
  let M := comparisonUpperStar A c.Z
  let J := openImmersionLowerShriek A c.i
  let I := Etale.openImmersionLowerShriek A c.i
  let R := lowerStar A c.g
  let a := (Functor.mapDerivedCategoryPlusCompIso N J).inv.app L
  let b := (Functor.mapDerivedCategoryPlusNatIso
    (openImmersionLowerShriekComparisonUpperStarIso A c.i)).inv.app L
  let d := (Functor.mapDerivedCategoryPlusCompIso I M).hom.app L
  have ha : DerivedCategory.Plus.ι.map a =
      (Functor.mapDerivedCategoryCompIso N J).inv.app L.obj := by
    have h : DerivedCategory.Plus.ι.mapIso
        ((Functor.mapDerivedCategoryPlusCompIso N J).app L) =
        (Functor.mapDerivedCategoryCompIso N J).app L.obj :=
      Iso.ext (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app N J L)
    exact congrArg Iso.inv h
  have hb : DerivedCategory.Plus.ι.map b =
      (Functor.mapDerivedCategoryNatIso
        (openImmersionLowerShriekComparisonUpperStarIso A c.i)).inv.app L.obj := by
    have h : DerivedCategory.Plus.ι.mapIso
        ((Functor.mapDerivedCategoryPlusNatIso
          (openImmersionLowerShriekComparisonUpperStarIso A c.i)).app L) =
        (Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComparisonUpperStarIso A c.i)).app L.obj :=
      Iso.ext (Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app _ L)
    exact congrArg Iso.inv h
  have hd : DerivedCategory.Plus.ι.map d =
      (Functor.mapDerivedCategoryCompIso I M).hom.app L.obj :=
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app I M L
  dsimp only [fixedCompactSupportComparisonIso, compactSupportSiteComparison,
    compactSupportSiteComparisonPlus, fixedDirectImageComparisonIso,
    properOpenSiteExtensionIso, rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.mapDerivedCategoryPlusCompatibility]
  simp only [Functor.map_comp, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Category.assoc, CategoryTheory.Functor.comp_map]
  dsimp only [Functor.mapDerivedCategoryPlus, ObjectProperty.lift,
    Functor.comp_obj, ObjectProperty.ι_obj]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rw [Functor.mapDerivedCategoryNatIso_symm, ← ha, ← hb, ← hd]
  have hn := R.rightDerivedFunctorPlusCompatibility.inv.naturality (a ≫ b ≫ d)
  simp only [Functor.map_comp, Category.assoc] at hn
  erw [reassoc_of% hn]
  rfl

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
  dsimp only
  intro G adj C H hIH
  let Λ := Padic.coefficientExtensionRing l E n
  let A := ModuleCat.{u + 1} Λ
  let S := fun T : Scheme.{u} ↦ (comparisonUpperStar A T).mapDerivedCategory
  let U := fun T : Scheme.{u} ↦ (comparisonLowerStar A T).rightDerivedFunctor
  let c₀ := Compactification.ofIsProper i
  let F := Etale.rightDerivedLowerShriekOfCompactification A c₀
  let Fpro := rightDerivedLowerShriekOfCompactification A c₀
  let J := U P ⋙ G ⋙ S Z
  let α := (S Z).map (G.map ((derivedComparisonAdjunction A P).unit.app H.obj))
  let δ := fun L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ↦
    ((compactSupportSiteComparison Λ c₀).app L).symm
  change IsIso α ∧ ∃ hJ : DerivedCategory.plusEtaleOrigin A Z
    (J.obj ((S P).obj H.obj)), _
  have hcomp : fixedCompactSupportComparisonIso Λ c₀ =
      compactSupportSiteComparison Λ c₀ := compactSupportComparison_eq Λ c₀
  have : IsIso ((derivedComparisonAdjunction A P).unit.app H.obj) :=
    isIso_derivedComparisonAdjunction_unit_app A P H.obj H.property
  have : IsIso α := by dsimp [α]; infer_instance
  refine ⟨inferInstance, ?_⟩
  have hJ : DerivedCategory.plusEtaleOrigin A Z (J.obj ((S P).obj H.obj)) :=
    (DerivedCategory.plusEtaleOrigin A Z).prop_of_iso (asIso α)
      (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hIH)
  refine ⟨hJ, ?_⟩
  let hH := (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj H.property).plus
  let ε := (C.homEquiv c₀ _ hJ _ hH).symm (𝟙 (J.obj ((S P).obj H.obj)))
  change (δ ⟨G.obj H.obj, hIH⟩).hom ≫ Fpro.map α ≫ ε =
    (S P).map (adj.counit.app H.obj) ∧ _
  have hformula (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A))
      (f : F.obj L.obj ⟶ H.obj) :
      C.homEquiv c₀ _
          (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property) _ hH
          ((δ L).inv ≫ (S P).map f) =
        (S Z).map (adj.homEquiv L.obj H.obj f) ≫ α := by
    have heq : ((derivedComparisonAdjunction A P).homEquiv _ _).symm
        (f ≫ (derivedComparisonAdjunction A P).unit.app H.obj) = (S P).map f := by
      apply ((derivedComparisonAdjunction A P).homEquiv _ _).injective
      simp only [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
      simpa only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] using
        (derivedComparisonAdjunction A P).unit.naturality f
    have h := C.homEquiv_normalized L
      (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property) _ hH
      (f ≫ (derivedComparisonAdjunction A P).unit.app H.obj)
    change C.homEquiv c₀ _ _ _ hH
      ((fixedCompactSupportComparisonIso Λ c₀).hom.app L ≫
        ((derivedComparisonAdjunction A P).homEquiv _ _).symm
          (f ≫ (derivedComparisonAdjunction A P).unit.app H.obj)) = _ at h
    erw [heq] at h
    rw [hcomp] at h
    change C.homEquiv c₀ _ _ _ hH ((δ L).inv ≫ (S P).map f) = _ at h
    refine h.trans ?_
    rw [adj.homEquiv_naturality_right, CategoryTheory.Functor.map_comp]
  refine ⟨?_, hformula⟩
  have hnat := C.naturality_left c₀ _ _
    (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hIH) hJ _ hH α ε
  have hcounit : C.homEquiv c₀ _
      (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hIH) _ hH
      (Fpro.map α ≫ ε) = α := by
    simpa only [ε, Equiv.apply_symm_apply, Category.comp_id] using hnat
  have hordinary := hformula ⟨G.obj H.obj, hIH⟩ (adj.counit.app H.obj)
  have heq : Fpro.map α ≫ ε =
      (δ ⟨G.obj H.obj, hIH⟩).inv ≫ (S P).map (adj.counit.app H.obj) := by
    apply (C.homEquiv c₀ _
      (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hIH) _ hH).injective
    rw [hcounit, hordinary]
    rw [← adj.homEquiv_symm_id, Equiv.apply_symm_apply,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [heq, Iso.hom_inv_id_assoc]

end AlgebraicGeometry.ProEtale
