/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison

/-! # Counit transport through the ordinary/pro-etale coefficient comparisons

Source: latest blueprint, sk-lem-sp-reduction, defining counit identity.
(blueprint: lem-pur-finite-pro-coefficient-counit-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
end AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem inverseSiteNaturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {M N : DerivedCategoryModule A X}
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (hN : _root_.DerivedCategory.TStructure.t.plus N) (v : M ⟶ N) :
    (comparison A Y).map ((rightDerivedLowerShriek (ModuleCat A) f).map v) ≫
        compactSiteInverse A f N =
      compactSiteInverse A f M ≫ (proCompact A f).map ((comparison A X).map v) := by
  unfold compactSiteInverse
  rw [dif_pos hM, dif_pos hN]
  exact (ProEtale.compactSupportSiteComparison A
    (HasCompactification.compactification f)).inv.naturality
      (show (⟨M, hM⟩ : _root_.DerivedCategory.Plus _) ⟶ ⟨N, hN⟩ from
        ObjectProperty.homMk v)

private theorem compactCoefficientAtOrigin
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] (M : DerivedCategoryModule A X)
    (hM : DerivedCategory.boundedConstructibleFiniteTor A X M) :
    proCompactCoefficientMap φ f ((comparison A X).obj M) =
      (proScalar φ Y).map (compactSiteMap A f M) ≫
        (ProEtale.pbcComparisonReduction Y φ).hom.app
          ((rightDerivedLowerShriek (ModuleCat A) f).obj M) ≫
        (comparison B Y).map (ExceptionalCoefficients.compactSupportMap φ
          (HasCompactification.compactification f) M) ≫
        compactSiteInverse B f ((ordinaryScalar φ X).obj M) ≫
        (proCompact B f).map ((ProEtale.pbcComparisonReduction X φ).inv.app M) := by
  let adj := ProEtale.derivedComparisonAdjunction (ModuleCat A) X
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat A) X M hM.1.1.1
  have hi : IsIso (adj.counit.app ((comparison A X).obj M)) :=
    IsIso.of_isIso_fac_left (adj.left_triangle_components M)
  have hO := actualOriginCtf A X ((comparison A X).obj M) (comparisonCtf A X M hM)
  have hS : _root_.DerivedCategory.TStructure.t.plus ((ordinaryScalar φ X).obj M) :=
    ExceptionalCoefficients.scalar_extension_plus_of_finiteTor φ X M hM.2
  have hSO : _root_.DerivedCategory.TStructure.t.plus
      ((ordinaryScalar φ X).obj ((origin A X).obj ((comparison A X).obj M))) :=
    ExceptionalCoefficients.scalar_extension_plus_of_finiteTor φ X
      ((origin A X).obj ((comparison A X).obj M)) hO.2
  have hi' : originInverse A X ((comparison A X).obj M) =
      (comparison A X).map (adj.unit.app M) := by
    unfold originInverse
    rw [dif_pos hi]
    apply (cancel_mono (adj.counit.app ((comparison A X).obj M))).mp
    rw [IsIso.inv_hom_id]
    exact (adj.left_triangle_components M).symm
  have hnA := compactSiteNaturality A f hM.1.1.1 hO.1.1.1 (adj.unit.app M)
  have hnY := (ProEtale.pbcComparisonReduction Y φ).hom.naturality
    ((rightDerivedLowerShriek (ModuleCat A) f).map (adj.unit.app M))
  have hnB := inverseSiteNaturality B f hS hSO ((ordinaryScalar φ X).map (adj.unit.app M))
  have hnX := (ProEtale.pbcComparisonReduction X φ).inv.naturality (adj.unit.app M)
  dsimp only [Functor.comp_map] at hnY hnX
  change (proScalar φ Y).map
      ((comparison A Y).map ((rightDerivedLowerShriek (ModuleCat A) f).map
        (adj.unit.app M))) ≫ (ProEtale.pbcComparisonReduction Y φ).hom.app
          ((rightDerivedLowerShriek (ModuleCat A) f).obj
            ((origin A X).obj ((comparison A X).obj M))) =
    (ProEtale.pbcComparisonReduction Y φ).hom.app
        ((rightDerivedLowerShriek (ModuleCat A) f).obj M) ≫
      (comparison B Y).map ((ordinaryScalar φ Y).map
        ((rightDerivedLowerShriek (ModuleCat A) f).map (adj.unit.app M))) at hnY
  have hnOrd' : (ordinaryScalar φ Y).map
      ((rightDerivedLowerShriek (ModuleCat A) f).map (adj.unit.app M)) ≫
        ExceptionalCoefficients.compactSupportMap φ
          (HasCompactification.compactification f)
          ((origin A X).obj ((comparison A X).obj M)) =
    ExceptionalCoefficients.compactSupportMap φ (HasCompactification.compactification f) M ≫
      (rightDerivedLowerShriek (ModuleCat B) f).map
        ((ordinaryScalar φ X).map (adj.unit.app M)) := by
    exact compactScalarMap_naturality φ (HasCompactification.compactification f)
      (adj.unit.app M)
  have hnOrd'' := congrArg (comparison B Y).map hnOrd'
  simp only [Functor.map_comp] at hnOrd''
  change (comparison B X).map ((ordinaryScalar φ X).map (adj.unit.app M)) ≫
      (ProEtale.pbcComparisonReduction X φ).inv.app
        ((origin A X).obj ((comparison A X).obj M)) =
    (ProEtale.pbcComparisonReduction X φ).inv.app M ≫
      (proScalar φ X).map ((comparison A X).map (adj.unit.app M)) at hnX
  have ht : (comparison A X).map (adj.unit.app M) ≫
      adj.counit.app ((comparison A X).obj M) = 𝟙 _ := adj.left_triangle_components M
  have ht' := congrArg (fun t ↦ (proCompact B f).map ((proScalar φ X).map t)) ht
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id] at ht'
  unfold proCompactCoefficientMap
  rw [hi', hnA]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnY, reassoc_of% hnOrd'', reassoc_of% hnB]
  rw [← (proCompact B f).map_comp_assoc, hnX]
  simp only [Functor.map_comp, Category.assoc]
  erw [ht', Category.comp_id]

private theorem coefficientCounitAtOrigin
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : proCategory A Y)
    (hG : DerivedCategory.boundedConstructibleFiniteTor A X
      ((rightDerivedUpperShriek A f).obj ((origin A Y).obj K)))
    (hGB : _root_.DerivedCategory.TStructure.t.plus
      ((rightDerivedUpperShriek B f).obj
        ((origin B Y).obj ((proScalar φ Y).obj K)))) :
    (proCompact B f).map ((ProEtale.pbcComparisonReduction X φ).inv.app
        ((rightDerivedUpperShriek A f).obj ((origin A Y).obj K))) ≫
        (proCompact B f).map (proCoefficientMap φ f K) ≫
        proCounit B f ((proScalar φ Y).obj K) =
      compactSiteMap B f ((ordinaryScalar φ X).obj
        ((rightDerivedUpperShriek A f).obj ((origin A Y).obj K))) ≫
        (comparison B Y).map
          ((rightDerivedLowerShriek (ModuleCat B) f).map
              (ExceptionalCoefficients.mateMap φ f ((origin A Y).obj K)) ≫
            (rightDerivedUpperShriekAdjunction B f).counit.app
              ((ordinaryScalar φ Y).obj ((origin A Y).obj K))) ≫
        (ProEtale.pbcComparisonReduction Y φ).inv.app ((origin A Y).obj K) ≫
        (proScalar φ Y).map
          ((ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.app K) := by
  let J := (origin A Y).obj K
  let M := (rightDerivedUpperShriek A f).obj J
  let adj := ProEtale.derivedComparisonAdjunction (ModuleCat B) Y
  let e := (ProEtale.pbcComparisonReduction Y φ).inv.app J ≫
    (proScalar φ Y).map
      ((ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.app K)
  let g := ExceptionalCoefficients.mateMap φ f J
  have hr : originReductionMap φ Y K =
      adj.unit.app ((ordinaryScalar φ Y).obj J) ≫ (origin B Y).map e := by
    exact Adjunction.homEquiv_unit _ _ _ _
  have hS := ExceptionalCoefficients.scalar_extension_plus_of_finiteTor φ X M hG.2
  have hn := compactSiteNaturality B f hS hGB
    (g ≫ (rightDerivedUpperShriek B f).map
      (originReductionMap φ Y K))
  have h := transportedTrace (rightDerivedLowerShriek (ModuleCat B) f)
    (rightDerivedUpperShriek B f)
    (rightDerivedUpperShriekAdjunction B f)
    (comparison B Y) (comparison B X) (origin B Y) adj (proCompact B f)
    ((ordinaryScalar φ Y).obj J) ((proScalar φ Y).obj K) e
    ((ordinaryScalar φ X).obj M) g _ _ (by simpa only [← hr] using hn)
  simp only [proCoefficientMap, proCounit, Functor.map_comp, Category.assoc]
  rw [← (proCompact B f).map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← hr] at h
  simp only [Functor.map_comp, Category.assoc, e, J, M, g, adj] at h
  exact h

/-- The transported exceptional coefficient map has the transported counit identity.
No smoothness, orientation or invertibility of the exceptional map is assumed.
Source: latest blueprint, sk-lem-sp-reduction.proof.md, definition of c by its
counit transpose, and sk-lem-sp-reduction-compatibilities.proof.md (1).
(blueprint: lem-pur-finite-pro-coefficient-counit-transport).

Proof: put J=Rnu_*K and M=f_A^times J. The ordinary coefficient mate is, by
definition, the transpose of inverse compact comparison followed by the A-counit.
The finite-Tor hypothesis on M puts all its scalar extensions in the bounded-below
site-comparison domain. The supplied bounded-below hypothesis on the B-exceptional
origin puts its compact site map on that same locus. On K and nu_X^*M the
actual comparison counits are
isomorphisms. Their triangle identities identify inverse origin counits with the
comparison images of the ordinary units. Expand proCompactCoefficientMap at
nu_X^*M; naturality of the compact site comparison moves these units next to the
origin counits, where they cancel. The resulting comparison is scalar extension
of the A-site comparison, the site/scalar mate, ordinary compact comparison,
inverse B-site comparison, and compact image of the inverse X-site/scalar mate.
It is invertible. Expand proCoefficientMap and proCounit. Naturality of the
B-site comparison and exceptional counit moves originReductionMap to the last
factor. Its defining adjunction identity replaces comparison of that map followed
by the B-origin counit with inverse site/scalar comparison followed by scalar
extension of the A-origin counit. Substitute the ordinary coefficient mate's counit
identity. The site/scalar comparison is natural in the ordinary A-counit, so the
remaining factors coincide. Cancel the invertible compact comparison to obtain
the displayed equality with its specified total inverse. No purity map is used. -/
theorem finiteProCoefficientCounitTransport
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f]
    (K : proCategory A Y) (_hK : IsCtf A Y K)
    (hG : DerivedCategory.boundedConstructibleFiniteTor A X
      ((rightDerivedUpperShriek A f).obj ((origin A Y).obj K)))
    (hGB : _root_.DerivedCategory.TStructure.t.plus
      ((rightDerivedUpperShriek B f).obj
        ((origin B Y).obj ((proScalar φ Y).obj K)))) :
    (proCompact B f).map (proCoefficientMap φ f K) ≫
        proCounit B f ((proScalar φ Y).obj K) =
      proCompactCoefficientInverse φ f ((exceptional A f).obj K) ≫
        (proScalar φ Y).map (proCounit A f K) := by
  classical
  let J := (origin A Y).obj K
  let M := (rightDerivedUpperShriek A f).obj J
  have hp : _root_.DerivedCategory.TStructure.t.plus ((ordinaryScalar φ X).obj M) :=
    ExceptionalCoefficients.scalar_extension_plus_of_finiteTor φ X M hG.2
  have ha : IsIso (compactSiteMap A f M) := by
    unfold compactSiteMap
    rw [dif_pos hG.1.1.1]
    infer_instance
  have hb : IsIso (compactSiteInverse B f ((ordinaryScalar φ X).obj M)) := by
    unfold compactSiteInverse
    rw [dif_pos hp]
    infer_instance
  have hcompact : IsIso (proCompactCoefficientMap φ f ((comparison A X).obj M)) := by
    rw [compactCoefficientAtOrigin φ f M hG]
    have := ExceptionalCoefficients.compactSupport_isIso φ
      (HasCompactification.compactification f) M
    infer_instance
  have hsite : compactSiteInverse B f ((ordinaryScalar φ X).obj M) ≫
      compactSiteMap B f ((ordinaryScalar φ X).obj M) = 𝟙 _ := by
    unfold compactSiteInverse compactSiteMap
    rw [dif_pos hp, dif_pos hp]
    exact Iso.inv_hom_id_app _ _
  have hmate : (rightDerivedLowerShriek (ModuleCat B) f).map
        (ExceptionalCoefficients.mateMap φ f J) ≫
      (rightDerivedUpperShriekAdjunction B f).counit.app
        ((ordinaryScalar φ Y).obj J) =
      ExceptionalCoefficients.comparisonInverse φ
          (HasCompactification.compactification f) M ≫
        (ordinaryScalar φ Y).map
          ((rightDerivedUpperShriekAdjunction A f).counit.app J) := by
    unfold ExceptionalCoefficients.mateMap
    exact ((rightDerivedUpperShriekAdjunction B f).homEquiv _ _).symm_apply_apply _
  have hord : ExceptionalCoefficients.compactSupportMap φ
        (HasCompactification.compactification f) M ≫
      ExceptionalCoefficients.comparisonInverse φ
        (HasCompactification.compactification f) M = 𝟙 _ := by
    have := ExceptionalCoefficients.compactSupport_isIso φ
      (HasCompactification.compactification f) M
    unfold ExceptionalCoefficients.comparisonInverse
    rw [dif_pos this]
    exact IsIso.hom_inv_id _
  have hn := (ProEtale.pbcComparisonReduction Y φ).hom.naturality
    ((rightDerivedUpperShriekAdjunction A f).counit.app J)
  change (proScalar φ Y).map ((comparison A Y).map
      ((rightDerivedUpperShriekAdjunction A f).counit.app J)) ≫
        (ProEtale.pbcComparisonReduction Y φ).hom.app J =
    (ProEtale.pbcComparisonReduction Y φ).hom.app
        ((rightDerivedLowerShriek (ModuleCat A) f).obj M) ≫
      (comparison B Y).map ((ordinaryScalar φ Y).map
        ((rightDerivedUpperShriekAdjunction A f).counit.app J)) at hn
  change _ = proCompactCoefficientInverse φ f ((comparison A X).obj M) ≫ _
  unfold proCompactCoefficientInverse
  rw [dif_pos hcompact]
  apply (cancel_epi (proCompactCoefficientMap φ f ((comparison A X).obj M))).mp
  simp only [IsIso.hom_inv_id_assoc]
  rw [compactCoefficientAtOrigin φ f M hG]
  simp only [Category.assoc]
  rw [coefficientCounitAtOrigin φ f K hG hGB]
  rw [reassoc_of% hsite, hmate]
  simp only [Functor.map_comp, Category.assoc]
  erw [← (comparison B Y).map_comp_assoc, hord,
    (comparison B Y).map_id, Category.id_comp]
  erw [← reassoc_of% hn]
  simp only [Iso.hom_inv_id_app_assoc, proCounit, Functor.map_comp, J, M]

end AlgebraicGeometry.Etale.FiniteSmoothPurity
