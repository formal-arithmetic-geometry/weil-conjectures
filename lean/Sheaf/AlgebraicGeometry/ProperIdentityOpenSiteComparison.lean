/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q143
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Proper identity-open site comparison

Source: Stacks Project, Tags 09AF and 099R; blueprint
`thm-sf-ambient-adjoint-class.proof.md`, compact-support factor
(blueprint: lem-coef-proper-identity-open-site-comparison).

The identifications below remove identity extension by zero using its canonical
adjunction identification, descended termwise. No direct-image comparison is chosen:
the inverse on the right is that of the recorded counit mate.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

open CategoryTheory.Limits

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma derive_identity_square
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (S : C ⥤ D) (E : C ⥤ C) (P : D ⥤ D)
    [S.Additive] [E.Additive] [P.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (o : E ⋙ S ≅ S ⋙ P) (e : E ≅ 𝟭 C) (p : P ≅ 𝟭 D)
    (h : o ≪≫ Functor.isoWhiskerLeft S p = Functor.isoWhiskerRight e S) :
    ((Functor.mapDerivedCategoryPlusCompIso E S).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso o ≪≫
      Functor.mapDerivedCategoryPlusCompIso S P).hom ≫
        Functor.whiskerLeft S.mapDerivedCategoryPlus
          (Functor.mapDerivedCategoryPlusNatIso p ≪≫
            Functor.mapDerivedCategoryPlusIdIso D).hom =
      Functor.whiskerRight (Functor.mapDerivedCategoryPlusNatIso e ≪≫
        Functor.mapDerivedCategoryPlusIdIso C).hom S.mapDerivedCategoryPlus := by
  have hd := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso z).hom) h
  rw [Functor.mapDerivedCategoryNatIso_trans] at hd
  have hu :
      (Functor.mapDerivedCategoryCompIso E S).inv ≫
        (Functor.mapDerivedCategoryNatIso o).hom ≫
        (Functor.mapDerivedCategoryCompIso S P).hom ≫
        Functor.whiskerLeft S.mapDerivedCategory
          (Functor.mapDerivedCategoryNatIso p).hom ≫
        Functor.whiskerLeft S.mapDerivedCategory
          (Functor.mapDerivedCategoryIdIso D).hom =
      Functor.whiskerRight (Functor.mapDerivedCategoryNatIso e).hom S.mapDerivedCategory ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryIdIso C).hom
          S.mapDerivedCategory := by
    rw [← cancel_epi (Functor.mapDerivedCategoryCompIso E S).hom]
    simp only [Iso.hom_inv_id_assoc]
    rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft S p),
      Functor.mapDerivedCategoryCompIso_comp_id S]
    rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e S),
      Functor.mapDerivedCategoryCompIso_id_comp S]
    simpa only [Category.assoc] using congrArg (· ≫ 𝟙 S.mapDerivedCategory) hd
  have hi (L : DerivedCategory.Plus C) :
      DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso E S).inv.app L) =
        (Functor.mapDerivedCategoryCompIso E S).inv.app L.obj := by
    apply (cancel_mono ((Functor.mapDerivedCategoryCompIso E S).hom.app L.obj)).mp
    erw [← Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app E S L,
      ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, Iso.inv_hom_id_app]
    rfl
  have hm {M N : DerivedCategory.Plus C} (g : M ⟶ N) :
      DerivedCategory.Plus.ι.map (S.mapDerivedCategoryPlus.map g) =
        S.mapDerivedCategory.map (DerivedCategory.Plus.ι.map g) := rfl
  ext L : 2
  apply DerivedCategory.Plus.ι.map_injective
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, Iso.symm_hom, Functor.map_comp, hi, hm,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusIdIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, Category.assoc]
  exact NatTrans.congr_app hu L.obj

private lemma adjoint_identity_iso {C : Type*} [Category C]
    {F G : C ⥤ C} (a : F ⊣ G) (e : G ≅ 𝟭 C) :
    a.leftAdjointUniq (Adjunction.id.ofNatIsoRight e.symm) = a.leftAdjointIdIso e := by
  apply Iso.ext
  ext M : 2
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointIdIso,
    conjugateIsoEquiv, conjugateEquiv, Adjunction.ofNatIsoRight]

namespace AlgebraicGeometry.ProEtale

/-- Termwise descent of the etale identity-extension identification.
Source: Stacks Tags 09AF and 05RU
(blueprint: lem-coef-proper-identity-open-site-comparison). -/
def identityOpenEtaleDerivedIso (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) (𝟙 X)).mapDerivedCategoryPlus ≅
      𝟭 _ :=
  Functor.mapDerivedCategoryPlusNatIso (Etale.openImmersionLowerShriekId (ModuleCat.{u + 1} A) X) ≪≫
    Functor.mapDerivedCategoryPlusIdIso _

/-- Termwise descent of the pro-etale identity-extension identification.
Source: Stacks Tags 09AF and 05RU
(blueprint: lem-coef-proper-identity-open-site-comparison). -/
def identityOpenProEtaleDerivedIso (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) (𝟙 X)).mapDerivedCategoryPlus ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryPlusNatIso (openImmersionLowerShriekIdIso (ModuleCat.{u + 1} A) X) ≪≫
    Functor.mapDerivedCategoryPlusIdIso _

/-- The canonical e: compact support at (id,f) to etale direct image.
Source: blueprint compact-support factor; Stacks Tag 09AF
(blueprint: lem-coef-proper-identity-open-site-comparison). -/
def properIdentityOpenEtaleIso (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper f) ≅
      Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) f :=
  Functor.isoWhiskerRight (identityOpenEtaleDerivedIso A X) _ ≪≫ Functor.leftUnitor _

/-- The canonical q: compact support at (id,f) to pro-etale direct image.
Source: blueprint compact-support factor; Stacks Tag 09AF
(blueprint: lem-coef-proper-identity-open-site-comparison). -/
def properIdentityOpenProEtaleIso (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper f) ≅
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus :=
  Functor.isoWhiskerRight (identityOpenProEtaleDerivedIso A X) _ ≪≫ Functor.leftUnitor _

/-- The isomorphism whose forward map is the specified ordinary counit mate.
Source: Stacks Tags 099R and 0B65
(blueprint: lem-coef-proper-identity-open-site-comparison). -/
def properIdentityOpenMateIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) f ⋙
        siteComparisonDerivedPullbackPlus Y A ≅
      siteComparisonDerivedPullbackPlus X A ⋙
        (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus :=
  letI := isIso_fixedComparisonDirectImageMatePlus A f
  asIso (fixedComparisonDirectImageMatePlus A f)

/-- The three equations in the identity-open normalization, using only canonical maps.
The first is an equality of natural transformations, hence is natural in L. The last
two are the corresponding sheaf and termwise-derived equations.
Source: Stacks Tags 09AF and 099R; blueprint compact-support factor
(blueprint: lem-coef-proper-identity-open-site-comparison). -/
def ProperIdentityOpenSiteComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : Prop :=
  (Functor.whiskerLeft (siteComparisonDerivedPullbackPlus X A)
      (properIdentityOpenProEtaleIso A f).inv ≫
    (compactSupportSiteComparisonPlus A (Compactification.ofIsProper f)).inv ≫
    Functor.whiskerRight (properIdentityOpenEtaleIso A f).hom
      (siteComparisonDerivedPullbackPlus Y A) = (properIdentityOpenMateIso A f).inv) ∧
  (∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) (𝟙 X)).hom.app M ≫
      (openImmersionLowerShriekIdIso (ModuleCat.{u + 1} A) X).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M) =
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).map
      ((Etale.openImmersionLowerShriekId (ModuleCat.{u + 1} A) X).hom.app M)) ∧
  (∀ L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
    (properOpenSiteExtensionIso A (𝟙 X)).hom.app L ≫
      (identityOpenProEtaleDerivedIso A X).hom.app
        ((siteComparisonDerivedPullbackPlus X A).obj L) =
    (siteComparisonDerivedPullbackPlus X A).map
      ((identityOpenEtaleDerivedIso A X).hom.app L))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Proper identity-open compact-support comparison is the inverse named direct-image mate.
Source: blueprint `thm-sf-ambient-adjoint-class.proof.md`, compact-support factor;
Stacks Tags 09AF and 099R
(blueprint: lem-coef-proper-identity-open-site-comparison).

Proof: (1) For the identity open every site object factors uniquely through it.
Both extension presheaves are the original sheaf, including restrictions and scalars.
The sheafification universal property gives the displayed canonical identifications.
(2) Apply lem-sf-open-comparison-unit-normalization at id. The sectionwise comparison
of the right adjoints is identity; the extension Hom bijections are identity under
these identifications, and the comparison Hom bijection cancels its inverse. Evaluate
at the identity to get t_p o = S(t_e) on sheaves.
(3) Apply this equality degreewise. Exact comparison and open extension descend
termwise. Parts (2) and (3) of lem-weil-pbc-localization-universal-property preserve
composition and detect equality, giving t_p o = S(t_e) in D+.
(4) Expand def-sf-compact-support-site-comparison-construction at (id,f): its forward
D+ map is b at J_e L followed by Q(o_L). The identifications e and q are F(t_e)
and Q(t_p), including the displayed functor unitors. Properness supplies qcqs.
(5) Naturality of the named mate gives q C^{-1} = b S(e). Cancel the invertible
factors to obtain q^{-1} C S(e) = b^{-1} in Lean composition order. This is an
equality of natural transformations and includes zero complexes and empty X. -/
theorem properIdentityOpenSiteComparison
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of D.k)) (aY : Y ⟶ Spec (.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsProper f] (_hf : f ≫ aY = aX) :
    @ProperIdentityOpenSiteComparison (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n hn) X Y f inferInstance := by
  let A := Padic.coefficientExtensionRing l E n
  have : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  have hs := (openImmersionLowerShriekComparison_coherence A).2.2 X
  have hs' : ∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) (𝟙 X)).hom.app M ≫
        (openImmersionLowerShriekIdIso (ModuleCat.{u + 1} A) X).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).map
        ((Etale.openImmersionLowerShriekId (ModuleCat.{u + 1} A) X).hom.app M) := by
    intro M
    simpa only [openImmersionLowerShriekIdIso, Etale.openImmersionLowerShriekId,
      adjoint_identity_iso] using hs M
  have hsheaf :
      openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) (𝟙 X) ≪≫
        Functor.isoWhiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} A) X)
          (openImmersionLowerShriekIdIso (ModuleCat.{u + 1} A) X) =
      Functor.isoWhiskerRight (Etale.openImmersionLowerShriekId (ModuleCat.{u + 1} A) X)
        (comparisonUpperStar (ModuleCat.{u + 1} A) X) := by
    apply Iso.ext
    ext M : 2
    simpa using hs' M
  have hd := derive_identity_square
    (comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) (𝟙 X))
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) (𝟙 X))
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) (𝟙 X))
    (Etale.openImmersionLowerShriekId (ModuleCat.{u + 1} A) X)
    (openImmersionLowerShriekIdIso (ModuleCat.{u + 1} A) X) hsheaf
  change ProperIdentityOpenSiteComparison A f
  refine ⟨?_, hs', fun L ↦ NatTrans.congr_app hd L⟩
  ext L : 2
  let S := siteComparisonDerivedPullbackPlus X A
  let T := siteComparisonDerivedPullbackPlus Y A
  let Q := (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus
  let b := properIdentityOpenMateIso A f
  let e := identityOpenEtaleDerivedIso A X
  let p := identityOpenProEtaleDerivedIso A X
  let o := properOpenSiteExtensionIso A (𝟙 X)
  have hdL : o.hom.app L ≫ p.hom.app (S.obj L) = S.map (e.hom.app L) :=
    NatTrans.congr_app hd L
  have hb := b.inv.naturality (e.hom.app L)
  simp only [Functor.comp_map] at hb
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    properIdentityOpenProEtaleIso, properIdentityOpenEtaleIso, Iso.trans_hom,
    Iso.trans_inv, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.map_comp]
  dsimp only [Compactification.ofIsProper] at *
  erw [(siteComparisonDerivedPullbackPlus Y A).map_id]
  simp only [Category.comp_id, Category.id_comp]
  change Q.map (p.inv.app (S.obj L)) ≫
    (compactSupportSiteComparisonPlus A (Compactification.ofIsProper f)).inv.app L ≫
      T.map ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) f).map
        (e.hom.app L)) = b.inv.app L
  simp only [compactSupportSiteComparisonPlus, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_inv, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  change Q.map (p.inv.app (S.obj L)) ≫ Q.map (o.inv.app L) ≫
    b.inv.app ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
      (𝟙 X)).mapDerivedCategoryPlus.obj L) ≫
    T.map ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) f).map
      (e.hom.app L)) = b.inv.app L
  rw [← hb]
  have hi : p.inv.app (S.obj L) ≫ o.inv.app L ≫ S.map (e.hom.app L) = 𝟙 _ := by
    rw [← hdL, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rw [← Q.map_comp_assoc, ← Q.map_comp_assoc, Category.assoc, hi, Q.map_id,
    Category.id_comp]
  rfl

end AlgebraicGeometry.ProEtale
