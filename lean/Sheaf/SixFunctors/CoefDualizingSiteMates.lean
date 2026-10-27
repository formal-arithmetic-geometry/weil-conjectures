module

public import Sheaf.Paper.EtaleCompactSupportCoefficientChange
public import Sheaf.SixFunctors.FiniteDualitySiteComparison
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import Sheaf.Paper.EtaleDerivedScalarTensor

import all Sheaf.Paper.NormalizedOriginComparisonCoherence
import all Sheaf.Paper.EtaleCompactSupportCoefficientChange

/-! # Site realization of normalized coefficient counit mates

Source: main-20261015, lem-coef-finite-dualizing.proof.md, final paragraph, final sentence
(blueprint: lem-coef-dualizing-site-mates).

All comparisons below use the recorded compact-support, tensor, and comparison-unit maps.
The pro-etale Hom equivalence is restricted to its specified etale-origin class.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
open AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.CoefDualizingSiteMates

private local instance fixedSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private local instance finiteCoeff (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)

/-- Ordinary etale module derived category. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev Et (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- Its bounded-below full subcategory. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev EtPlus (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- The corresponding pro-etale category. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev Pro (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))

/-- Derived scalar extension on the unchanged small pro-etale site.
Source: blueprint coefficient convention (blueprint: lem-coef-dualizing-site-mates). -/
abbrev TP {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) : Pro A X ⥤ Pro B X :=
  @pbcFixedScalarExtension.{u} X.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
    A B inferInstance inferInstance φ

/-- The recorded exact comparison pullback. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev S (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) : Et A X ⥤ Pro A X :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory

/-- The recorded comparison direct image. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev U (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) : Pro A X ⥤ Et A X :=
  (comparisonLowerStar (ModuleCat.{u + 1} A) X).rightDerivedFunctor

/-- Compact support at the retained compactification. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev F (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : Et A X ⥤ Et A Y :=
  Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- The same compact support on D+. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev Fplus (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : EtPlus A X ⥤ EtPlus A Y :=
  Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c

/-- The recorded pro-etale compact support. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev P (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : Pro A X ⥤ Pro A Y :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- The right functor is precisely S G U. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev J (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}}
    (G : Et A Y ⥤ Et A X) : Pro A Y ⥤ Pro A X := U A Y ⋙ G ⋙ S A X

/-- Alpha is comparison pullback of G applied to the comparison adjunction unit.
Source: blueprint final paragraph (blueprint: lem-coef-dualizing-site-mates). -/
def alpha (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}}
    (G : Et A Y ⥤ Et A X) (H : Et A Y) :
    (S A X).obj (G.obj H) ⟶ (J A G).obj ((S A Y).obj H) :=
  (S A X).map (G.map ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app H))

/-- The universal tensor presentation is canonically isomorphic to the chosen scalar
extension, by the same universal unit. Source: Stacks 07A6 and blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
def modelIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {X : Scheme.{u}} {K : EtPlus A X}
    (M : Etale.CoefficientTensorModel φ X K) :
    (Etale.scalarExtension φ X).obj K.obj ≅ M.obj.obj :=
  let ad := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let g := (ad.homEquiv K.obj M.obj.obj).symm M.unit.hom
  have hu : Sheaf.IsDerivedBaseChange (ad.unit.app K.obj) := fun L ↦ by
    convert (ad.homEquiv K.obj L).bijective using 1
    funext g
    exact (ad.homEquiv_unit K.obj L g).symm
  have hg : ad.unit.app K.obj ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map g = M.unit.hom :=
    (ad.homEquiv_unit K.obj M.obj.obj g).symm.trans (Equiv.apply_symm_apply _ _)
  haveI := Sheaf.IsDerivedBaseChange.isIso hu M.universal g hg
  asIso g

/-- Tensor/site comparison at a universal tensor presentation, with B-linearity fixed
by the scalar unit. Source: blueprint final paragraph; Stacks 07A4
(blueprint: lem-coef-dualizing-site-mates). -/
def tensorSiteIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {X : Scheme.{u}} {K : EtPlus A X}
    (M : Etale.CoefficientTensorModel φ X K) :
    (S B X).obj M.obj.obj ≅
      (TP φ X).obj ((S A X).obj K.obj) :=
  (S B X).mapIso (modelIso M).symm ≪≫ (pbcComparisonReduction.{u} X φ).symm.app K.obj

/-- The actual coefficient/counit composite, including the canonical D+ inclusion
comparisons. Source: blueprint final paragraph (blueprint: lem-coef-dualizing-site-mates). -/
def counitWord {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {φ : A →+* B} {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {G : Et A Y ⥤ Et A X} (ad : F A c ⊣ G)
    (N : EtPlus A Y) (hGN : _root_.DerivedCategory.TStructure.t.plus (G.obj N.obj))
    (M : Etale.CoefficientTensorModel φ X ⟨G.obj N.obj, hGN⟩)
    (MF : Etale.CoefficientTensorModel φ Y ((Fplus A c).obj ⟨G.obj N.obj, hGN⟩))
    (MN : Etale.CoefficientTensorModel φ Y N)
    [IsIso (Etale.compactSupportCoefficientComparisonPlus c M MF)] :
    (F B c).obj M.obj.obj ⟶ MN.obj.obj :=
  (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} B) c).inv.app M.obj ≫
    (inv (Etale.compactSupportCoefficientComparisonPlus c M MF)).hom ≫
      (MF.map MN (ObjectProperty.homMk
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) c).hom.app ⟨G.obj N.obj, hGN⟩ ≫
            ad.counit.app N.obj))).hom

/-- The source endpoint identification a = t followed by scalar extension of alpha.
Source: blueprint final paragraph (blueprint: lem-coef-dualizing-site-mates). -/
def sourceIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {X Y : Scheme.{u}} (G : Et A Y ⥤ Et A X)
    (N : EtPlus A Y) (hGN : _root_.DerivedCategory.TStructure.t.plus (G.obj N.obj))
    (M : Etale.CoefficientTensorModel φ X ⟨G.obj N.obj, hGN⟩)
    (hα : IsIso (alpha A G N.obj)) :
    (S B X).obj M.obj.obj ≅
      (TP φ X).obj
        ((J A G).obj ((S A Y).obj N.obj)) :=
  haveI := hα
  tensorSiteIso M ≪≫
    (TP φ X).mapIso (asIso (alpha A G N.obj))

/-- The displayed pro-etale mate is literal transport of v by the fixed endpoints.
Source: blueprint final paragraph (blueprint: lem-coef-dualizing-site-mates). -/
def realizedMate {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {X Y : Scheme.{u}} (GA : Et A Y ⥤ Et A X)
    (GB : Et B Y ⥤ Et B X) (N : EtPlus A Y)
    (hGN : _root_.DerivedCategory.TStructure.t.plus (GA.obj N.obj))
    (M : Etale.CoefficientTensorModel φ X ⟨GA.obj N.obj, hGN⟩)
    (MN : Etale.CoefficientTensorModel φ Y N)
    (hα : IsIso (alpha A GA N.obj)) (v : M.obj.obj ⟶ GB.obj MN.obj.obj) :
    (TP φ X).obj
        ((J A GA).obj ((S A Y).obj N.obj)) ⟶
      (J B GB).obj
        ((TP φ Y).obj ((S A Y).obj N.obj)) :=
  (sourceIso GA N hGN M hα).inv ≫ (S B X).map v ≫ alpha B GB MN.obj.obj ≫
    (J B GB).map (tensorSiteIso MN).hom

/-- The transported coefficient/counit word, retaining the specified compact-support
comparison d and both tensor endpoints. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
def realizedWord {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite B]
    {φ : A →+* B} {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (GA : Et A Y ⥤ Et A X) (N : EtPlus A Y)
    (hGN : _root_.DerivedCategory.TStructure.t.plus (GA.obj N.obj))
    (M : Etale.CoefficientTensorModel φ X ⟨GA.obj N.obj, hGN⟩)
    (MN : Etale.CoefficientTensorModel φ Y N)
    (hα : IsIso (alpha A GA N.obj)) (h : (F B c).obj M.obj.obj ⟶ MN.obj.obj) :
    (P B c).obj ((TP φ X).obj
        ((J A GA).obj ((S A Y).obj N.obj))) ⟶
      (TP φ Y).obj ((S A Y).obj N.obj) :=
  (P B c).map (sourceIso GA N hGN M hα).inv ≫
    (compactSupportSiteComparison B c).hom.app M.obj ≫
      (S B Y).map h ≫ (tensorSiteIso MN).hom

/-- The quotient map at positive levels, lifted only to the module coefficient universe.
Source: blueprint coefficient convention (blueprint: lem-coef-dualizing-site-mates). -/
abbrev coefficientMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ) (hmn : m ≤ n) :
    ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)) →+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)) :=
  RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E (n + 1))
    (T := Padic.coefficientExtensionIdeal l E (m + 1))
    (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn)))

private theorem compactSupportTensorUnit_universal
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {φ : A →+* B} {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    {f : X ⟶ Y} (c : Compactification f) {K : EtPlus A X}
    (M : Etale.CoefficientTensorModel φ X K) :
    Sheaf.IsDerivedBaseChange
      (((Fplus A c).map M.unit ≫
        (Etale.compactSupportCoefficientRestrictionPlus φ c).hom.app M.obj).hom) := by
  let η := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
    c.i).mapDerivedCategoryPlus.map M.unit ≫
      (Etale.coefficientRestrictionOpenPlus φ c.i).hom.app M.obj
  have hη : Sheaf.IsDerivedBaseChange η.hom := Etale.openTensorUnit_universal c.i M
  have hp := Etale.properCoefficientTensorUnit_universal φ c.g η hη
  simpa only [η, Fplus, Etale.compactSupportCoefficientRestrictionPlus,
    Etale.rightDerivedLowerShriekOfCompactificationPlus,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.map_comp,
    Functor.comp_map, Category.assoc] using hp

private theorem mapIso_inv_eq
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} (e : X ≅ Y) (e' : F.obj X ≅ F.obj Y)
    (h : F.map e.hom = e'.hom) : F.map e.inv = e'.inv := by
  apply (cancel_mono e'.hom).1
  rw [← h, ← F.map_comp, e.inv_hom_id, F.map_id]
  rw [h]
  exact e'.inv_hom_id.symm

private theorem openComparison_ambient
    (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (K : EtPlus A X) :
    DerivedCategory.Plus.ι.map ((properOpenSiteExtensionIso A j).inv.app K) =
      (Functor.mapDerivedCategoryCompIso
        (comparisonUpperStar (ModuleCat.{u + 1} A) X)
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)).inv.app K.obj ≫
      (Functor.mapDerivedCategoryNatIso
        (openImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} A) j).symm).hom.app K.obj ≫
      (Functor.mapDerivedCategoryCompIso
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j)
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z)).hom.app K.obj := by
  have hc := mapIso_inv_eq DerivedCategory.Plus.ι
    ((Functor.mapDerivedCategoryPlusCompIso
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)).app K)
    ((Functor.mapDerivedCategoryCompIso
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)).app K.obj)
    (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app _ _ K)
  have hn := mapIso_inv_eq DerivedCategory.Plus.ι
    ((Functor.mapDerivedCategoryPlusNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j)).app K)
    ((Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j)).app K.obj)
    (Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app _ K)
  dsimp only [Iso.app_inv] at hc hn
  simp only [properOpenSiteExtensionIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.map_comp]
  erw [hc, hn, Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
  simp only [Category.assoc]
  rfl

private theorem compactSupportComparison_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : EtPlus A X) :
    (compactSupportSiteComparison A c).hom.app K =
      (fixedCompactSupportComparisonIso A c).hom.app K := by
  let R := lowerStar (ModuleCat.{u + 1} A) c.g
  have hn := R.rightDerivedFunctorPlusCompatibility.inv.naturality
    ((properOpenSiteExtensionIso A c.i).inv.app K)
  dsimp only [Functor.comp_map] at hn
  simp only [compactSupportSiteComparison, compactSupportSiteComparisonPlus,
    fixedCompactSupportComparisonIso, fixedDirectImageComparisonIso,
    Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Functor.comp_map, Functor.comp_obj]
  rw [← reassoc_of% hn, openComparison_ambient]
  dsimp only [Functor.mapDerivedCategoryPlus, ObjectProperty.lift, Functor.comp_obj,
    DerivedCategory.Plus.ι, ObjectProperty.ι_obj]
  simp only [Functor.map_comp, Category.assoc]
  erw [(openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.map_id,
    (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map_id,
    (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map_id,
    (comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategory.map_id,
    (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map_id]
  repeat erw [Category.id_comp]

private theorem normalizedHom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f)
    (G : Et A Y ⥤ Et A X) (ad : F A c ⊣ G)
    (C : ComparisonClassAdjunction A f c G ad
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X)
      _root_.DerivedCategory.TStructure.t.plus)
    (K : EtPlus A X) (H : EtPlus A Y) (h : (F A c).obj K.obj ⟶ H.obj) :
    C.homEquiv c ((S A X).obj K.obj)
        (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj K.property)
        ((S A Y).obj H.obj)
        ((DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj H.property).plus)
        ((compactSupportSiteComparison A c).hom.app K ≫ (S A Y).map h) =
      (S A X).map ((ad.homEquiv K.obj H.obj) h) ≫ alpha A G H.obj := by
  let η := (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit
  have he : ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ _).symm
      (h ≫ η.app H.obj) = (S A Y).map h := by
    apply ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    simpa only [Functor.id_map, Functor.comp_map] using η.naturality h
  rw [compactSupportComparison_eq, ← he]
  erw [C.homEquiv_normalized]
  rw [ad.homEquiv_naturality_right, Functor.map_comp]
  rfl

attribute [local irreducible] counitWord sourceIso tensorSiteIso modelIso
  realizedWord realizedMate
  Etale.compactSupportCoefficientComparisonPlus Etale.CoefficientTensorModel.map
  compactSupportSiteComparison fixedCompactSupportComparisonIso
  pbcComparisonReduction pbcFixedScalarExtension pbcFixedScalarExtensionComp

/-- Full finite-coefficient site realization of a normalized counit mate. Universal
presentations of scalar extension are quantified, rather than chosen arbitrarily.
Source: main-20261015 lem-coef-finite-dualizing.proof.md, final paragraph, final sentence
(blueprint: lem-coef-dualizing-site-mates).

Proof: (1) The comparison unit is invertible on D+, giving both alpha maps.
(2) The specified Hom chain sends d followed by S(h) to S(h-hat) followed by alpha;
this follows from naturality of the comparison unit and the ordinary adjunction.
The two prescribed compact-support comparisons agree by derived inclusion compatibility.
(3) Compact support of M with its coefficient restriction unit is a universal tensor
presentation, by the open and proper tensor-unit universality lemmas. Its comparison
is invertible, giving the inverse in counitWord.
(4) Naturality of the same Hom chain in the source and target gives realizedMate as
the transpose of realizedWord. If v is invertible, every factor is invertible.
(5) The actual relative counit is the inverse Hom image of the identity. Source
naturality therefore gives its composite with P(realizedMate) equal to realizedWord.
Only the etale-origin Hom bijection is used, with no ambient pro-etale adjunction. -/
theorem siteRealization
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ) (hmn : m ≤ n)
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of D.k)) (aY : Y ⟶ Spec (.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hf : f ≫ aY = aX) (c : Compactification f)
    (GA : Et (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) Y ⥤
      Et (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) X)
    (GB : Et (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) Y ⥤
      Et (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) X)
    (adA : F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) c ⊣ GA)
    (adB : F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) c ⊣ GB)
    (N : EtPlus (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) Y)
    (_hN : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Y N.obj)
    (_hGA : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X
      (GA.obj N.obj)) :
    ∃ hGN : _root_.DerivedCategory.TStructure.t.plus (GA.obj N.obj),
    ∀ (M : Etale.CoefficientTensorModel
        (coefficientMap l E m n hmn)
        X ⟨GA.obj N.obj, hGN⟩)
      (MN : Etale.CoefficientTensorModel
        (coefficientMap l E m n hmn) Y N)
      (_hGB : WeilConjectures.finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
        (GB.obj MN.obj.obj))
      (C : @ComparisonClassAdjunction
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) inferInstance
        (inferInstance : Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))))
        X Y f inferInstance c GB adB
        (DerivedCategory.plusEtaleOrigin
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))) X)
        _root_.DerivedCategory.TStructure.t.plus),
    ∃ MF : Etale.CoefficientTensorModel
        (coefficientMap l E m n hmn)
        Y ((Fplus (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) c).obj
          ⟨GA.obj N.obj, hGN⟩),
    ∃ hc : IsIso (Etale.compactSupportCoefficientComparisonPlus c M MF),
    ∃ hα : IsIso (alpha _ GA N.obj),
      IsIso (alpha _ GB MN.obj.obj) ∧
      ∀ (v : M.obj.obj ⟶ GB.obj MN.obj.obj)
        (_hv : (adB.homEquiv M.obj.obj MN.obj.obj).symm v =
          @counitWord _ _ _ _ _ _ _ _ _ _ c GA adA N hGN M MF MN hc),
      ∃ hx : DerivedCategory.plusEtaleOrigin
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))) X
          ((TP (coefficientMap l E m n hmn) X).obj
            ((J _ GA).obj ((S _ Y).obj N.obj))),
      ∃ hh : _root_.DerivedCategory.TStructure.t.plus
          ((TP (coefficientMap l E m n hmn) Y).obj ((S _ Y).obj N.obj)),
      ∃ hj : DerivedCategory.plusEtaleOrigin
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))) X
          ((J _ GB).obj
            ((TP (coefficientMap l E m n hmn) Y).obj ((S _ Y).obj N.obj))),
        C.homEquiv c _ hx _ hh
            (realizedWord c GA N hGN M MN hα
              (@counitWord _ _ _ _ _ _ _ _ _ _ c GA adA N hGN M MF MN hc)) =
          realizedMate GA GB N hGN M MN hα v ∧
        (IsIso v → IsIso (realizedMate GA GB N hGN M MN hα v)) ∧
        (P _ c).map (realizedMate GA GB N hGN M MN hα v) ≫
            (C.homEquiv c _ hj _ hh).symm (𝟙 _) =
          realizedWord c GA N hGN M MN hα
            (@counitWord _ _ _ _ _ _ _ _ _ _ c GA adA N hGN M MF MN hc) := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated aY
  obtain ⟨a, b, _, hz⟩ := _hGA.1.2
  have hGN : _root_.DerivedCategory.TStructure.t.plus (GA.obj N.obj) :=
    ⟨a, (_root_.DerivedCategory.isGE_iff _ a).2 fun q hq ↦ hz q (.inl hq)⟩
  refine ⟨hGN, ?_⟩
  intro M MN hGB C
  let MF : Etale.CoefficientTensorModel (coefficientMap l E m n hmn) Y
      ((Fplus _ c).obj ⟨GA.obj N.obj, hGN⟩) :=
    ⟨(Fplus _ c).obj M.obj,
      (Fplus _ c).map M.unit ≫
        (Etale.compactSupportCoefficientRestrictionPlus _ c).hom.app M.obj,
      compactSupportTensorUnit_universal c M⟩
  have hc := Etale.compactSupportCoefficientComparisonPlus_isIso c M MF
  have huA := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
    Y N.obj N.property
  have hα : IsIso (alpha _ GA N.obj) := by
    dsimp only [alpha]
    infer_instance
  have huB := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))))
    Y MN.obj.obj MN.obj.property
  have hβ : IsIso (alpha _ GB MN.obj.obj) := by
    dsimp only [alpha]
    infer_instance
  refine ⟨MF, hc, hα, hβ, ?_⟩
  intro v hv
  let a := sourceIso GA N hGN M hα
  let b := tensorSiteIso MN
  have hx := (DerivedCategory.plusEtaleOrigin _ X).prop_of_iso a
    (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj M.obj.property)
  have hh := (DerivedCategory.plusEtaleOrigin _ Y).prop_of_iso b
    (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj MN.obj.property)
  obtain ⟨r, s, _, hz⟩ := hGB.1.2
  have hGN' : _root_.DerivedCategory.TStructure.t.plus (GB.obj MN.obj.obj) :=
    ⟨r, (_root_.DerivedCategory.isGE_iff _ r).2 fun q hq ↦ hz q (.inl hq)⟩
  let j := (@asIso _ _ _ _ (alpha _ GB MN.obj.obj) hβ) ≪≫ (J _ GB).mapIso b
  have hj := (DerivedCategory.plusEtaleOrigin _ X).prop_of_iso j
    (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hGN')
  have ht : C.homEquiv c _ hx _ hh.plus
      (realizedWord c GA N hGN M MN hα
        (@counitWord _ _ _ _ _ _ _ _ _ _ c GA adA N hGN M MF MN hc)) =
      realizedMate GA GB N hGN M MN hα v := by
    unfold realizedWord
    have hn := normalizedHom _ c GB adB C M.obj MN.obj
      (@counitWord _ _ _ _ _ _ _ _ _ _ c GA adA N hGN M MF MN hc)
    have he : (adB.homEquiv _ _)
        (@counitWord _ _ _ _ _ _ _ _ _ _ c GA adA N hGN M MF MN hc) = v := by
      exact (congrArg (adB.homEquiv _ _) hv.symm).trans
        ((adB.homEquiv _ _).apply_symm_apply v)
    rw [he] at hn
    let h := @counitWord _ _ _ _ _ _ _ _ _ _ c GA adA N hGN M MF MN hc
    let d := (compactSupportSiteComparison _ c).hom.app M.obj
    have hM := DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj M.obj.property
    have hH := (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj MN.obj.property).plus
    have hr := C.naturality_right c _ hM _ _ hH hh.plus
      (d ≫ (S _ Y).map h) b.hom
    have hl := C.naturality_left c _ _ hx hM _ hh.plus a.inv
      ((d ≫ (S _ Y).map h) ≫ b.hom)
    calc
      _ = a.inv ≫ C.homEquiv c _ hM _ hh.plus
          ((d ≫ (S _ Y).map h) ≫ b.hom) := by
        simpa only [Category.assoc] using hl
      _ = a.inv ≫ (C.homEquiv c _ hM _ hH (d ≫ (S _ Y).map h) ≫
          (J _ GB).map b.hom) := congrArg (fun z ↦ a.inv ≫ z) hr
      _ = _ := by
        exact (congrArg (fun z ↦ a.inv ≫ z ≫ (J _ GB).map b.hom) hn).trans
          (by simp only [realizedMate, a, b, Category.assoc])
  refine ⟨hx, hh.plus, hj, ht, ?_, ?_⟩
  · intro hv
    have := hv
    unfold realizedMate
    infer_instance
  · apply (C.homEquiv c _ hx _ hh.plus).injective
    exact (C.naturality_left c _ _ hx hj _ hh.plus
      (realizedMate GA GB N hGN M MN hα v)
      ((C.homEquiv c _ hj _ hh.plus).symm (𝟙 _))).trans
        ((congrArg (fun z ↦ realizedMate GA GB N hGN M MN hα v ≫ z)
          ((C.homEquiv c _ hj _ hh.plus).apply_symm_apply (𝟙 _))).trans
            ((Category.comp_id _).trans ht.symm))
/-- The ordinary structure-morphism right adjoint in the same compactification
normalization as the recorded dualizing object. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev dualizingG (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} {a : X ⟶ Z} (c : Compactification a) :
    Et (ULift.{u + 1} A) Z ⥤ Et (ULift.{u + 1} A) X :=
  letI := c.hasCompactification
  Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) a

/-- The constant-unit endpoint identification, with the recorded degree-zero comparison.
Source: blueprint final paragraph (blueprint: lem-coef-dualizing-site-mates). -/
def baseUnitTransport (A : Type u) [CommRing A] (Z : Scheme.{u}) :
    (S (ULift.{u + 1} A) Z).obj (𝟙_ _) ⟶ (𝟙_ (Pro (ULift.{u + 1} A) Z)) :=
  CategoryTheory.finiteDualitySingleTransport
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) Z)
    (comparisonUpperStarUnitIso (ULift.{u + 1} A) Z).hom
    (_root_.DerivedCategory.singleFunctorObjUnitIso _)
    (_root_.DerivedCategory.singleFunctorObjUnitIso _)

private theorem map_map_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    G.map (F.map (f ≫ g)) = G.map (F.map f) ≫ G.map (F.map g) := by
  rw [F.map_comp, G.map_comp]

/-- For a structure morphism the alpha comparison, after the constant-unit endpoint
identification, is exactly the published dualizing comparison, as an actual arrow.
Source: blueprint final paragraph (blueprint: lem-coef-dualizing-site-mates).

Proof: the published finiteDualityObjectMap applies S G to finiteDualityBaseUnit.
That base unit is the comparison adjunction unit followed by U of the degree-zero
constant-unit comparison. Functoriality of G and S expands it into alpha followed
by J of baseUnitTransport, which is precisely the displayed expression. Thus the
identification uses the original comparison arrow and its original constant unit. -/
theorem dualizingNormalization (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} {a : X ⟶ Z} (c : Compactification a) :
    finiteDualityObjectMap A c =
      alpha (ULift.{u + 1} A) (dualizingG A c) (𝟙_ _) ≫
        (J (ULift.{u + 1} A) (dualizingG A c)).map (baseUnitTransport A Z) := by
  have := c.hasCompactification
  exact map_map_comp (dualizingG A c) (S (ULift.{u + 1} A) X)
    ((derivedComparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) Z).unit.app
      (𝟙_ _))
    ((U (ULift.{u + 1} A) Z).map (baseUnitTransport A Z))

end AlgebraicGeometry.ProEtale.CoefDualizingSiteMates

namespace CategoryTheory.CoefDualizingSiteMates

universe u₀ u₁ u₂ w₀ w₁ w₂ v₀ v₁ v₂ z₀ z₁ z₂

/-- Scalar transport through specified endpoint comparisons. The concrete comparison
is realizedMate; here the coherent tensor identifications are explicit parameters.
Source: blueprint final paragraph, quotient cocycle
(blueprint: lem-coef-dualizing-site-mates). -/
def transport {CA : Type u₀} [Category.{v₀} CA] {CB : Type u₁} [Category.{v₁} CB]
    {PA : Type w₀} [Category.{z₀} PA] {PB : Type w₁} [Category.{z₁} PB]
    (SA : CA ⥤ PA) (SB : CB ⥤ PB) (T : CA ⥤ CB) (TP : PA ⥤ PB)
    (t : SA ⋙ TP ≅ T ⋙ SB) {WA : CA} {WB : CB} {VA : PA} {VB : PB}
    (a : SA.obj WA ≅ VA) (b : SB.obj WB ≅ VB) (v : T.obj WA ⟶ WB) :
    TP.obj VA ⟶ VB :=
  TP.map a.inv ≫ t.hom.app WA ≫ SB.map v ≫ b.hom

/-- Transport preserves identity coefficient normalization under the specified tensor
unit identifications, including when the scalar functors are only isomorphic to identity.
Source: blueprint final paragraph, identity clause
(blueprint: lem-coef-dualizing-site-mates).

Proof: expand transport. The ordinary unit identification e and compatibility ht
replace the tensor-comparison factors by ep at S(W). Naturality of ep moves the
source endpoint inverse past ep. Cancel that inverse with the target endpoint.
The remaining arrow is ep at V, precisely the normalized identity. This applies
also to the canonical chosen scalar functors, not only literal identity functors. -/
theorem transport_identity {C : Type u₀} [Category.{v₀} C]
    {P : Type w₀} [Category.{z₀} P] (S : C ⥤ P)
    (T : C ⥤ C) (TP : P ⥤ P) (t : S ⋙ TP ≅ T ⋙ S)
    (e : T ≅ 𝟭 C) (ep : TP ≅ 𝟭 P)
    (_ht : ∀ W : C, t.hom.app W ≫ S.map (e.hom.app W) = ep.hom.app (S.obj W))
    {W : C} {V : P} (a : S.obj W ≅ V) :
    transport S S T TP t a a (e.hom.app W) = ep.hom.app V := by
  dsimp only [transport]
  calc
    _ = TP.map a.inv ≫ (t.hom.app W ≫ S.map (e.hom.app W)) ≫ a.hom := by
      simp only [Category.assoc]
    _ = TP.map a.inv ≫ ep.hom.app (S.obj W) ≫ a.hom := by rw [_ht]
    _ = ep.hom.app V ≫ a.inv ≫ a.hom := by
      rw [← Category.assoc, ep.hom.naturality]
      simp only [Functor.id_map, Category.assoc]
    _ = ep.hom.app V := by simp

/-- Every successive-coefficient cocycle transports under the specified coherent tensor
identifications. This is equality of the displayed arrows, not only of their iso classes.
Source: blueprint final paragraph, quotient cocycle
(blueprint: lem-coef-dualizing-site-mates).

Proof: expand both transported maps. The intermediate endpoint inverse and direct
comparison cancel. Naturality of tBC moves the image of vAB through tBC. The assumed
coherence of the tensor comparisons combines the two t factors into tAC, with the
specified scalar associator. Apply the assumed ordinary coefficient cocycle. The
remaining source endpoint passes through the pro-etale associator by naturality.
This is the direct transported map. The representative coherence required here is
the ordinary K-flat tensor reassociation: (x tensor b) tensor c maps to x tensor bc.
Hence the actual comparison comparisons in siteRealization satisfy this hypothesis. -/
theorem transport_cocycle
    {CA : Type u₀} [Category.{v₀} CA] {CB : Type u₁} [Category.{v₁} CB]
    {CC : Type u₂} [Category.{v₂} CC]
    {PA : Type w₀} [Category.{z₀} PA] {PB : Type w₁} [Category.{z₁} PB]
    {PC : Type w₂} [Category.{z₂} PC]
    (SA : CA ⥤ PA) (SB : CB ⥤ PB) (SC : CC ⥤ PC)
    (TAB : CA ⥤ CB) (TBC : CB ⥤ CC) (TAC : CA ⥤ CC)
    (PAB : PA ⥤ PB) (PBC : PB ⥤ PC) (PAC : PA ⥤ PC)
    (tAB : SA ⋙ PAB ≅ TAB ⋙ SB) (tBC : SB ⋙ PBC ≅ TBC ⋙ SC)
    (tAC : SA ⋙ PAC ≅ TAC ⋙ SC) (e : TAB ⋙ TBC ≅ TAC) (ep : PAB ⋙ PBC ≅ PAC)
    (_ht : ∀ W : CA,
      PBC.map (tAB.hom.app W) ≫ tBC.hom.app (TAB.obj W) ≫ SC.map (e.hom.app W) =
        ep.hom.app (SA.obj W) ≫ tAC.hom.app W)
    {WA : CA} {WB : CB} {WC : CC} {VA : PA} {VB : PB} {VC : PC}
    (a : SA.obj WA ≅ VA) (b : SB.obj WB ≅ VB) (c : SC.obj WC ≅ VC)
    (vAB : TAB.obj WA ⟶ WB) (vBC : TBC.obj WB ⟶ WC) (vAC : TAC.obj WA ⟶ WC)
    (_hv : TBC.map vAB ≫ vBC = e.hom.app WA ≫ vAC) :
    PBC.map (transport SA SB TAB PAB tAB a b vAB) ≫
        transport SB SC TBC PBC tBC b c vBC =
      ep.hom.app VA ≫ transport SA SC TAC PAC tAC a c vAC := by
  simp only [transport, Functor.map_comp, Category.assoc]
  rw [← PBC.map_comp_assoc b.hom b.inv, b.hom_inv_id]
  simp only [Functor.map_id, Category.id_comp]
  have hn := tBC.hom.naturality_assoc vAB (SC.map vBC ≫ c.hom)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  rw [← SC.map_comp_assoc, _hv, SC.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (_ht WA)]
  simpa only [Functor.comp_map, Category.assoc] using
    ep.hom.naturality_assoc a.inv (tAC.hom.app WA ≫ SC.map vAC ≫ c.hom)

end CategoryTheory.CoefDualizingSiteMates

namespace AlgebraicGeometry.ProEtale.CoefDualizingSiteMates

/-- The pro-etale scalar associator, fixed by the composition of the actual restriction
functors. Source: blueprint quotient cocycle (blueprint: lem-coef-dualizing-site-mates). -/
def tensorComp {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (X : Scheme.{u}) :
    TP φ X ⋙ TP ψ X ≅ TP (ψ.comp φ) X :=
  @pbcFixedScalarExtensionComp.{u} X.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
    A B C inferInstance inferInstance inferInstance φ ψ (ψ.comp φ) rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Coherence of the actual site/tensor comparisons for successive coefficients.
Source: blueprint quotient cocycle (blueprint: lem-coef-dualizing-site-mates).

Proof: the generic comparisonScalarComp lemma expresses this coherence with the
inverse site comparisons. It follows from composition of scalar restriction mates,
exact derived descent, and preservation of horizontal pasting by the mates equivalence.
Cancel the direct comparison on the right and its two inverse-comparison factors;
functoriality and identity cancellation give the displayed equation. No flatness or
boundedness hypothesis is used. -/
theorem tensorCoherence {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (X : Scheme.{u}) (K : Et A X) :
    (TP ψ X).map ((pbcComparisonReduction.{u} X φ).hom.app K) ≫
        (pbcComparisonReduction.{u} X ψ).hom.app ((Etale.scalarExtension φ X).obj K) ≫
        (S C X).map
          ((pbcFixedScalarExtensionComp.{u} X.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app K) =
      (tensorComp φ ψ X).hom.app ((S A X).obj K) ≫
        (pbcComparisonReduction.{u} X (ψ.comp φ)).hom.app K := by
  apply (cancel_mono ((pbcComparisonReduction X (ψ.comp φ)).inv.app K)).1
  simp only [Category.assoc]
  rw [comparisonScalarComp X φ ψ (ψ.comp φ) rfl K]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  erw [(TP ψ X).map_id]
  simp only [Category.id_comp, Category.comp_id]
  rfl

/-- The concrete mate formula is precisely scalar transport with the recorded scalar
comparison, after the unique tensor-presentation identification. Thus the identity and
cocycle theorems apply to these actual arrows.
Source: blueprint final paragraph (blueprint: lem-coef-dualizing-site-mates).

Proof: expand realizedMate, sourceIso and tensorSiteIso. Inverting sourceIso reverses
the composite; functors preserve inverses. Its first two factors are TP(alpha inverse)
and pbcComparisonReduction. The remaining factor is S(modelIso hom). Combine it
with S(v) by functoriality. The final factors are alpha_B and J_B(t), exactly the
specified target endpoint. This gives transport literally, with no new Hom bijection. -/
theorem realizedMate_transport
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {X Y : Scheme.{u}} (GA : Et A Y ⥤ Et A X)
    (GB : Et B Y ⥤ Et B X) (N : EtPlus A Y)
    (hGN : _root_.DerivedCategory.TStructure.t.plus (GA.obj N.obj))
    (M : Etale.CoefficientTensorModel φ X ⟨GA.obj N.obj, hGN⟩)
    (MN : Etale.CoefficientTensorModel φ Y N)
    (hα : IsIso (alpha A GA N.obj)) (hβ : IsIso (alpha B GB MN.obj.obj))
    (v : M.obj.obj ⟶ GB.obj MN.obj.obj) :
    realizedMate GA GB N hGN M MN hα v =
      @CategoryTheory.CoefDualizingSiteMates.transport _ _ _ _ _ _ _ _
        (S A X) (S B X) (Etale.scalarExtension φ X) (TP φ X)
        (pbcComparisonReduction.{u} X φ) _ _ _ _
        (@asIso _ _ _ _ (alpha A GA N.obj) hα)
        ((@asIso _ _ _ _ (alpha B GB MN.obj.obj) hβ) ≪≫
          (J B GB).mapIso (tensorSiteIso MN))
        ((modelIso M).hom ≫ v) := by
  simp only [realizedMate, sourceIso, tensorSiteIso,
    CategoryTheory.CoefDualizingSiteMates.transport, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Iso.symm_inv, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, asIso_hom, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.ProEtale.CoefDualizingSiteMates

