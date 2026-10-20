/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q137
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.CompactSupportExchangeTransport
public import Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass
public import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage

/-!
# Counit cancellation and transposition under site comparison

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-smb-extraordinary.proof.md, transport of adjunction bijections and counits
(blueprint: lem-pur-smb-mate-counit-cancellation

).The auxiliary definitions spell out the specified maps, including the compatibility
between bounded-below compact support and its ambient derived functor. No adjunction
on arbitrary pro-etale objects is introduced.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The finite coefficient instance supplied by the fixed positive purity level.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md,
transport of adjunction bijections and counits
(blueprint: lem-pur-smb-mate-counit-cancellation). -/
instance mateCounitCoefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  letI : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  Finite.of_equiv P.Ring Equiv.ulift.symm

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {v : Y' ⟶ Y}
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable (sq : IsPullback u' f' f v) (c : Compactification f)

/-- The inverse of the pro-etale exchange, constructed through the specified etale exchange.
Its forward map is identified with the ambient pro-etale exchange in the main statement.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md,
transport of adjunction bijections and counits
(blueprint: lem-pur-smb-mate-counit-cancellation). -/
def mateCounitExchangeIso
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c) ⋙
        (upperStar (ModuleCat.{u + 1} Λ) v).leftDerivedFunctor).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj M.obj) ≅
      ((upperStar (ModuleCat.{u + 1} Λ) u').leftDerivedFunctor ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
          (c.ofIsPullback sq)).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj M.obj) :=
  letI := (Etale.compactSupportFiniteTorsion Λ sq c).1 M
  ((compactExchangeTransportSource Λ v c).app M).symm ≪≫
    (DerivedCategory.Plus.ι ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory).mapIso
        (asIso ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
          Λ sq c).app M)) ≪≫
    (compactExchangeTransportTarget Λ sq c).app M

variable
  (R : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
  (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ⊣ R)

/-- The etale counit, with the bounded-below compact-support compatibility inserted.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md,
transport of adjunction bijections and counits
(blueprint: lem-pur-smb-mate-counit-cancellation). -/
def mateCounitEtaleCounit
    (G : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : _root_.DerivedCategory.TStructure.t.plus (R.obj G.obj)) :
    (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
        ⟨R.obj G.obj, hM⟩ ⟶ G :=
  ObjectProperty.homMk
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} Λ) c).hom.app ⟨R.obj G.obj, hM⟩ ≫ adj.counit.app G.obj)

/-- The specified pro-etale counit C_Y(epsilon) after C_c inverse.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md,
transport of adjunction bijections and counits
(blueprint: lem-pur-smb-mate-counit-cancellation). -/
def mateCounitProCounit
    (G : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : _root_.DerivedCategory.TStructure.t.plus (R.obj G.obj)) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj (R.obj G.obj)) ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory.obj G.obj :=
  (compactExchangeTransportComparison Λ c).inv.app ⟨R.obj G.obj, hM⟩ ≫
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map (mateCounitEtaleCounit Λ c R adj G hM))

/-- The etale arrow w = v^*(epsilon) after the inverse compact-support exchange.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md,
transport of adjunction bijections and counits
(blueprint: lem-pur-smb-mate-counit-cancellation). -/
def mateCounitEtaleComposite
    (G : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : _root_.DerivedCategory.TStructure.t.plus (R.obj G.obj)) :
    (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
        (c.ofIsPullback sq)).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) u').mapDerivedCategoryPlus.obj
            ⟨R.obj G.obj, hM⟩) ⟶
      (Etale.upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryPlus.obj G :=
  (asIso (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
    Λ sq c)).inv.app ⟨R.obj G.obj, hM⟩ ≫
    (Etale.upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryPlus.map
      (mateCounitEtaleCounit Λ c R adj G hM)

/-- The pro-etale arrow z = Lv^*(epsilon^p) after the inverse specified exchange.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md,
transport of adjunction bijections and counits
(blueprint: lem-pur-smb-mate-counit-cancellation). -/
def mateCounitProComposite
    (G : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : _root_.DerivedCategory.TStructure.t.plus (R.obj G.obj)) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (c.ofIsPullback sq)).obj
          ((upperStar (ModuleCat.{u + 1} Λ) u').leftDerivedFunctor.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
              (R.obj G.obj))) ⟶
      (upperStar (ModuleCat.{u + 1} Λ) v).leftDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory.obj G.obj) :=
  (mateCounitExchangeIso Λ sq c ⟨R.obj G.obj, hM⟩).inv ≫
    (upperStar (ModuleCat.{u + 1} Λ) v).leftDerivedFunctor.map
      (mateCounitProCounit Λ c R adj G hM)

/-- The left side of cancellation identity (1), including T_M and kappa_v inverse.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md,
transport of adjunction bijections and counits
(blueprint: lem-pur-smb-mate-counit-cancellation). -/
def mateCounitCancelled
    (G : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : _root_.DerivedCategory.TStructure.t.plus (R.obj G.obj)) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
          (c.ofIsPullback sq)).obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) u').mapDerivedCategoryPlus.obj
              ⟨R.obj G.obj, hM⟩)).obj ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryPlus.obj G).obj :=
  (compactExchangeTransportTarget Λ sq c).hom.app ⟨R.obj G.obj, hM⟩ ≫
    mateCounitProComposite Λ sq c R adj G hM ≫
    (leftDerivedUpperStarComparisonIso v Λ).inv.app G

variable
  (R' : _root_.DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
    _root_.DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
  (adj' : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
    (c.ofIsPullback sq) ⊣ R')

/-- The ordinary etale transpose beta^e under the supplied etale adjunction.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md,
transport of adjunction bijections and counits
(blueprint: lem-pur-smb-mate-counit-cancellation). -/
def mateCounitEtaleTranspose
    (G : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : _root_.DerivedCategory.TStructure.t.plus (R.obj G.obj)) :
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) u').mapDerivedCategoryPlus.obj
        ⟨R.obj G.obj, hM⟩).obj ⟶
      R'.obj ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryPlus.obj G).obj :=
  (adj'.homEquiv _ _)
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} Λ) (c.ofIsPullback sq)).inv.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) u').mapDerivedCategoryPlus.obj
            ⟨R.obj G.obj, hM⟩) ≫
      DerivedCategory.Plus.ι.map (mateCounitEtaleComposite Λ sq c R adj G hM))

/-- The normalized transported transpose, first using the kappa_u witness, then the
canonical compact-support comparison, the comparison unit, and J prime. This is the
displayed class-restricted formula; it requires no all-object pro-etale adjunction.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md,
transport of adjunction bijections and counits
(blueprint: lem-pur-smb-mate-counit-cancellation). -/
def mateCounitProTranspose
    (G : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : _root_.DerivedCategory.TStructure.t.plus (R.obj G.obj)) :
    (upperStar (ModuleCat.{u + 1} Λ) u').leftDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj (R.obj G.obj)) ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory.obj
        (R'.obj ((comparisonLowerStar (ModuleCat.{u + 1} Λ) Y').rightDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} Λ) v).leftDerivedFunctor.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory.obj G.obj)))) :=
  (leftDerivedUpperStarComparisonIso u' Λ).inv.app ⟨R.obj G.obj, hM⟩ ≫
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory.map
      ((adj'.homEquiv _ _)
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
            (ModuleCat.{u + 1} Λ) (c.ofIsPullback sq)).inv.app
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) u').mapDerivedCategoryPlus.obj
                ⟨R.obj G.obj, hM⟩) ≫
          (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y').homEquiv _ _
            ((compactExchangeTransportTarget Λ sq c).hom.app ⟨R.obj G.obj, hM⟩ ≫
              mateCounitProComposite Λ sq c R adj G hM)))

/-- The target comparison psi = U(kappa_v) after the specified comparison unit.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md,
transport of adjunction bijections and counits
(blueprint: lem-pur-smb-mate-counit-cancellation). -/
def mateCounitTargetUnit
    (G : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryPlus.obj G).obj ⟶
      (comparisonLowerStar (ModuleCat.{u + 1} Λ) Y').rightDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} Λ) v).leftDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory.obj G.obj)) :=
  (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y').unit.app
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryPlus.obj G).obj ≫
    (comparisonLowerStar (ModuleCat.{u + 1} Λ) Y').rightDerivedFunctor.map
      ((leftDerivedUpperStarComparisonIso v Λ).hom.app G)

/-- The pullback of the map induced by R on two bounded-below inputs. This simply
packages the ordinary derived map into the full bounded-below subcategory.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md,
transport of adjunction bijections and counits
(blueprint: lem-pur-smb-mate-counit-cancellation). -/
def mateCounitInputMap
    (G H : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hG : _root_.DerivedCategory.TStructure.t.plus (R.obj G.obj))
    (hH : _root_.DerivedCategory.TStructure.t.plus (R.obj H.obj)) (a : G ⟶ H) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) u').mapDerivedCategoryPlus.obj ⟨R.obj G.obj, hG⟩ ⟶
      (Etale.upperStar (ModuleCat.{u + 1} Λ) u').mapDerivedCategoryPlus.obj ⟨R.obj H.obj, hH⟩ :=
  (Etale.upperStar (ModuleCat.{u + 1} Λ) u').mapDerivedCategoryPlus.map
    (ObjectProperty.homMk (X := ⟨R.obj G.obj, hG⟩) (Y := ⟨R.obj H.obj, hH⟩)
      (R.map (DerivedCategory.Plus.ι.map a)))


omit [Finite Λ] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mateCounitEtaleCounit_naturality
    (G H : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hG : _root_.DerivedCategory.TStructure.t.plus (R.obj G.obj))
    (hH : _root_.DerivedCategory.TStructure.t.plus (R.obj H.obj)) (a : G ⟶ H) :
    (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).map
        (ObjectProperty.homMk (X := ⟨R.obj G.obj, hG⟩) (Y := ⟨R.obj H.obj, hH⟩)
          (R.map (DerivedCategory.Plus.ι.map a))) ≫
      mateCounitEtaleCounit Λ c R adj H hH =
    mateCounitEtaleCounit Λ c R adj G hG ≫ a := by
  apply ObjectProperty.hom_ext
  change DerivedCategory.Plus.ι.map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).map
        (ObjectProperty.homMk (X := ⟨R.obj G.obj, hG⟩) (Y := ⟨R.obj H.obj, hH⟩)
          (R.map (DerivedCategory.Plus.ι.map a)))) ≫ _ = _
  simp only [mateCounitEtaleCounit, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.homMk]
  simp only [Category.assoc]
  have hn := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} Λ) c).hom.naturality
      (ObjectProperty.homMk (X := ⟨R.obj G.obj, hG⟩) (Y := ⟨R.obj H.obj, hH⟩)
        (R.map (DerivedCategory.Plus.ι.map a)))
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc]
  erw [hn]
  simpa only [Category.assoc, Functor.comp_obj, Functor.comp_map, Functor.id_obj,
    Functor.id_map, ObjectProperty.ι_obj, ObjectProperty.ι_map, ObjectProperty.homMk] using
    congrArg
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} Λ) c).hom.app ⟨R.obj G.obj, hG⟩ ≫ ·)
    (adj.counit.naturality (DerivedCategory.Plus.ι.map a))

omit [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mateCounitEtaleComposite_naturality
    (G H : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hG : _root_.DerivedCategory.TStructure.t.plus (R.obj G.obj))
    (hH : _root_.DerivedCategory.TStructure.t.plus (R.obj H.obj)) (a : G ⟶ H) :
    (Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} Λ) (c.ofIsPullback sq)).map
        (mateCounitInputMap Λ R (u' := u') G H hG hH a) ≫
      mateCounitEtaleComposite Λ sq c R adj H hH =
    mateCounitEtaleComposite Λ sq c R adj G hG ≫
      (Etale.upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryPlus.map a := by
  unfold mateCounitEtaleComposite mateCounitInputMap
  rw [← Category.assoc]
  have hn := (asIso (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
    Λ sq c)).inv.naturality
      (ObjectProperty.homMk (X := ⟨R.obj G.obj, hG⟩) (Y := ⟨R.obj H.obj, hH⟩)
        (R.map (DerivedCategory.Plus.ι.map a)))
  simp only [Functor.comp_map] at hn
  erw [hn]
  simpa only [Etale.rightDerivedLowerShriekOfCompactificationPlus,
    Functor.comp_map, Functor.map_comp, Category.assoc] using
    congrArg
      ((asIso (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
        Λ sq c)).inv.app ⟨R.obj G.obj, hG⟩ ≫ ·)
      (congrArg ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryPlus.map)
        (mateCounitEtaleCounit_naturality Λ c R adj G H hG hH a))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mateCounitExchangeIso_hom
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (mateCounitExchangeIso Λ sq c M).hom =
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} Λ) sq c).app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj M.obj) := by
  have h := (compactSupport_exchange_transport Λ sq c).2 M _ (Iso.refl _)
  simpa [mateCounitExchangeIso, compactExchangeTransportAtWitness] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mateCounitCancelled_eq
    (G : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : _root_.DerivedCategory.TStructure.t.plus (R.obj G.obj)) :
    mateCounitCancelled Λ sq c R adj G hM =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map (mateCounitEtaleComposite Λ sq c R adj G hM)) := by
  simp only [mateCounitCancelled, mateCounitProComposite, mateCounitExchangeIso,
    mateCounitProCounit, mateCounitEtaleComposite, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.app_inv, Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [compactExchangeTransportSource, Iso.trans_hom, Iso.app_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Iso.symm_hom, Functor.associator_inv_app, Category.id_comp, Category.assoc]
  simp only [Functor.map_comp, Category.assoc, Functor.comp_map]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := (leftDerivedUpperStarComparisonIso v Λ).hom.naturality
    (mateCounitEtaleCounit Λ c R adj G hM)
  simp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  simp only [Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, CategoryTheory.Category.comp_id, asIso_inv,
    NatIso.isIso_inv_app]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mateCounitTranspose_eq
    (G : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : _root_.DerivedCategory.TStructure.t.plus (R.obj G.obj)) :
    (leftDerivedUpperStarComparisonIso u' Λ).hom.app ⟨R.obj G.obj, hM⟩ ≫
        mateCounitProTranspose Λ sq c R adj R' adj' G hM =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory.map
          (mateCounitEtaleTranspose Λ sq c R adj R' adj' G hM) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory.map
          (R'.map (mateCounitTargetUnit Λ (v := v) G)) := by
  have hz : (compactExchangeTransportTarget Λ sq c).hom.app ⟨R.obj G.obj, hM⟩ ≫
      mateCounitProComposite Λ sq c R adj G hM =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (mateCounitEtaleComposite Λ sq c R adj G hM)) ≫
        (leftDerivedUpperStarComparisonIso v Λ).hom.app G := by
    apply (cancel_mono ((leftDerivedUpperStarComparisonIso v Λ).inv.app G)).mp
    simpa only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
      mateCounitCancelled] using mateCounitCancelled_eq Λ sq c R adj G hM
  have hc : (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y').homEquiv _ _
      ((compactExchangeTransportTarget Λ sq c).hom.app ⟨R.obj G.obj, hM⟩ ≫
        mateCounitProComposite Λ sq c R adj G hM) =
      DerivedCategory.Plus.ι.map (mateCounitEtaleComposite Λ sq c R adj G hM) ≫
        mateCounitTargetUnit Λ (v := v) G := by
    rw [hz, Adjunction.homEquiv_unit]
    simp only [Functor.map_comp, mateCounitTargetUnit]
    exact ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y').unit.naturality_assoc
      (DerivedCategory.Plus.ι.map (mateCounitEtaleComposite Λ sq c R adj G hM)) _).symm
  simp only [mateCounitProTranspose, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp]
  apply congrArg
    ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory.map)
  change (adj'.homEquiv _ _) (_ ≫ _) =
    (adj'.homEquiv _ _) (_ ≫ _) ≫ R'.map _
  simp only [Functor.comp_obj] at hc ⊢
  rw [hc, ← Category.assoc]
  exact adj'.homEquiv_naturality_right _ _

omit [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mateCounitEtaleTranspose_naturality
    (G H : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hG : _root_.DerivedCategory.TStructure.t.plus (R.obj G.obj))
    (hH : _root_.DerivedCategory.TStructure.t.plus (R.obj H.obj)) (a : G ⟶ H) :
    DerivedCategory.Plus.ι.map (mateCounitInputMap Λ R (u' := u') G H hG hH a) ≫
      mateCounitEtaleTranspose Λ sq c R adj R' adj' H hH =
    mateCounitEtaleTranspose Λ sq c R adj R' adj' G hG ≫
      R'.map (DerivedCategory.Plus.ι.map
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryPlus.map a)) := by
  unfold mateCounitEtaleTranspose
  apply adj'.homEquiv_naturality_left_square
  rw [← Category.assoc]
  have hn := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} Λ) (c.ofIsPullback sq)).inv.naturality
      (mateCounitInputMap Λ R (u' := u') G H hG hH a)
  simp only [Functor.comp_map] at hn
  erw [hn]
  simp only [Category.assoc]
  erw [← Functor.map_comp, mateCounitEtaleComposite_naturality Λ sq c R adj G H hG hH a,
    Functor.map_comp]

omit [Finite Λ] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mateCounitTargetUnit_naturality
    (G H : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (a : G ⟶ H) :
    DerivedCategory.Plus.ι.map
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryPlus.map a) ≫
      mateCounitTargetUnit Λ (v := v) H =
    mateCounitTargetUnit Λ (v := v) G ≫
      (comparisonLowerStar (ModuleCat.{u + 1} Λ) Y').rightDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} Λ) v).leftDerivedFunctor.map
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory.map
            (DerivedCategory.Plus.ι.map a))) := by
  unfold mateCounitTargetUnit
  rw [← Category.assoc]
  have hn := (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y').unit.naturality
    (DerivedCategory.Plus.ι.map
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryPlus.map a))
  simp only [Functor.id_map, Functor.comp_map] at hn
  erw [hn]
  simp only [Category.assoc, ← Functor.map_comp]
  have hk := (leftDerivedUpperStarComparisonIso v Λ).hom.naturality a
  simp only [Functor.comp_map] at hk
  erw [hk]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mateCounitProTranspose_naturality
    (G H : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hG : _root_.DerivedCategory.TStructure.t.plus (R.obj G.obj))
    (hH : _root_.DerivedCategory.TStructure.t.plus (R.obj H.obj)) (a : G ⟶ H) :
    (upperStar (ModuleCat.{u + 1} Λ) u').leftDerivedFunctor.map
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
          (R.map (DerivedCategory.Plus.ι.map a))) ≫
      mateCounitProTranspose Λ sq c R adj R' adj' H hH =
    mateCounitProTranspose Λ sq c R adj R' adj' G hG ≫
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} Λ) v).leftDerivedFunctor ⋙
        (comparisonLowerStar (ModuleCat.{u + 1} Λ) Y').rightDerivedFunctor ⋙ R' ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory).map
          (DerivedCategory.Plus.ι.map a) := by
  let m : (⟨R.obj G.obj, hG⟩ : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) ⟶ ⟨R.obj H.obj, hH⟩ :=
    ObjectProperty.homMk (R.map (DerivedCategory.Plus.ι.map a))
  have hk := (leftDerivedUpperStarComparisonIso u' Λ).hom.naturality m
  simp only [Functor.comp_map] at hk
  apply (cancel_epi ((leftDerivedUpperStarComparisonIso u' Λ).hom.app
    ⟨R.obj G.obj, hG⟩)).mp
  erw [← Category.assoc, ← hk, Category.assoc,
    mateCounitTranspose_eq Λ sq c R adj R' adj' H hH]
  simp only [← Category.assoc]
  rw [mateCounitTranspose_eq Λ sq c R adj R' adj' G hG]
  simp only [Functor.comp_map]
  erw [← Functor.map_comp,
    mateCounitEtaleTranspose_naturality Λ sq c R adj R' adj' G H hG hH a,
    Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [mateCounitTargetUnit_naturality Λ G H a]

omit [Finite Λ] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mateCounitTargetUnit_isIso
    (G : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (mateCounitTargetUnit Λ (v := v) G) := by
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) Y'
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryPlus.obj G).obj
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryPlus.obj G).property
  unfold mateCounitTargetUnit
  infer_instance

/-- Counit cancellation (1), transpose conjugation (2), and their naturality in G.
The isomorphism used for the inverse exchange is identified with the actual ambient
exchange in the first clause. The field and coefficient data are exactly the finite
purity conventions.
Proof plan, following all five steps of the node:
1. Identify the canonical comparison C_c with the inverse of
lem-sf-class-compact-support-comparison. The paths S and T are those of
lem-pur-co-smooth-exchange-transport, so T C(E^e) = E^p S naturally in M.
2. Use thm-cbc-finite-torsion to invert E^e. Both S and T are isomorphisms;
therefore E^p = T C(E^e) S inverse, the forward map of mateCounitExchangeIso.
Consequently (E^p) inverse T = S C((E^e) inverse).
3. Check the bounded-below domains: G and RG are bounded below, exact etale
pullback preserves these bounds, and kappa transports them to the pro-etale
inputs. The second adjoint value is bounded below by the stated hypothesis.
Use the normalized comparison-class Hom formula of thm-sf-ambient-adjoint-class
and def-weil-exceptional-inverse-image. No unbounded pro-etale adjunction occurs.
4. Substitute epsilon^p = C(epsilon^e) C_c inverse into step 2. Functoriality
cancels C_c inverse with C_c. Naturality of kappa_v at epsilon^e then cancels
kappa_v inverse with kappa_v, proving identity (1).
5. Expand the normalized transpose on the kappa_u witness. Identity (1) gives
z T = kappa_v C(w). Naturality of the comparison unit gives
U(z T) eta = U(kappa_v) eta w. Naturality of J prime in its target gives
J prime(psi w) = R prime(psi) J prime(w). Apply C_X prime to obtain (2).
The unit is invertible on bounded-below inputs by thm-weil-pbc-site-comparison,
so psi and its functorial image are isomorphisms. Naturality of every factor
gives the three displayed naturality equations. Empty schemes, zero objects,
identity base changes, arbitrary v and nonsmooth f are included.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md,
transport of adjunction bijections and counits
(blueprint: lem-pur-smb-mate-counit-cancellation). -/
theorem smoothMate_counit_cancellation
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {v : Y' ⟶ Y}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    (aY' : Y' ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    [LocallyOfFiniteType aY'] [QuasiCompact aY']
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hf : f ≫ aY = aX) (_hv : v ≫ aY = aY')
    (sq : IsPullback u' f' f v) (c : Compactification f) [QuasiCompact c.i]
    (R : _root_.DerivedCategory
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c ⊣ R)
    (R' : _root_.DerivedCategory
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (adj' : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) (c.ofIsPullback sq) ⊣ R')
    (G : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (hM : _root_.DerivedCategory.TStructure.t.plus (R.obj G.obj))
    (_hR' : _root_.DerivedCategory.TStructure.t.plus
      (R'.obj ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        v).mapDerivedCategoryPlus.obj G).obj)) :
    (mateCounitExchangeIso P.Coefficient sq c ⟨R.obj G.obj, hM⟩).hom =
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} P.Coefficient) sq c).app
          ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
            X).mapDerivedCategory.obj (R.obj G.obj)) ∧
    mateCounitCancelled P.Coefficient sq c R adj G hM =
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y').mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
          (mateCounitEtaleComposite P.Coefficient sq c R adj G hM)) ∧
    (leftDerivedUpperStarComparisonIso u' P.Coefficient).hom.app ⟨R.obj G.obj, hM⟩ ≫
      mateCounitProTranspose P.Coefficient sq c R adj R' adj' G hM =
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map
          (mateCounitEtaleTranspose P.Coefficient sq c R adj R' adj' G hM) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map
          (R'.map (mateCounitTargetUnit P.Coefficient (v := v) G)) ∧
    IsIso (mateCounitTargetUnit P.Coefficient (v := v) G) ∧
    (∀ (H : DerivedCategory.Plus
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (hH : _root_.DerivedCategory.TStructure.t.plus (R.obj H.obj))
      (_hR'H : _root_.DerivedCategory.TStructure.t.plus
        (R'.obj ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          v).mapDerivedCategoryPlus.obj H).obj)) (a : G ⟶ H),
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y').mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map
            ((Etale.rightDerivedLowerShriekOfCompactificationPlus
              (ModuleCat.{u + 1} P.Coefficient) (c.ofIsPullback sq)).map
                (mateCounitInputMap P.Coefficient R (u' := u') G H hM hH a))) ≫
        mateCounitCancelled P.Coefficient sq c R adj H hH =
      mateCounitCancelled P.Coefficient sq c R adj G hM ≫
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y').mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map
            ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
              v).mapDerivedCategoryPlus.map a)) ∧
      DerivedCategory.Plus.ι.map
          (mateCounitInputMap P.Coefficient R (u' := u') G H hM hH a) ≫
        mateCounitEtaleTranspose P.Coefficient sq c R adj R' adj' H hH =
      mateCounitEtaleTranspose P.Coefficient sq c R adj R' adj' G hM ≫
        R'.map (DerivedCategory.Plus.ι.map
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
            v).mapDerivedCategoryPlus.map a)) ∧
      (upperStar (ModuleCat.{u + 1} P.Coefficient) u').leftDerivedFunctor.map
          ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
            (R.map (DerivedCategory.Plus.ι.map a))) ≫
        mateCounitProTranspose P.Coefficient sq c R adj R' adj' H hH =
      mateCounitProTranspose P.Coefficient sq c R adj R' adj' G hM ≫
        ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory ⋙
          (upperStar (ModuleCat.{u + 1} P.Coefficient) v).leftDerivedFunctor ⋙
          (comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y').rightDerivedFunctor ⋙
          R' ⋙ (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory).map
            (DerivedCategory.Plus.ι.map a)) := by
  refine ⟨mateCounitExchangeIso_hom P.Coefficient sq c ⟨R.obj G.obj, hM⟩,
    mateCounitCancelled_eq P.Coefficient sq c R adj G hM,
    mateCounitTranspose_eq P.Coefficient sq c R adj R' adj' G hM,
    mateCounitTargetUnit_isIso P.Coefficient G, ?_⟩
  intro H hH _hR'H a
  refine ⟨?_,
    mateCounitEtaleTranspose_naturality P.Coefficient sq c R adj R' adj' G H hM hH a,
    mateCounitProTranspose_naturality P.Coefficient sq c R adj R' adj' G H hM hH a⟩
  rw [mateCounitCancelled_eq P.Coefficient sq c R adj H hH,
    mateCounitCancelled_eq P.Coefficient sq c R adj G hM]
  rw [← Functor.map_comp, ← Functor.map_comp]
  simpa only [Functor.map_comp] using congrArg
    ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y').mapDerivedCategory.map)
    (congrArg DerivedCategory.Plus.ι.map
      (mateCounitEtaleComposite_naturality P.Coefficient sq c R adj G H hM hH a))

end AlgebraicGeometry.ProEtale
