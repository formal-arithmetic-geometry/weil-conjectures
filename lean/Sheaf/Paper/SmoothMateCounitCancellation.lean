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
import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange

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
  sorry

end AlgebraicGeometry.ProEtale
