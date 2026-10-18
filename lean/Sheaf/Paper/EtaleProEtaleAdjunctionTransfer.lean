/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.Paper.FiniteDiscreteSchemeRing
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.Paper.FiniteLocalizingExceptionalPreservation
import Sheaf.Paper.LocalizingAdmissibleCoefficients

/-! # Transfer of finite-coefficient adjunctions

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-et-proet,
node det-sp-et-proet-adjunction-transfer (blueprint: det-sp-et-proet-adjunction-transfer).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.AdjunctionTransfer

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The recorded finite-value etale constructibility intersected with finite Tor amplitude.
Source: blueprint det-sp-et-proet-adjunction-transfer, definition of Dctf
(blueprint: det-sp-et-proet-adjunction-transfer). -/
abbrev etaleProperty (T : Scheme.{u}) :=
  Etale.DerivedCategory.isBoundedConstructible A T ⊓
    _root_.DerivedCategory.finiteTorAmplitude (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- The bounded etale objects included in the bounded-below derived category.
The lower bound is read directly from the recorded constructibility predicate.
Source: blueprint det-sp-et-proet-adjunction-transfer, bounded inputs in proof step 1
(blueprint: det-sp-et-proet-adjunction-transfer). -/
def etaleToPlus (T : Scheme.{u}) :
    (etaleProperty A T).FullSubcategory ⥤
      _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  ObjectProperty.ιOfLE (fun K hK ↦ by
    obtain ⟨a, b, _hab, h⟩ := hK.1.2
    exact ⟨a, (_root_.DerivedCategory.isGE_iff K a).mpr (fun i hi ↦ h i (Or.inl hi))⟩)

/-- The finite-coefficient pro-etale convention is etale bounded constructible origin,
intersected with the actual pro-etale Tor test against every degree-zero module sheaf.
Source: blueprint det-sp-et-proet-adjunction-transfer and def-weil-pbc-proetale-modules
(blueprint: det-sp-et-proet-adjunction-transfer). -/
abbrev proEtaleProperty (T : Scheme.{u}) :=
  (Etale.DerivedCategory.isBoundedConstructible A T).map
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⊓
    _root_.DerivedCategory.finiteTorAmplitude
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- Restrict the specified termwise inverse image, retaining its objects and maps.
Source: blueprint det-sp-et-proet-adjunction-transfer, comparison equivalences
(blueprint: det-sp-et-proet-adjunction-transfer). -/
def comparison (T : Scheme.{u})
    (h : ∀ K, etaleProperty A T K → proEtaleProperty A T
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj K)) :
    (etaleProperty A T).FullSubcategory ⥤ (proEtaleProperty A T).FullSubcategory :=
  (proEtaleProperty A T).lift
    ((etaleProperty A T).ι ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory)
    (fun K ↦ h K.obj K.property)

/-- The ordinary etale compactification composite, restricted to Dctf.
Source: blueprint det-sp-et-proet-adjunction-transfer, chosen compactification
(blueprint: det-sp-et-proet-adjunction-transfer). -/
def etaleLowerShriek {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ K, etaleProperty A X K → etaleProperty A Y
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K)) :
    (etaleProperty A X).FullSubcategory ⥤ (etaleProperty A Y).FullSubcategory :=
  (etaleProperty A Y).lift ((etaleProperty A X).ι ⋙
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (fun K ↦ h K.obj K.property)

/-- The same chosen compactification in the ordinary pro-etale coefficient presentation.
Source: blueprint det-sp-et-proet-adjunction-transfer, Rf_!
(blueprint: det-sp-et-proet-adjunction-transfer). -/
def proEtaleLowerShriek {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ K, proEtaleProperty A X K → proEtaleProperty A Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K)) :
    (proEtaleProperty A X).FullSubcategory ⥤ (proEtaleProperty A Y).FullSubcategory :=
  (proEtaleProperty A Y).lift ((proEtaleProperty A X).ι ⋙
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (fun K ↦ h K.obj K.property)

/-- Inclusion of the generators in their recorded localizing closure.
Source: blueprint det-sp-et-proet-adjunction-transfer, Brown restriction
(blueprint: det-sp-et-proet-adjunction-transfer). -/
def toLocalizing (T : Scheme.{u}) :
    (proEtaleProperty A T).FullSubcategory ⥤
      (CategoryTheory.localizingClosure (proEtaleProperty A T)).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K hK _P _hP hgen ↦ hgen K hK)

/-- The compactification functor on the same localizing closures.
Source: blueprint det-sp-et-proet-adjunction-transfer, Brown adjunction
(blueprint: det-sp-et-proet-adjunction-transfer). -/
def localizingLowerShriek {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ K, CategoryTheory.localizingClosure (proEtaleProperty A X) K →
      CategoryTheory.localizingClosure (proEtaleProperty A Y)
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K)) :
    (CategoryTheory.localizingClosure (proEtaleProperty A X)).FullSubcategory ⥤
      (CategoryTheory.localizingClosure (proEtaleProperty A Y)).FullSubcategory :=
  (CategoryTheory.localizingClosure (proEtaleProperty A Y)).lift
    ((CategoryTheory.localizingClosure (proEtaleProperty A X)).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (fun K ↦ h K.obj K.property)

/-- Restrict a Brown right adjoint without changing its ambient objects or morphisms.
Source: blueprint det-sp-et-proet-adjunction-transfer, final conclusion
(blueprint: det-sp-et-proet-adjunction-transfer). -/
def brownRestriction {X Y : Scheme.{u}}
    (J : (CategoryTheory.localizingClosure (proEtaleProperty A Y)).FullSubcategory ⥤
      (CategoryTheory.localizingClosure (proEtaleProperty A X)).FullSubcategory)
    (h : ∀ N : (proEtaleProperty A Y).FullSubcategory,
      proEtaleProperty A X ((J.obj ((toLocalizing A Y).obj N)).obj)) :
    (proEtaleProperty A Y).FullSubcategory ⥤ (proEtaleProperty A X).FullSubcategory :=
  (proEtaleProperty A X).lift
    (toLocalizing A Y ⋙ J ⋙ (CategoryTheory.localizingClosure (proEtaleProperty A X)).ι) h

/-- Transfer the etale adjunction with its prescribed counit, and identify it uniquely
with the restriction of the Brown adjoint. The equivalence equalities ensure that the
forward functors are the actual restricted comparison inverse images. The equation
on cf identifies its inverse with the specified proper mate and open comparison,
so cf is the canonical compact-support comparison for the same compactification. The localizing
categories and compactification functor are expressed in the ordinary constant-ring
presentation of the finite-discrete coefficient categories.

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-et-proet,
det-sp-et-proet-adjunction-transfer, statement and both proof paragraphs
(blueprint: det-sp-et-proet-adjunction-transfer).

Proof:
1. Put E_T = nu_T^*. For M',N' set M=Q_X M', N=Q_Y N'. Use the equivalence
   counits, bounded-below full faithfulness (thm-weil-pbc-site-comparison), the etale
   adjunction, and the given compact-support comparison to identify Hom(M',E_X G N)
   with Hom(Rf_! M',N'). Naturality of the equivalence counits, etale adjunction and
   compact-support comparison makes this a natural Hom equivalence.
2. Transpose the identity to obtain the counit. It is c_f(G Q_Y N') inverse, followed
   by E_Y(epsilon_et at Q_Y N'), followed by the equivalence counit at N'. At E_Y N,
   the equivalence triangle identity gives the displayed formula using the inverse
   equivalence unit at N. The Hom equivalence gives both adjunction triangle identities.
3. Identify finite discrete condensed coefficients with constant ring sheaves using
   lem-weil-pbc-finite-discrete-condensed-ring-constant and
   lem-weil-pbc-finite-discrete-scheme-ring-constant. The clopen-fibre argument identifies
   these with def-weil-pbc-proetale-modules, including empty objects. The section-action
   equivalence def-weil-pbc-internal-abelian-sheaf-module-equivalence is exact termwise,
   so identifies the ordinary derived categories with the module-object categories.
4. sk-prop-sf-existence supplies the Brown adjunction on the localizing closures.
   sk-prop-sf-rf-shriek-preservation makes its right adjoint preserve Dctf and restricts
   the adjunction. Fullness of both inclusions retains exactly the Brown counit.
5. det-sp-unique-right-adjoint transposes the two counits to mutually inverse natural
   transformations. Injectivity of the Brown Hom equivalence proves uniqueness of
   the counit-preserving isomorphism, with precisely the displayed ambient equation. -/
theorem etaleProEtaleAdjunctionTransfer
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (_hA : ∃ n : ℕ, (ℓ ^ n : A) = 0) (c : Compactification f)
    (hX : ∀ K, etaleProperty A X K → proEtaleProperty A X
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K))
    (hY : ∀ K, etaleProperty A Y K → proEtaleProperty A Y
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K))
    (eX : (etaleProperty A X).FullSubcategory ≌ (proEtaleProperty A X).FullSubcategory)
    (eY : (etaleProperty A Y).FullSubcategory ≌ (proEtaleProperty A Y).FullSubcategory)
    (heX : eX.functor = comparison A X hX) (heY : eY.functor = comparison A Y hY)
    (hEt : ∀ K, etaleProperty A X K → etaleProperty A Y
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K))
    (hPro : ∀ K, proEtaleProperty A X K → proEtaleProperty A Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K))
    (cf : etaleLowerShriek A c hEt ⋙ eY.functor ≅
      eX.functor ⋙ proEtaleLowerShriek A c hPro)
    (_hcf : ∀ K : (etaleProperty A X).FullSubcategory,
      (cf.inv.app K).hom =
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
            (eqToHom (congrArg (fun F ↦ (F.obj K).obj) heX)) ≫
          (compactSupportSiteComparison A c).hom.app ((etaleToPlus A X).obj K) ≫
          eqToHom (congrArg (fun F ↦ (F.obj ((etaleLowerShriek A c hEt).obj K)).obj)
            heY).symm)
    (G : (etaleProperty A Y).FullSubcategory ⥤ (etaleProperty A X).FullSubcategory)
    (adjEt : etaleLowerShriek A c hEt ⊣ G) :
    ∃ adjPro : proEtaleLowerShriek A c hPro ⊣ (eY.inverse ⋙ G ⋙ eX.functor),
      (∀ N : (etaleProperty A Y).FullSubcategory,
        (adjPro.counit.app (eY.functor.obj N)) =
          (proEtaleLowerShriek A c hPro).map
              (eX.functor.map (G.map (eY.unitIso.inv.app N))) ≫
            cf.inv.app (G.obj N) ≫ eY.functor.map (adjEt.counit.app N)) ∧
      (∀ (hLoc : ∀ K, CategoryTheory.localizingClosure (proEtaleProperty A X) K →
          CategoryTheory.localizingClosure (proEtaleProperty A Y)
            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K))
        (J : (CategoryTheory.localizingClosure (proEtaleProperty A Y)).FullSubcategory ⥤
          (CategoryTheory.localizingClosure (proEtaleProperty A X)).FullSubcategory)
        (adjBrown : localizingLowerShriek A c hLoc ⊣ J),
        ∃ hJ : ∀ N : (proEtaleProperty A Y).FullSubcategory,
            proEtaleProperty A X ((J.obj ((toLocalizing A Y).obj N)).obj),
          ∃! γ : (eY.inverse ⋙ G ⋙ eX.functor) ≅ brownRestriction A J hJ,
            ∀ N : (proEtaleProperty A Y).FullSubcategory,
              (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
                  ((γ.hom.app N).hom) ≫
                (adjBrown.counit.app ((toLocalizing A Y).obj N)).hom =
              (adjPro.counit.app N).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.AdjunctionTransfer
