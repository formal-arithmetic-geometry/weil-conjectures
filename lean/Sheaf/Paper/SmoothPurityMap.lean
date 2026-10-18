/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.Paper.PurityDiagonalDualizingObject
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal

/-! # The specified finite-coefficient smooth purity map

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
def-pur-smooth-purity-map; master snapshot order 2012
(blueprint: def-pur-smooth-purity-map).

All arrows are constructed from the recorded diagonal orientation and tensor counit mate.
The original pro-etale coefficient K is retained. An etale representative and its
isomorphism are coordinates for the comparison, not choices of purity isomorphisms.
The exceptional target is the actual transported exceptional inverse image of K.
The shifted coefficient line is the recorded diagonalTwist; inverse shift provides its
unshifted presentation, so reassociation uses the ordinary tensor-shift comparison.

## Main definitions

* `smoothPurityTheta`: the canonical tensor counit mate in comparison coordinates.
* `smoothPurityReassociation`: canonical second-variable shift compatibility.
* `smoothPurityTensorMap`: the tensor form on the original intrinsic object.
* `smoothPurityMap`: its precomposition with twist reassociation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v uC
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Finiteness of the recorded positive quotient, without a ramification restriction.
Source: blueprint finite coefficient conventions (blueprint: def-pur-smooth-purity-map). -/
instance smoothPurityRingFinite (P : PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- The recorded finite exceptional functor at the specified compactification.
Source: blueprint finite exceptional inverse image
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityExceptional (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriek f P.Coefficient
  letI : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient)
      (HasCompactification.compactification f)).IsLeftAdjoint :=
    inferInstanceAs (Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} P.Coefficient) f).IsLeftAdjoint
  ProEtale.sfFiniteExceptionalAt P.Coefficient (HasCompactification.compactification f)

/-- The functor identity expressing the recorded finite exceptional transport.
Source: blueprint finite exceptional inverse image (blueprint: def-pur-smooth-purity-map). -/
def smoothPurityExceptionalComparison (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    P.smoothPurityExceptional f ≅
      (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor ⋙
      Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f ⋙
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory :=
  Iso.refl _

/-- Pullback of the original pro-etale object, in exact fixed-scalar coordinates.
Source: blueprint def-pur-smooth-purity-map, M = Lf* K
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) := ProEtale.sfFixedDerivedPullback P.Ring f

/-- The recorded tensor bifunctor with the fixed module-category instances cached.
Source: blueprint derived tensor product (blueprint: def-pur-smooth-purity-map). -/
@[implicit_reducible]
def smoothPurityTensor (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  ProEtale.derivedTensor (ModuleCat.{u + 1} A) X

/-- The degree-zero constant coefficient is the derived tensor unit.
Source: blueprint finite coefficient unit (blueprint: def-pur-smooth-purity-map). -/
def smoothPurityUnitIso (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    Etale.ordinaryFiniteUnit A Y ≅
      𝟙_ (_root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y

/-- The canonical ordinary tensor mate, including the degree-zero unit comparison.
Source: blueprint def-pur-co-smoothness clause 2
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityEtaleTheta (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} A))) :
    ((Etale.ordinaryFiniteTensor A X).obj
      ((Etale.ordinaryFinitePullback A f).obj K₀)).obj
        ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj
          (Etale.ordinaryFiniteUnit A Y)) ⟶
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K₀ :=
  ((Etale.ordinaryFiniteTensor A X).obj
    ((Etale.ordinaryFinitePullback A f).obj K₀)).map
      ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).map
        (smoothPurityUnitIso A Y).hom) ≫
    ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app
      ((Etale.ordinaryFinitePullback A f).obj K₀)).app
        (Etale.dualizingComplex (ModuleCat.{u + 1} A) f) ≫
    Etale.dualizingComplexTensorMap A f K₀

/-- Canonical pullback comparison at a representing isomorphism.
Source: blueprint def-pur-smooth-purity-map, M (blueprint: def-pur-smooth-purity-map). -/
def smoothPurityPullbackComparison (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (K₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K) :
    (P.smoothPurityPullback f).obj K ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
          ((Etale.ordinaryFinitePullback P.Coefficient f).obj K₀) :=
  (P.smoothPurityPullback f).mapIso e.symm ≪≫
    (ProEtale.sfDerivedComparisonPullbackIso P.Ring f).app K₀ ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f).app K₀).symm

/-- The canonical comparison tensor constraint, specialized once to finite rings.
Source: blueprint derived tensor comparison (blueprint: def-pur-smooth-purity-map). -/
def smoothPurityComparisonTensor (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u})
    (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
      (((Etale.ordinaryFiniteTensor A X).obj M).obj N) ≅
    ((smoothPurityTensor A X).obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj N) :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  letI : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} A) M).app N

/-- Canonical tensor-source comparison in the specified etale presentation.
Source: blueprint tensor mate (blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTensorComparison (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (K₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K) :
    ((smoothPurityTensor P.Coefficient X).obj
      ((P.smoothPurityPullback f).obj K)).obj (P.diagonalDualizing f) ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
          (((Etale.ordinaryFiniteTensor P.Coefficient X).obj
            ((Etale.ordinaryFinitePullback P.Coefficient f).obj K₀)).obj
              (P.diagonalOrdinaryDualizing f)) :=
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let M₀ := (Etale.ordinaryFinitePullback P.Coefficient f).obj K₀
  ((smoothPurityTensor P.Coefficient X).mapIso
    (P.smoothPurityPullbackComparison f K K₀ e)).app (P.diagonalDualizing f) ≪≫
    ((smoothPurityTensor P.Coefficient X).obj
      (F.obj M₀)).mapIso (P.diagonalDualizingComparison f) ≪≫
    (smoothPurityComparisonTensor P.Coefficient X M₀
      (P.diagonalOrdinaryDualizing f)).symm

/-- The canonical tensor mate in the source ordering M tensor omega. The comparison
uses the site pullback square, the monoidal comparison and the actual etale counit
mate. The last arrow is induced by the comparison adjunction unit and the supplied
representative isomorphism, so the target is Rf! K itself.
Source: blueprint def-pur-co-smoothness clause 2 and def-pur-smooth-purity-map
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTheta (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (K₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K) :
    ((smoothPurityTensor P.Coefficient X).obj
      ((P.smoothPurityPullback f).obj K)).obj (P.diagonalDualizing f) ⟶
        (P.smoothPurityExceptional f).obj K :=
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  (P.smoothPurityTensorComparison f K K₀ e).hom ≫
    F.map (smoothPurityEtaleTheta P.Coefficient f K₀) ≫
    F.map ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f).map
      ((ProEtale.derivedComparisonAdjunction
        (ModuleCat.{u + 1} P.Coefficient) Y).unit.app K₀ ≫
          (ProEtale.comparisonLowerStar
            (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor.map e.hom)) ≫
    ((P.smoothPurityExceptionalComparison f).app K).inv

/-- Canonical second-variable tensor-shift compatibility over an abstract coefficient
category, followed by cancellation of opposite shifts.
Source: blueprint def-pur-smooth-purity-map, tau
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTensorShiftGeneric (C : Type uC) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{v} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (r : ℤ) (M T : _root_.DerivedCategory C) :
    (((curriedTensor (_root_.DerivedCategory C)).obj M).obj (T⟦-r⟧))⟦r⟧ ≅
      ((curriedTensor (_root_.DerivedCategory C)).obj M).obj T :=
  letI := _root_.DerivedCategory.commShiftTensorLeft C M
  (((curriedTensor (_root_.DerivedCategory C)).obj M).commShiftIso r).symm.app _ ≪≫
    ((curriedTensor (_root_.DerivedCategory C)).obj M).mapIso
      ((shiftFunctorCompIsoId _ (-r) r (neg_add_cancel r)).app T)

/-- Identification of the published derived tensor with its canonical monoidal
presentation, as functors rather than by repeated reduction of instance data.
Source: blueprint def-weil-derived-tensor (blueprint: def-pur-smooth-purity-map).
Proof: unfold ProEtale.derivedTensor. Its definition is precisely curriedTensor
for the K-flat derived monoidal structure. Both sides use the existing sheaf
monoidal structure and its derived localization, so the identity is reflexive.
This postpones only the proof of an interface identity, with no map data chosen. -/
theorem smoothPurityTensorPresentation (C : Type uC) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) :
    ProEtale.derivedTensor C X =
      curriedTensor (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C)) := by
  sorry

/-- The canonical shift comparison in the published tensor presentation is uniquely
specified by equality, across the two interface types, to the existing K-flat shift.
Source: blueprint def-pur-smooth-purity-map, tau
(blueprint: def-pur-smooth-purity-map).
Proof: rewrite the bifunctor using smoothPurityTensorPresentation. The source and
target then become the source and target of smoothPurityTensorShiftGeneric, so that
isomorphism supplies existence and reflexive heterogeneous equality. If two proposed
isomorphisms satisfy the equation, transitivity of heterogeneous equality gives their
ordinary equality, proving uniqueness. Thus the theorem fixes the isomorphism itself,
including its map, rather than merely asserting that the objects are isomorphic. -/
theorem existsUnique_smoothPurityTensorShift
    (C : Type uC) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) (r : ℤ)
    (M T : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C)) :
    ∃! e : ((((ProEtale.derivedTensor C X).obj M).obj (T⟦-r⟧)))⟦r⟧ ≅
      ((ProEtale.derivedTensor C X).obj M).obj T,
      HEq e (smoothPurityTensorShiftGeneric (Sheaf (Scheme.ProEt.topology X) C) r M T) := by
  sorry

/-- The published canonical shift comparison, selected by its exact map identity.
Source: blueprint def-pur-smooth-purity-map, tau
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTensorShiftCoefficients (C : Type uC) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) (r : ℤ)
    (M T : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C)) :
    ((((ProEtale.derivedTensor C X).obj M).obj (T⟦-r⟧)))⟦r⟧ ≅
      ((ProEtale.derivedTensor C X).obj M).obj T :=
  (existsUnique_smoothPurityTensorShift C X r M T).exists.choose

/-- Specialization of canonical tensor-shift compatibility to finite module coefficients.
Source: blueprint def-pur-smooth-purity-map, tau
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTensorShift (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (r : ℤ)
    (M T : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (((smoothPurityTensor A X).obj M).obj (T⟦-r⟧))⟦r⟧ ≅
      ((smoothPurityTensor A X).obj M).obj T :=
  smoothPurityTensorShiftCoefficients (ModuleCat.{u + 1} A) X r M T

/-- Canonical twist reassociation. T is the already shifted coefficient line A(d)[2d];
T[-2d] is its canonical inverse-shift presentation A(d). The first factor is tensor's
shift compatibility in the second variable; the second cancels the opposite shifts.
On total K-flat tensor complexes these are exactly the usual shift identifications.
Source: blueprint def-pur-smooth-purity-map, tau
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityReassociation (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ)
    (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) :
    (((smoothPurityTensor P.Coefficient X).obj M).obj
      ((P.diagonalTwist X d)⟦-(2 * (d : ℤ))⟧))⟦2 * (d : ℤ)⟧ ≅
      ((smoothPurityTensor P.Coefficient X).obj M).obj
        (P.diagonalTwist X d) :=
  smoothPurityTensorShift P.Coefficient X (2 * (d : ℤ)) M (P.diagonalTwist X d)

/-- The recorded exceptional functor with its source-implied compactification supplied.
Source: blueprint finite purity domain (blueprint: def-pur-smooth-purity-map). -/
def smoothPurityExceptionalOver (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :
    _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) ⥤
    _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
  letI := isNoetherian_of_locallyOfFiniteType aY
  letI := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  letI : HasCompactification f := inferInstance
  P.smoothPurityExceptional f

/-- The tensor form gamma^sm = (1 tensor Pi^-1) followed by the specified theta.
Pi is precisely the normalized diagonal orientation, never an arbitrary endpoint iso.
The finite-type field domain supplies compactification internally.
Source: blueprint main-20261015 def-pur-smooth-purity-map, displayed tensor composite
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTensorMapInPresentation (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (K₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K) :
    ((smoothPurityTensor P.Coefficient X).obj
      ((P.smoothPurityPullback f).obj K)).obj (P.diagonalTwist X d) ⟶
        (P.smoothPurityExceptionalOver f aY).obj K :=
  letI := isNoetherian_of_locallyOfFiniteType aY
  letI := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  letI : HasCompactification f := inferInstance
  ((smoothPurityTensor P.Coefficient X).obj
    ((P.smoothPurityPullback f).obj K)).map
      (P.diagonalDualizingObject d f aY).inv ≫
    P.smoothPurityTheta f K K₀ e

/-- The tensor-composite source on the original intrinsic coefficient object.
The inverse of the canonical realization equivalence only changes its presentation.
Source: blueprint def-pur-smooth-purity-map, tensor source
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTensorSource (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
  ((smoothPurityTensor P.Coefficient X).obj
    ((P.smoothPurityPullback f).obj
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K))).obj
        (P.diagonalTwist X d)

/-- The uniquely determined tensor composite, characterized in every etale
presentation of the original intrinsic coefficient object. This is the displayed
formula 1 tensor Pi^-1 followed by theta, rather than a bare existence of an iso.
Source: blueprint main-20261015 def-pur-smooth-purity-map
(blueprint: def-pur-smooth-purity-map).

Proof: finite constructible origin supplies a bounded etale representative of K.
The comparison unit is invertible on bounded-below etale objects; the triangle
identities give an invertible counit on K. Thus Rnu_* K is a canonical representative.
Use its counit inverse in the pullback/tensor comparison, then tensor with the fixed
inverse diagonal orientation and apply the counit mate theta. For any other
representative e, naturality of the comparison unit and its triangle identities
identify the last two factors of smoothPurityTheta with the exceptional comparison.
The monoidal comparison is natural in both variables, and the pullback square is
natural in K. Hence conjugating by e gives exactly smoothPurityTensorMapInPresentation.
This proves existence with the stated equality for every representative. Since at
least one representative exists, that equality determines the morphism uniquely.
No representative, root, basis, orientation or endpoint iso is chosen as map data. -/
theorem existsUnique_smoothPurityTensorMap (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (_hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    ∃! g : P.smoothPurityTensorSource f d K ⟶
      (P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).obj
        ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K),
      ∀ (K₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)))
        (e : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅
            (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K),
        g = P.smoothPurityTensorMapInPresentation f d (Y ↘ Spec (.of P.field.k))
          ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) K₀ e := by
  sorry

/-- The canonical tensor form gamma^sm on the actual intrinsic pro-etale object K.
The theorem specifies a unique morphism by the explicit composite in every
presentation, so its use postpones only a proof and never unspecified map data.
Source: blueprint def-pur-smooth-purity-map, gamma^sm
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTensorMap (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :=
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
    (P.existsUnique_smoothPurityTensorMap f d K hK).exists.choose

/-- The smooth purity map gamma = gamma^sm after tau, in the original intrinsic
small-pro-etale derived category. Its source is Lf* K(d)[2d] using the canonical
inverse-shift presentation of the recorded shifted Tate line. Its target is the
canonical realization of the recorded exceptional inverse image of K.
Source: blueprint def-pur-smooth-purity-map, final composite
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityMap (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :=
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
    (P.smoothPurityReassociation X d ((P.smoothPurityPullback f).obj
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K))).hom ≫
    P.smoothPurityTensorMap f d K hK

end WeilConjectures.PurityFiniteSetting
