/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeoCartierCanonicalClass
public import WeilConjectures.SecSmoothPurity.TransportFiniteLineDerived
public import WeilConjectures.SecSmoothPurity.TransportFiniteSupport
public import WeilConjectures.AlgebraicGeometry.CompactSupportExchangeTransport
public import WeilConjectures.SecSmoothPurity.TransportLinePull
public import WeilConjectures.SecSmoothPurity.TransportScalarLines
public import WeilConjectures.SixFunctors.CondensedCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.AlgebraicGeometry.GeometricPointProperCoefficientExchange
public import WeilConjectures.AlgebraicGeometry.PurityDivisorClass
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.AlgebraicGeometry.TowerClassSystems
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal

/-! # Condensed Cartier classes and normalized compact-support exchange

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Steps 1 and 3
(blueprint: lem-pur-condensed-cartier-compact-exchange).

The integral normalization below uses the inverse limit of the actual Kummer
sequences and the entire relative pole extension, before extension of scalars.
It does not characterize an integral derived arrow merely by finite evaluations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.CondensedCartier

variable (ell : ℕ) [Fact ell.Prime]

/-- The integral Kummer limit, with both maps specified on every finite projection.
Source: the integral-limit construction in Steps 1 and 3 of the rank-one Thom proof
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
structure IntegralKummer (T : Scheme.{u}) where
  level : ∀ n : ℕ, (tateModuleLevel T ell (n + 1)).X ≅
    Scheme.proEtaleRootsOfUnitySheaf T (ell ^ (n + 1))
  level_normalized : ∀ n : ℕ,
    (level n).inv = (rootComparison T (ell ^ (n + 1))).inv ≫
      (λ_ (rootsOfUnitySheaf T (ell ^ (n + 1)))).inv ≫
      η[condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) T] ▷ _
  inclusion : (tateModule T ell).X ⟶ limit (SpTowerClasses.powerUnits ell T)
  inclusion_normalized : ∀ n : ℕ,
    inclusion ≫ limit.π (SpTowerClasses.powerUnits ell T) (op n) =
      (limit.π (tateModuleSystem T ell) (op (n + 1))).hom ≫ (level n).hom ≫
        Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1))
  projection : limit (SpTowerClasses.powerUnits ell T) ⟶ Scheme.proEtaleUnitsSheaf T
  projection_normalized : projection =
    limit.π (SpTowerClasses.powerUnits ell T) (op 0) ≫ Scheme.proEtaleUnitsPower T ell
  zero : inclusion ≫ projection = 0
  exact : (ShortComplex.mk inclusion projection zero).ShortExact

/-- The integral supported constant on the pro-etale site, already used by the
Cartier boundary. Source: the relative frame extension in Step 1
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
abbrev integralConstant (X : Scheme.{u}) :=
  (constantSheaf (ProEt.topology X) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The coefficient unit sends the integral section one to the ring section one.
Source: the scalar extension in Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def generator (c : Coefficient ell) (X : Scheme.{u}) :
    integralConstant X ⟶ condensedRingObj (c.obj ell) X :=
  (Functor.Monoidal.εIso (constantSheaf (ProEt.topology X) Ab.{u + 1})).inv ≫ η

/-- The supported unit, before deriving. Source: the source of c_D in Step 1
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
abbrev sourceModule (c : Coefficient ell) {D T : Scheme.{u}} (i : D ⟶ T) :=
  (CondensedRing.lowerStar (c.obj ell) i).obj (c.line ell D 0)

/-- Degree-two module Ext is the canonical single-to-shifted-single derived Hom.
Source: the displayed supported Cartier arrow in Step 1
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
abbrev Class (c : Coefficient ell) {D T : Scheme.{u}} (i : D ⟶ T) :=
  Ext (sourceModule ell c i) (c.line ell T 1) 2

/-- The actual scalar insertion into the shifted Tate line. Source: Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def rootInsertion (c : Coefficient ell) (T : Scheme.{u}) :
    (tateModule T ell).X ⟶ (c.line ell T 1).X :=
  (Mod.extendUnit (coefficientMap (c.integralMap ell) T) (tateModule T ell)).hom ≫
    (λ_ (c.firstLine ell T)).inv.hom

/-- Full-boundary normalization: the pole extension followed by the positive
integral Kummer boundary, with the canonical scalar insertion. This fixes the
local sign -∂κ(f) without choosing local lifts or testing only finite reductions.
Source: Steps 1 and 3 and lem-pur-divisor-class
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def Normalized {T D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (K : IntegralKummer ell T)
    (c : Coefficient ell) (a : Class ell c i) : Prop :=
  cartierScalarBoundaryEquation (Mod.forget (condensedRingObj (c.obj ell) T))
    ((ProEtale.lowerStar Ab.{u + 1} i).map (generator ell c D)) a
    (cartierProBoundary i (Etale.cartierPoleBoundary i hI))
    (cartierKummerClass K.exact (rootInsertion ell c T))

/-- The supported class as an actual morphism in the ordinary derived category.
Source: Step 1 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
abbrev classArrow {c : Coefficient ell} {D T : Scheme.{u}} {i : D ⟶ T}
    (a : Class ell c i) := a.hom

/-- Compact image on the actual proper/open compactification model.
Source: Step 3 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def compactArrow {c : Coefficient ell} {D T S : Scheme.{u}}
    {i : D ⟶ T} {f : T ⟶ S} (cf : Compactification f) (a : Class ell c i) :=
  (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cf).map (classArrow ell a)

/-- The closed source comparison is the ordinary adjunction mate, followed by
pullback of the unit; it is not an unspecified isomorphism.
Source: Step 3 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def sourcePull {c : Coefficient ell} {D T D' T' : Scheme.{u}}
    {i : D ⟶ T} {i' : D' ⟶ T'} {h : T' ⟶ T} {d : D' ⟶ D}
    (sq : CommSq d i' i h) :
    (actualPull (c.obj ell) h).obj
        ((DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i') :=
  ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) h).app _).hom ≫
    ((CondensedRing.upperStar (c.obj ell) h).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
    (DerivedCategory.singleFunctor _ 0).map
      ((CondensedRing.lowerStarBaseChange (c.obj ell) sq).app (c.line ell D 0) ≫
        (CondensedRing.lowerStar (c.obj ell) i').map
          (Functor.Monoidal.εIso (CondensedRing.upperStar (c.obj ell) d)).inv)

/-- Exchange on an arbitrary base square, with its proper factor and normalized
open factor displayed. Source: Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def compactExchange (c : Coefficient ell) {T S T' S' : Scheme.{u}}
    {f : T ⟶ S} {f' : T' ⟶ S'} {h : T' ⟶ T} {g : S' ⟶ S}
    (sq : IsPullback h f' f g) (cf : Compactification f)
    (o : actualOpen (c.obj ell) cf.i ⋙
        actualPull (c.obj ell) (pullback.fst cf.g g) ≅
      actualPull (c.obj ell) h ⋙ actualOpen (c.obj ell) (cf.ofIsPullback sq).i)
    (K : c.derived ell T) :=
  (condensedAmbientExchange (c.obj ell)
      (CompactSupportComposition.square (cf.isPullback_g_ofIsPullback sq).flip)).app
        ((actualOpen (c.obj ell) cf.i).obj K) ≫
    (actualPush (c.obj ell) (cf.ofIsPullback sq).g).map (o.hom.app K)


/-- Pullback of the degree-zero coefficient unit, fixed by the monoidal unit.
Source: Step 3 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def unitPull (c : Coefficient ell) {X Y : Scheme.{u}} (h : X ⟶ Y) :
    (actualPull (c.obj ell) h).obj (unit ell c Y) ≅ unit ell c X :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) h).app _ ≪≫
    ((CondensedRing.upperStar (c.obj ell) h).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Functor.Monoidal.εIso (CondensedRing.upperStar (c.obj ell) h)).symm

/-- The ordinary supported scalar unit, including the direct-image/scalar square.
Source: Step 3 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def sourceScalarUnit {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell) {D T : Scheme.{u}} (i : D ⟶ T) :
    sourceModule ell c i ⟶
      (Mod.comap (coefficientMap a.hom.hom T)).obj (sourceModule ell c' i) :=
  (CondensedRing.lowerStar (c.obj ell) i).map
      (Mod.comapUnitHom (coefficientMap a.hom.hom D)) ≫
    (CondensedRing.comapLowerStarIso a.hom.hom i).inv.app (c'.line ell D 0)

/-- The derived scalar source map is the adjunct of the full supported unit.
Source: Step 3 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def sourceScalarMap {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell) {D T : Scheme.{u}} (i : D ⟶ T) :
    (scalarSixChange a T).obj
        ((DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c' i) :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap a.hom.hom T)).homEquiv _ _ |>.symm <|
      (DerivedCategory.singleFunctor _ 0).map (sourceScalarUnit ell a i) ≫
        ((Mod.comap (C := Sheaf (ProEt.topology T) Ab.{u + 1})
          (coefficientMap a.hom.hom T)).mapDerivedCategorySingleFunctor 0).inv.app
            (sourceModule ell c' i)

/-- Forgetting compact support uses the open unit and the fixed direct-image
compositor. The equation on u specifies the inverse of the open unit.
Source: proper/composition normalization in Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def supportToOrdinary (c : Coefficient ell) {T S : Scheme.{u}} {f : T ⟶ S}
    (cf : Compactification f) (K : c.derived ell T)
    (u : (CondensedRing.upperStar (c.obj ell) cf.i).mapDerivedCategory.obj
      ((actualOpen (c.obj ell) cf.i).obj K) ≅ K) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cf).obj K ⟶
      (actualPush (c.obj ell) f).obj K :=
  (actualPush (c.obj ell) cf.g).map
      ((exactAdjunction (c.obj ell) cf.i).homEquiv _ _ u.hom) ≫
    (lowerComp (c.obj ell) cf.i cf.g).inv.app K ≫
    (Functor.rightDerivedFunctorNatIso
      (CondensedRing.lowerStarCongr (c.obj ell) cf.comm.symm)).hom.app K

/-- The proper section unit is the adjoint of pullback of one followed by the
closed direct-image unit. It fixes the scalar of the section identification.
Source: proper/composition normalization in Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def sectionUnit (c : Coefficient ell) {T S : Scheme.{u}} (f : T ⟶ S) (i : S ⟶ T) :
    unit ell c S ⟶ (actualPush (c.obj ell) f).obj
      ((DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i)) :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction (c.obj ell) f).homEquiv _ _ <|
    (unitPull ell c f).hom ≫
      (DerivedCategory.singleFunctor _ 0).map
        (Functor.LaxMonoidal.ε (CondensedRing.lowerStar (c.obj ell) i))

/-- Underived closed direct image into total direct image, fixed as the
adjunct of the ordinary closed counit under the exact inverse-image comparison.
Source: composition normalization, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def closedSingleMap (c : Coefficient ell) {D T : Scheme.{u}} (i : D ⟶ T) :
    (DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i) ⟶
      (actualPush (c.obj ell) i).obj (unit ell c D) :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction (c.obj ell) i).homEquiv _ _ <|
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) i).hom.app _ ≫
      ((CondensedRing.upperStar (c.obj ell) i).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((CondensedRing.upperStarLowerStarAdjunction (c.obj ell) i).counit.app (c.line ell D 0))

/-- The proper/composition source map uses forgetting compact support, the
closed direct-image comparison and the fixed total direct-image compositor.
Source: composition normalization, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def properSourceMap (c : Coefficient ell) {D T S : Scheme.{u}}
    (i : D ⟶ T) {f : T ⟶ S} (cf : Compactification f)
    (u : (CondensedRing.upperStar (c.obj ell) cf.i).mapDerivedCategory.obj
      ((actualOpen (c.obj ell) cf.i).obj
        ((DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i))) ≅
      (DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i)) :=
  supportToOrdinary ell c cf _ u ≫
    (actualPush (c.obj ell) f).map (closedSingleMap ell c i) ≫
    (CondensedRing.rightDerivedLowerStarComp (c.obj ell) i f).hom.app (unit ell c D)

/-- Canonical proper-support coordinates on the compact source. Every map is
fixed by a displayed adjunction or composition equation.
Source: composition normalization, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
structure ProperSourceCoordinate (c : Coefficient ell) {D T S : Scheme.{u}}
    (i : D ⟶ T) {f : T ⟶ S} (cf : Compactification f) where
  openUnit : (CondensedRing.upperStar (c.obj ell) cf.i).mapDerivedCategory.obj
      ((actualOpen (c.obj ell) cf.i).obj
        ((DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i))) ≅
      (DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i)
  openUnit_normalized : openUnit.inv =
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (c.obj ell) cf.i).unit.app
        ((DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i))
  iso : (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cf).obj
      ((DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i)) ≅
      (actualPush (c.obj ell) (i ≫ f)).obj (unit ell c D)
  normalized : iso.hom = properSourceMap ell c i cf openUnit

/-- The finite-coordinate realization of the supported source, with no change of
its underlying sections. Source: finite coefficient interpretation, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def finiteSourceIso (A : CommRingCat.{0}) [fin : Finite A] (n : ℕ)
    (hA : (ell ^ (n + 1) : A) = 0) {D T : Scheme.{u}} (i : D ⟶ T)
    (hD : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(D, ⊤)))
    (p : FiniteLineCoordinates ell A fin n hA D hD) :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  (finiteEncodingPush A i).app (Coefficient.line ell (.finite A fin n hA) D 0) ≪≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).mapIso p.unit

/-- The finite-coordinate realization of the Tate target, normalized at the
annihilating root level. Source: finite coefficient interpretation, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def finiteTargetIso (A : CommRingCat.{0}) [fin : Finite A] (n : ℕ)
    (hA : (ell ^ (n + 1) : A) = 0) (T : Scheme.{u})
    (hT : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (p : FiniteLineCoordinates ell A fin n hA T hT) :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  (finiteEncoding A T).inverse.mapIso
      ((λ_ ((Coefficient.finite A fin n hA).firstLine ell T)) ≪≫ p.line) ≪≫
    (finiteEncoding A T).unitIso.symm.app _

/-- Agreement with the signed Cartier class supplied by the recorded divisor
construction, as an equality of module Ext classes, before taking compact image.
Source: Steps 1 and 3 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def FiniteNormalized (A : CommRingCat.{0}) [fin : Finite A] (n : ℕ)
    (hA : (ell ^ (n + 1) : A) = 0) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hD : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(D, ⊤)))
    (hT : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (a : Class ell (.finite A fin n hA) i) : Prop :=
  ∃ pD : FiniteLineCoordinates ell A fin n hA D hD,
  ∃ pT : FiniteLineCoordinates ell A fin n hA T hT,
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  ((Ext.mk₀ (finiteSourceIso ell A n hA i hD pD).inv).comp
      (a.mapExactFunctor (finiteEncoding A T).inverse) (zero_add 2)).comp
        (Ext.mk₀ (finiteTargetIso ell A n hA T hT pT).hom) (add_zero 2) =
    geoCartierCanonicalClass (ULift.{u + 1} A) (ell ^ (n + 1))
      (pow_pos (Fact.out : ell.Prime).pos _) (finiteLiftAnnihilator ell A n hA) i hI hT


/-- Precisely the coefficient presentations R/pi^m, R, F and Qbar. The redundant
Zell and Qell constructors are their degree-one finite-extension cases.
Source: coefficient paragraph, Steps 1 and 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def Allowed : Coefficient ell → Prop
  | .finite A _ _ _ => ∃ (E : PadicAlgCl.FiniteIntermediateField ell)
      (π : PadicAlgCl.integers ell E.1),
      Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E.1) ∧
      ∃ m : ℕ, Nonempty (A ≃+* completedResidue ell E π m)
  | .integers | .rationals | .integral _ | .rational _ | .closure => True

/-- A simultaneous family of supported arrows. Values outside the hypotheses
carry no property; this indexing permits the same arrow to occur in every square.
Source: compatible classes, Steps 1 and 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
abbrev Family := ∀ (c : Coefficient ell) {D T : Scheme.{u}} (i : D ⟶ T), Class ell c i

/-- Retained etale antecedents for a whole arrow, using the recorded witness
rather than only asserting that its endpoints descend.
Source: finite etale-origin clause, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
structure ArrowOrigin (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {K L : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))}
    (a : K ⟶ L) where
  source : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))
  target : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))
  sourceIso : source.obj ≅ K
  targetIso : target.obj ≅ L
  sourceWitness : Scheme.FixedEtaleOriginWitness X A source
  targetWitness : Scheme.FixedEtaleOriginWitness X A target
  arrow : sourceWitness.complex ⟶ targetWitness.complex
  equation : sourceWitness.iso.hom ≫ sourceIso.hom ≫ a =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map arrow.hom ≫
      targetWitness.iso.hom ≫ targetIso.hom

/-- The same whole-arrow witness in the internal finite-module coordinates.
Source: finite coefficient interpretation, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def HasOrigin (c : Coefficient ell) (X : Scheme.{u})
    {K L : c.derived ell X} (a : K ⟶ L) : Prop :=
  match c, K, L, a with
  | .finite A fin _ _, _, _, a =>
    letI : Finite A := fin
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    Nonempty (ArrowOrigin (ULift.{u + 1} A) X ((finiteEncodingDerived A X).inverse.map a))
  | _, _, _, _ => True

/-- Transport an etale endpoint through the actual finite encoding and the
proper/open site comparison. This specifies the compact-image witness.
Source: finite etale-origin clause, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def finiteCompactEndpoint (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A]
    {T S : Scheme.{u}} {f : T ⟶ S} (cf : Compactification f)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) T)))
    (L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory.obj L.obj ≅
      (finiteEncodingDerived A T).inverse.obj K) :=
  (finiteEncodingSupport A cf).app K ≪≫
    (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) cf).mapIso e.symm ≪≫
    (ProEtale.compactSupportSiteComparison (ULift.{u + 1} A) cf).app L

/-- A whole-arrow origin and its literal compact-image transport, with the same
antecedent and endpoint isomorphisms on both sides of the displayed equation.
Source: finite etale-origin clause, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def CompactOrigin (c : Coefficient ell) {T S : Scheme.{u}} {f : T ⟶ S}
    (cf : Compactification f) {K L : c.derived ell T} (a : K ⟶ L) : Prop :=
  match c, K, L, a with
  | .finite A fin _ _, K, L, a =>
    letI : Finite A := fin
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    ∃ O : ArrowOrigin (ULift.{u + 1} A) T ((finiteEncodingDerived A T).inverse.map a),
      let eK := finiteCompactEndpoint A cf K O.sourceWitness.complex
        (O.sourceWitness.iso ≪≫ O.sourceIso)
      let eL := finiteCompactEndpoint A cf L O.targetWitness.complex
        (O.targetWitness.iso ≪≫ O.targetIso)
      (finiteEncodingDerived A S).inverse.map
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (Profinite.continuousMapRingObj A) cf).map a) ≫ eL.hom =
        eK.hom ≫
          (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) S).mapDerivedCategory.map
              ((Etale.rightDerivedLowerShriekOfCompactification
                (ModuleCat.{u + 1} (ULift.{u + 1} A)) cf).map O.arrow.hom)
  | _, _, _, _ => True

/-- Finite encoding of total inverse image, with both exact-to-total
comparisons fixed by the published derived functors.
Source: finite exchange transport, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def finitePullDerivedIso (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A]
    {X Y : Scheme.{u}} (h : X ⟶ Y) :
    actualPull (Profinite.continuousMapRingObj A) h ⋙ (finiteEncodingDerived A X).inverse ≅
      (finiteEncodingDerived A Y).inverse ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) h).leftDerivedFunctor :=
  Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj A) h) (finiteEncodingDerived A X).inverse ≪≫
    (Functor.mapDerivedCategoryCompIso
      (CondensedRing.upperStar (Profinite.continuousMapRingObj A) h)
      (finiteEncoding A X).inverse).symm ≪≫
    Functor.mapDerivedCategoryNatIso (finiteEncodingPull A h).symm ≪≫
    Functor.mapDerivedCategoryCompIso (finiteEncoding A Y).inverse
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) h) ≪≫
    Functor.isoWhiskerLeft (finiteEncodingDerived A Y).inverse
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) h).symm

/-- The actual internal exchange is the fixed-module exchange under the finite
encoding. The latter is the comparison image of the etale exchange by the
recorded compactSupport_exchange_transport equation, at the retained witnesses.
Source: finite exchange transport, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def FiniteExchange (c : Coefficient ell) {T S T' S' : Scheme.{u}}
    {f : T ⟶ S} {f' : T' ⟶ S'} {h : T' ⟶ T} {g : S' ⟶ S}
    (sf : IsPullback h f' f g) (cf : Compactification f) :
    (actualOpen (c.obj ell) cf.i ⋙
        actualPull (c.obj ell) (pullback.fst cf.g g) ≅
      actualPull (c.obj ell) h ⋙ actualOpen (c.obj ell) (cf.ofIsPullback sf).i) →
    c.derived ell T → Prop :=
  match c with
  | .finite A fin n hA => fun o K ↦
    letI : Finite A := fin
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    let R := Profinite.continuousMapRingObj A
    let M := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let H := (finiteEncodingDerived A T).inverse
    let F' := ProEtale.rightDerivedLowerShriekOfCompactification M (cf.ofIsPullback sf)
    let eSource := (finitePullDerivedIso A g).app
        ((CondensedRing.rightDerivedLowerShriekOfCompactification R cf).obj K) ≪≫
      (ProEtale.upperStar M g).leftDerivedFunctor.mapIso ((finiteEncodingSupport A cf).app K)
    let eTarget := (finiteEncodingSupport A (cf.ofIsPullback sf)).app
        ((actualPull R h).obj K) ≪≫ F'.mapIso ((finitePullDerivedIso A h).app K)
    (finiteEncodingDerived A S').inverse.map
        (compactExchange ell (.finite A fin n hA) sf cf o K) ≫ eTarget.hom =
      eSource.hom ≫
        (ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap M sf cf).app (H.obj K)
  | _ => fun _ _ ↦ True

/-- Normalize each family member by the full integral Kummer boundary and, at
finite coefficients, by the existing signed divisor class in module Ext.
Source: Steps 1 and 3 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def ClassProperties (C : Family.{u} ell) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) : Prop :=
  (∃ K : IntegralKummer ell T,
    ∀ (c : Coefficient ell), Allowed ell c → Normalized ell i hI K c (C c i)) ∧
  (∀ (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ) (hA : (ell ^ (n + 1) : A) = 0),
    Allowed ell (.finite A fin n hA) →
    letI : Finite A := fin
    ∃ hD : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(D, ⊤)),
    ∃ hT : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(T, ⊤)),
      FiniteNormalized ell A n hA i hI hD hT (C (.finite A fin n hA) i))

/-- Both endpoints of the actual compact image are bounded constructible.
Source: Step 3 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def CompactProperties (C : Family.{u} ell) {D T S : Scheme.{u}}
    (i : D ⟶ T) {f : T ⟶ S} (cf : Compactification f) : Prop :=
  ∀ (c : Coefficient ell), Allowed ell c →
    boundedConstructible (condensedRingObj (c.obj ell) S)
      ((CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cf).obj
        ((DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i))) ∧
    boundedConstructible (condensedRingObj (c.obj ell) S)
      ((CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cf).obj
        (c.derivedLine ell T 1)) ∧
    HasOrigin ell c T (classArrow ell (C c i)) ∧
    HasOrigin ell c S (compactArrow ell cf (C c i)) ∧
    CompactOrigin ell c cf (classArrow ell (C c i))

/-- The same supported arrow and compact image commute with the actual ordinary
(noncompleted) derived scalar functor and proper/open scalar mate. This covers
all reductions and successive coefficient-field extensions.
Source: Step 3 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def ScalarProperties (C : Family.{u} ell) {D T S : Scheme.{u}}
    (i : D ⟶ T) {f : T ⟶ S} (cf : Compactification f) : Prop :=
  ∀ (c c' : Coefficient ell) (a : c.bundled.{u} ell ⟶ c'.bundled ell),
    Allowed ell c → Allowed ell c' → IsListedScalarCoefficientMap ell a →
    ∃ ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell,
    ∃ p : ScalarLineCoordinates ell a ha T,
    let X := (DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i)
    let Y := c.derivedLine ell T 1
    let F' := CondensedRing.rightDerivedLowerShriekOfCompactification (c'.obj ell) cf
    let sx := sourceScalarMap ell a i
    let sy := scalarLineMap ell a T 1 (p.power 1)
    IsIso sx ∧ IsIso sy ∧
    (scalarSixChange a T).map (classArrow ell (C c i)) ≫ sy =
      sx ≫ classArrow ell (C c' i) ∧
    IsIso ((scalarSupportMap a cf).app X) ∧
    IsIso ((scalarSupportMap a cf).app Y) ∧
    (scalarSixChange a S).map (compactArrow ell cf (C c i)) ≫
        (scalarSupportMap a cf).app Y ≫ F'.map sy =
      (scalarSupportMap a cf).app X ≫ F'.map sx ≫ compactArrow ell cf (C c' i) ∧
    HasOrigin ell c' T sx ∧ HasOrigin ell c' T sy ∧
    HasOrigin ell c' S ((scalarSupportMap a cf).app X) ∧
    HasOrigin ell c' S ((scalarSupportMap a cf).app Y)

/-- The canonical proper/open exchange, with both endpoint isomorphisms and the
class and compact-image equations. Cartier preservation and normalization of the
restricted class are conclusions, also at a non-finite-type geometric point.
Source: Step 3 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def BaseChangeProperties (C : Family.{u} ell) {D T S D' T' S' : Scheme.{u}}
    {i : D ⟶ T} {f : T ⟶ S} {i' : D' ⟶ T'} {f' : T' ⟶ S'}
    {d : D' ⟶ D} {h : T' ⟶ T} {g : S' ⟶ S}
    (si : IsPullback d i' i h) (sf : IsPullback h f' f g)
    (cf : Compactification f) : Prop :=
  ∃ hi' : IsClosedImmersion i',
  letI := hi'
  ∃ hI' : i'.ker.IsInvertible,
    ClassProperties ell C i' hI' ∧ CompactProperties ell C i' (cf.ofIsPullback sf) ∧
    ScalarProperties ell C i' (cf.ofIsPullback sf) ∧
    ∀ (c : Coefficient ell), Allowed ell c →
    ∃ p : LinePullCoordinates ell c h,
    ∃ o : actualOpen (c.obj ell) cf.i ⋙
        actualPull (c.obj ell) (pullback.fst cf.g g) ≅
      actualPull (c.obj ell) h ⋙ actualOpen (c.obj ell) (cf.ofIsPullback sf).i,
    ∃ q : ProperSourceCoordinate ell c i cf,
    ∃ q' : ProperSourceCoordinate ell c i' (cf.ofIsPullback sf),
    o.inv = CompactSupportComposition.openExchange (c.obj ell) sf cf ∧
    let X := (DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i)
    let Y := c.derivedLine ell T 1
    let F' := CondensedRing.rightDerivedLowerShriekOfCompactification
      (c.obj ell) (cf.ofIsPullback sf)
    let sx := sourcePull ell (c := c) si.toCommSq
    let sy := (p.derived ell 1).hom
    IsIso sx ∧
    (actualPull (c.obj ell) g).map q.iso.hom ≫
        (condensedAmbientExchange (c.obj ell)
          (CompactSupportComposition.square (si.paste_vert sf))).app (unit ell c D) ≫
        (actualPush (c.obj ell) (i' ≫ f')).map (unitPull ell c d).hom =
      compactExchange ell c sf cf o X ≫ F'.map sx ≫ q'.iso.hom ∧
    HasOrigin ell c S q.iso.hom ∧ HasOrigin ell c S' q'.iso.hom ∧
    IsIso (compactExchange ell c sf cf o X) ∧
    IsIso (compactExchange ell c sf cf o Y) ∧
    (actualPull (c.obj ell) h).map (classArrow ell (C c i)) ≫ sy =
      sx ≫ classArrow ell (C c i') ∧
    (actualPull (c.obj ell) g).map (compactArrow ell cf (C c i)) ≫
        compactExchange ell c sf cf o Y ≫ F'.map sy =
      compactExchange ell c sf cf o X ≫ F'.map sx ≫
        compactArrow ell (cf.ofIsPullback sf) (C c i') ∧
    HasOrigin ell c T' sx ∧ HasOrigin ell c T' sy ∧
    HasOrigin ell c S' (compactExchange ell c sf cf o X) ∧
    HasOrigin ell c S' (compactExchange ell c sf cf o Y) ∧
    FiniteExchange ell c sf cf o X ∧ FiniteExchange ell c sf cf o Y

/-- A section identification is normalized by its image in ordinary direct
image: its inverse maps to the adjunction section unit. This determines the
proper/composition isomorphism rather than an arbitrary scalar multiple.
Source: section paragraph, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
structure SectionCoordinate (c : Coefficient ell) {T S : Scheme.{u}} {f : T ⟶ S}
    (i : S ⟶ T) (cf : Compactification f) where
  openUnit : (CondensedRing.upperStar (c.obj ell) cf.i).mapDerivedCategory.obj
      ((actualOpen (c.obj ell) cf.i).obj
        ((DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i))) ≅
      (DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i)
  openUnit_normalized : openUnit.inv =
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (c.obj ell) cf.i).unit.app
        ((DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i))
  iso : (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cf).obj
      ((DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i)) ≅ unit ell c S
  normalized : iso.inv ≫ supportToOrdinary ell c cf _ openUnit = sectionUnit ell c f i

/-- The two base domains in the node: separated finite-type schemes over k,
with their induced structural map, and arbitrary algebraically closed points.
Source: base-change paragraphs, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def AllowedBase (F : WeilConjectures.FiniteFieldDatum.{u}) (S : SepFinType F.k)
    (S' : Scheme.{u}) (g : S' ⟶ S.obj.left) : Prop :=
  (LocallyOfFiniteType (g ≫ S.obj.hom) ∧ QuasiCompact (g ≫ S.obj.hom) ∧
    IsSeparated (g ≫ S.obj.hom)) ∨
  ∃ (Ω : Type u) (inst : Field Ω),
    letI := inst
    IsAlgClosed Ω ∧ Nonempty (S' ≅ Spec (.of Ω))

/-- The normalized section comparison turns source exchange into unit pullback
and respects every listed coefficient change. All its finite instances retain
whole-arrow etale origins.
Source: section and coefficient paragraphs, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def SectionProperties {T S : Scheme.{u}} {f : T ⟶ S}
    (allowed : ∀ (S' : Scheme.{u}), (S' ⟶ S) → Prop)
    (i : S ⟶ T) (cf : Compactification f) : Prop :=
  ∀ (c : Coefficient ell), Allowed ell c →
    ∃ q : SectionCoordinate ell c i cf,
    HasOrigin ell c S q.iso.hom ∧
    (∀ {T' S' : Scheme.{u}} {f' : T' ⟶ S'} {h : T' ⟶ T} {g : S' ⟶ S},
      allowed S' g →
      ∀ (i' : S' ⟶ T') (si : IsPullback g i' i h) (sf : IsPullback h f' f g),
      ∃ o : actualOpen (c.obj ell) cf.i ⋙
          actualPull (c.obj ell) (pullback.fst cf.g g) ≅
        actualPull (c.obj ell) h ⋙ actualOpen (c.obj ell) (cf.ofIsPullback sf).i,
      o.inv = CompactSupportComposition.openExchange (c.obj ell) sf cf ∧
      ∃ q' : SectionCoordinate ell c i' (cf.ofIsPullback sf),
      compactExchange ell c sf cf o
          ((DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i)) ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c.obj ell) (cf.ofIsPullback sf)).map (sourcePull ell (c := c) si.toCommSq) ≫
          q'.iso.hom = (actualPull (c.obj ell) g).map q.iso.hom ≫ (unitPull ell c g).hom) ∧
    (∀ (c' : Coefficient ell) (a : c.bundled.{u} ell ⟶ c'.bundled ell),
      Allowed ell c' → IsListedScalarCoefficientMap ell a →
      ∃ ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell,
      ∃ p : ScalarLineCoordinates ell a ha S,
      ∃ q' : SectionCoordinate ell c' i cf,
      (scalarSixChange a S).map q.iso.hom ≫ scalarLineZero ell a S 0 (p.power 0) =
        (scalarSupportMap a cf).app
            ((DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i)) ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification (c'.obj ell) cf).map
            (sourceScalarMap ell a i) ≫ q'.iso.hom)

/-- The exact geometric hypotheses of the compact Cartier assertion.
Source: Steps 1 and 3 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
structure Datum (k : Type u) [Field k] where
  S : SepFinType k
  T : SepFinType k
  D : SepFinType k
  f : T ⟶ S
  i : D ⟶ T
  [smooth : Smooth f.hom.left]
  [separated : IsSeparated f.hom.left]
  [finiteType : LocallyOfFiniteType f.hom.left]
  [quasiCompact : QuasiCompact f.hom.left]
  [closed : IsClosedImmersion i.hom.left]
  cartier : i.hom.left.ker.IsInvertible
  [divisorSmooth : Smooth (i.hom.left ≫ f.hom.left)]
  [divisorProper : IsProper (i.hom.left ≫ f.hom.left)]

attribute [instance] Datum.smooth Datum.separated Datum.finiteType Datum.quasiCompact
  Datum.closed Datum.divisorSmooth Datum.divisorProper

/-- Condensed Cartier classes, compact images and normalized exchanges, with all
coefficient and origin compatibilities in the ordinary derived categories.

Source: the latest rank-one Thom proof, Steps 1 and 3
(blueprint: lem-pur-condensed-cartier-compact-exchange).

Proof in words. Smoothness makes D/S flat, so the Cartier ideal stays invertible
under all indicated pullbacks. At finite coefficients take the relative pole
extension followed by the positive Kummer boundary; its section off D fixes the
local sign -boundary(kappa(f)). Form the compatible Kummer tower on the pro-etale
site and take its exact inverse limit. The projection-normalized identification
of its kernel with the Tate module gives IntegralKummer. The Yoneda product with
the relative pole boundary and the full scalar adjunct gives the integral class;
its finite reductions are the signed finite class. Extend scalars using the
closed support projection formula to obtain the rational and closure classes.
The source has its two-stratum constructible description and is flat; the Tate
line is locally free. Compact support preserves bounded constructibility on
these inputs. Pullback of the entire relative extension and Kummer tower gives
the class equation. Naturality of the proper/open exchange then gives the
compact-image equation; the composition exchange law identifies its source
with the exchange for fi. When fi is the identity, its adjunction unit gives
the displayed section normalization and the exchange becomes the unit pullback.
At finite coefficients use the etale relative extension as a whole-arrow origin;
exact open comparison and the proper counit mate transport this witness and its
exchange. For an arbitrary geometric point apply proper coefficient exchange
after open extension: the integral inputs are derived complete with uniformly
bounded finite etale-origin reductions, and rational/closure inputs follow by
scalar extension. Finally scalar functoriality and the proper/open scalar mate
give the reduction and coefficient-field identities, including their section
normalizations. No step claims that the supported class or its compact image
is an isomorphism. -/
theorem condensed_cartier_compact_exchange (F : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ F.p) :
    ∃ C : Family.{u} ell,
      (∀ (s : Datum F.k) (cf : Compactification s.f.hom.left),
        ClassProperties ell C s.i.hom.left s.cartier ∧
        CompactProperties ell C s.i.hom.left cf ∧ ScalarProperties ell C s.i.hom.left cf ∧
        (∀ (S' : SepFinType F.k) (g : S' ⟶ s.S)
          {T' D' : Scheme.{u}} {f' : T' ⟶ S'.obj.left} {i' : D' ⟶ T'}
          {h : T' ⟶ s.T.obj.left} {d : D' ⟶ s.D.obj.left}
          (sf : IsPullback h f' s.f.hom.left g.hom.left)
          (si : IsPullback d i' s.i.hom.left h),
          BaseChangeProperties ell C si sf cf) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ s.S.obj.left)
          {T' D' : Scheme.{u}} {f' : T' ⟶ Spec (.of Ω)} {i' : D' ⟶ T'}
          {h : T' ⟶ s.T.obj.left} {d : D' ⟶ s.D.obj.left}
          (sf : IsPullback h f' s.f.hom.left b)
          (si : IsPullback d i' s.i.hom.left h),
          BaseChangeProperties ell C si sf cf)) ∧
      (∀ (s : Datum F.k) (i : s.S.obj.left ⟶ s.T.obj.left)
        [IsClosedImmersion i] (hI : i.ker.IsInvertible) (hs : i ≫ s.f.hom.left = 𝟙 _)
        (cf : Compactification s.f.hom.left), SectionProperties ell (AllowedBase F s.S) i cf) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedCartier
