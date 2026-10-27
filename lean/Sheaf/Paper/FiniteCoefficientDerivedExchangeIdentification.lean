/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedAmbientExchange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison
import Sheaf.CategoryTheory.ConstantScalarGeometricAdjunctions
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.Paper.FiniteDiscreteCoefficientSections
import Sheaf.Paper.IntegralFinitePullbackComposition

/-! # Finite coefficient realization of the specified derived exchange

Source: blueprint main-20261015, det-sf-comp-coherence-refinement, proof (2);
Stacks Project, Tags 09AL, 03D7, 03D8 and 09T5
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The recorded termwise realization, with its endpoint categories explicit.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def Encoding.derivedFunctor {T : Scheme.{u}} (e : Encoding A T) :
    DerivedCategory (Internal A T) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
  e.fixedDerived.functor

/-- Total internal pullback for the finite coefficient.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def internalPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Internal A Y) ⥤ DerivedCategory (Internal A X) :=
  CondensedRing.moduleObjectDerivedPullback (coefficient A) f

/-- Total internal direct image for the finite coefficient.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def internalPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Internal A X) ⥤ DerivedCategory (Internal A Y) :=
  CondensedRing.moduleObjectDerivedPushforward (coefficient A) f

/-- Ordinary derived pullback of fixed scalar sheaves.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def ordinaryPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).leftDerivedFunctor

/-- Ordinary derived direct image of fixed scalar sheaves.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def ordinaryPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
  (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctor


/-- Heart realization from the recorded normalized coefficient encoding.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
abbrev Encoding.heart {T : Scheme.{u}} (e : Encoding A T) :=
  e.ordinary.functor ⋙ e.fixed.functor

/-- The existing scalar-forgetting functor.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
abbrev forgetAb (T : Scheme.{u}) :=
  sheafCompose (Scheme.ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1})

/-- The encoding retains the original abelian sheaf.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def Encoding.underlyingIso {T : Scheme.{u}} (e : Encoding A T) :
    e.heart ⋙ forgetAb A T ≅ Mod.forget (condensedRingObj (coefficient A) T) := by
  dsimp only [Encoding.heart]
  rw [e.ordinary_functor, e.fixed_functor]
  exact Iso.refl _

/-- The specified internal derived adjunction, in the named finite specialization.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def internalAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalPull A f ⊣ internalPush A f :=
  CondensedRing.derivedUpperStarLowerStarAdjunction (coefficient A) f

/-- The specified ordinary derived adjunction.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def ordinaryAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryPull A f ⊣ ordinaryPush A f :=
  ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f

/-- The canonical localization factorization of the termwise coefficient functor.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def Encoding.factors {T : Scheme.{u}} (e : Encoding A T) :
    DerivedCategory.Q ⋙ e.derivedFunctor ≅
      e.heart.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  e.heart.mapDerivedCategoryFactors

/-- The actual internal right-derived unit, transported to complex localization.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def internalRightUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar (coefficient A) f).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ internalPush A f :=
  derivedCochainRightUnit (CondensedRing.lowerStar (coefficient A) f) (internalPush A f)
    (CondensedRing.lowerStar (coefficient A) f).rightDerivedFunctorUnit

/-- The actual ordinary right-derived unit, transported to complex localization.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def ordinaryRightUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.mapHomologicalComplex
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f) (.up ℤ)) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ ordinaryPush A f :=
  derivedCochainRightUnit (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
    (ordinaryPush A f)
    (Functor.rightDerivedFunctorUnit
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f))

/-- Normalized edge comparisons retain the actual underlying-sheaf map, right-derived
comparison unit, and the unit and counit of the specified derived adjunctions.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
structure DerivedEdgeComparison {X Y : Scheme.{u}}
    (eX : Encoding A X) (eY : Encoding A Y) (f : X ⟶ Y) where
  heartDirect : CondensedRing.lowerStar (coefficient A) f ⋙ eY.heart ≅
    eX.heart ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  heart_normalization : ∀ M : Internal A X,
    (forgetAb A Y).map (heartDirect.hom.app M) ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map (eX.underlyingIso.hom.app M) =
    eY.underlyingIso.hom.app ((CondensedRing.lowerStar (coefficient A) f).obj M)
  direct : internalPush A f ⋙ eY.derivedFunctor ≅ eX.derivedFunctor ⋙ ordinaryPush A f
  direct_normalization : ∀ P : CochainComplex (Internal A X) ℤ,
    eY.factors.inv.app
        (((CondensedRing.lowerStar (coefficient A) f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      eY.derivedFunctor.map ((internalRightUnit A f).app P) ≫
      direct.hom.app (DerivedCategory.Q.obj P) =
    DerivedCategory.Q.map ((heartDirect.hom.mapHomologicalComplex (.up ℤ)).app P) ≫
      (ordinaryRightUnit A f).app ((eX.heart.mapHomologicalComplex (.up ℤ)).obj P) ≫
      (ordinaryPush A f).map (eX.factors.inv.app P)
  inverse : internalPull A f ⋙ eX.derivedFunctor ≅ eY.derivedFunctor ⋙ ordinaryPull A f
  unit : ∀ M : DerivedCategory (Internal A Y),
    eY.derivedFunctor.map ((internalAdj A f).unit.app M) ≫
        direct.hom.app ((internalPull A f).obj M) =
      (ordinaryAdj A f).unit.app (eY.derivedFunctor.obj M) ≫
        (ordinaryPush A f).map (inverse.inv.app M)
  counit : ∀ N : DerivedCategory (Internal A X),
    eX.derivedFunctor.map ((internalAdj A f).counit.app N) =
      inverse.hom.app ((internalPush A f).obj N) ≫
        (ordinaryPull A f).map (direct.hom.app N) ≫
        (ordinaryAdj A f).counit.app (eX.derivedFunctor.obj N)


/-- The published internal composition map, with its endpoints shared.
Source: Stacks 03D8; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def internalCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    internalPull A (f ≫ g) ≅ internalPull A g ⋙ internalPull A f :=
  CondensedRing.leftDerivedUpperStarComp (coefficient A) f g

/-- The published ordinary composition map, with its endpoints shared.
Source: Stacks 03D8; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def ordinaryCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ordinaryPull A (f ≫ g) ≅ ordinaryPull A g ⋙ ordinaryPull A f :=
  ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g

/-- The actual internal exchange, in the named specialization of its endpoint functors.
Source: Stacks 07A7; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def internalExchange {X' X C Y : Scheme.{u}}
    {a : X' ⟶ X} {f' : X' ⟶ C} {f : X ⟶ Y} {c : C ⟶ Y}
    (sq : ChosenCartesianSquare a f' f c) :
    internalPush A f ⋙ internalPull A c ⟶ internalPull A a ⋙ internalPush A f' :=
  CondensedRing.condensedAmbientExchange (coefficient A) sq

/-- The actual ordinary exchange, in the named specialization of its endpoint functors.
Source: Stacks 07A7; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def ordinaryExchange {X' X C Y : Scheme.{u}}
    {a : X' ⟶ X} {f' : X' ⟶ C} {f : X ⟶ Y} {c : C ⟶ Y}
    (sq : ChosenCartesianSquare a f' f c) :
    ordinaryPush A f ⋙ ordinaryPull A c ⟶ ordinaryPull A a ⋙ ordinaryPush A f' :=
  ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} A)) sq.toCommSq

/-- Compatibility with the actual pullback compositor, on all derived objects.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def compositionCompatible {X Y Z : Scheme.{u}}
    {eX : Encoding A X} {eY : Encoding A Y} {eZ : Encoding A Z}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (df : DerivedEdgeComparison A eX eY f)
    (dg : DerivedEdgeComparison A eY eZ g)
    (dfg : DerivedEdgeComparison A eX eZ (f ≫ g)) : Prop :=
  ∀ M : DerivedCategory (Internal A Z),
    eX.derivedFunctor.map
        ((internalCompIso A f g).hom.app M) ≫
      df.inverse.hom.app ((internalPull A g).obj M) ≫
      (ordinaryPull A f).map (dg.inverse.hom.app M) =
    dfg.inverse.hom.app M ≫
      (ordinaryCompIso A f g).hom.app (eZ.derivedFunctor.obj M)

/-- The source vertical comparison, composed from the two normalized edge comparisons.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def exchangeSourceIso {X Y C : Scheme.{u}}
    {eX : Encoding A X} {eY : Encoding A Y} {eC : Encoding A C}
    {f : X ⟶ Y} {c : C ⟶ Y}
    (df : DerivedEdgeComparison A eX eY f)
    (dc : DerivedEdgeComparison A eC eY c) :
    (internalPush A f ⋙ internalPull A c) ⋙ eC.derivedFunctor ≅
      eX.derivedFunctor ⋙ (ordinaryPush A f ⋙ ordinaryPull A c) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ dc.inverse ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight df.direct _ ≪≫
    Functor.associator _ _ _

/-- The target vertical comparison, composed from the two normalized edge comparisons.
Source: Stacks Project, Tags 00YV, 03D7, 03D8 and 09T5; blueprint refinement (2)
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification). -/
def exchangeTargetIso {X' X C : Scheme.{u}}
    {eX' : Encoding A X'} {eX : Encoding A X} {eC : Encoding A C}
    {a : X' ⟶ X} {f' : X' ⟶ C}
    (da : DerivedEdgeComparison A eX' eX a)
    (df' : DerivedEdgeComparison A eX' eC f') :
    (internalPull A a ⋙ internalPush A f') ⋙ eC.derivedFunctor ≅
      eX.derivedFunctor ⋙ (ordinaryPull A a ⋙ ordinaryPush A f') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ df'.direct ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight da.inverse _ ≪≫
    Functor.associator _ _ _

/-- Finite coefficient realization identifies the specified unbounded exchange and retains
an etale-origin pair for every bounded constructible finite-Tor object.
Source: blueprint main-20261015, det-sf-comp-coherence-refinement.proof (2);
Stacks 09AL, 03D7, 03D8, 09T5
(blueprint: lem-sfb-finite-coefficient-derived-exchange-identification).

Proof following the five DAG steps:
1. Exact termwise realization keeps the bounded interval and cohomology. On each stratum
of the finite constructible stratification, a finitely presented module over finite A
is finite, and A_U tensor_A P is the constant sheaf P. Apply
lem-weil-pbc-finite-ring-constructible-derived-origin (09AL). Retain its bounded
constructible etale antecedent and specified comparison isomorphism as W.
2. Factor heart realization into section-action reconstruction, the normalized constant
ring identification and scalar restriction. Apply
lem-sfb-internal-module-operations-transport.
The equality lem-weil-pbc-finite-discrete-coefficient-sections identifies both actions
on pushforward sections, fixing heartDirect. Apply
lem-sfb-constant-scalar-geometric-adjunctions: every constant a maps to the same constant a.
Thus the Hom bijections, units and counits agree.
3. Apply lem-derived-exact-equivalence-squares. Its universal right-derived pair fixes
direct by direct_normalization. Exact pullback is its termwise localization. Apply
lem-kun-derived-adjoint-square-comparison to the actual adjunctions and this universal
pair; the resulting unit and counit identities are those of DerivedEdgeComparison.
4. Direct-image composition is the ordinary identity-on-sections compositor. Pullback
composition is its unique unit-compatible adjunction conjugate. By
lem-weil-pbc-proetale-derived-pullback-composition and
lem-weil-pbc-conjugate-iso-unit-equation this is also the ordinary compositor.
Localize the termwise equality using lem-weil-pbc-exact-functor-derived-factorization.
This proves compositionCompatible for both paths around the square.
5. The source comparison is a_c then c^* b_f; the target is b_f' then Rf'_* a_a.
Expand def-weil-pbc-ambient-ringed-exchange as unit, canonical square, counit.
Substitute the equations from Steps 3 and 4. Naturality moves each comparison past
the intervening factors and inverse comparisons cancel, giving the displayed rectangle.
All factors are natural transformations, so the equality is natural on all unbounded L.
No properness or horizontal invertibility is used. -/
theorem finiteCoefficientDerivedExchangeIdentification [Finite A] [DiscreteTopology A]
    (E : ∀ T : Scheme.{u}, Encoding A T)
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ C} {f : X ⟶ Y} {c : C ⟶ Y}
    [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace C] [QuasiSeparatedSpace C] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (sq : ChosenCartesianSquare a f' f c) :
    (∃ (df : DerivedEdgeComparison A (E X) (E Y) f)
      (dc : DerivedEdgeComparison A (E C) (E Y) c)
      (da : DerivedEdgeComparison A (E X') (E X) a)
      (df' : DerivedEdgeComparison A (E X') (E C) f')
      (daf : DerivedEdgeComparison A (E X') (E Y) (a ≫ f))
      (dfc : DerivedEdgeComparison A (E X') (E Y) (f' ≫ c)),
      compositionCompatible A da df daf ∧ compositionCompatible A df' dc dfc ∧
      ∀ L : DerivedCategory (Internal A X),
        (E C).derivedFunctor.map
            ((internalExchange A sq).app L) ≫
          (exchangeTargetIso A da df').hom.app L =
        (exchangeSourceIso A df dc).hom.app L ≫
          (ordinaryExchange A sq).app
              ((E X).derivedFunctor.obj L)) ∧
    (∀ L : ConstantModelConstructibleFiniteTor (coefficient A) X,
      ∃ h : DerivedCategory.TStructure.t.plus ((E X).derivedFunctor.obj L.obj),
        ∃ W : Scheme.FixedEtaleOriginWitness X (ULift.{u + 1} A)
            ⟨(E X).derivedFunctor.obj L.obj, h⟩,
          Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) X W.complex.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
