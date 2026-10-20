/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.FiniteRingCompactSupportProjectionMap
public import Sheaf.Paper.CompletedCompactSupportExchange
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Typed exchange and projection transformations

Source: Weil blueprint main-20261015, sec-six-functors-basics,
node sk-def-sf-exchanges, order 1701 (blueprint: sk-def-sf-exchanges).

The finite maps use the intrinsic constant-ring module categories. The direct-image
map is the unit/comparison/counit mate on D+. The compact-support map is the proper
mate followed by the normalized open exchange. Projection is the existing natural
proper-counit/open-projection map, restricted to its stated bounded-below domain.
For the other coefficient stages the operation and comparison data on closed full
domains are exactly the supplied data of def-exchange-projection. The adic exchange
is separately the specified completed exchange, with completed horizontal pullbacks.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u uX uB uY uX' uB' uY' vX vB vY vX' vB' vY'

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

open SheafOfModules

/-- Activate the published Grothendieck property on the original small site,
whose object and morphism universes differ. This supplies the standard injective
resolution construction used in D+, without adding an existence hypothesis.
Source: Stacks 079H and 079P, the injective resolutions underlying order 1701
(blueprint: sk-def-sf-exchanges). -/
instance sfExchangeEnoughInjectives (W : Scheme.{u}) (A : Type u) [CommRing A] :
    EnoughInjectives (proEtaleRingModules W (proEtaleConstantRing W A)) :=
  letI : IsGrothendieckAbelian.{u + 1}
      (proEtaleRingModules W (proEtaleConstantRing W A)) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
      (ProEt.topology W) (proEtaleConstantRing W A)).1
  inferInstance

attribute [-instance] sfExchangeEnoughInjectives
attribute [local instance] sfExchangeEnoughInjectives

/-- Direct-image exchange on the actual bounded-below intrinsic categories. Only
commutativity is used. The comparison is derived from the canonical composition
comparisons, and `mateEquiv` applies the f' unit, that comparison, then the f counit.
Source: blueprint order 1701, first exchange and its defining composite; Stacks 07A7
(blueprint: sk-def-sf-exchanges). -/
def sfExchangeStarPlus (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    (proEtaleConstantModuleDirectImage f A).rightDerivedFunctorPlus ⋙
        (sfIntrinsicPullback A g).mapDerivedCategoryPlus ⟶
      (sfIntrinsicPullback A g').mapDerivedCategoryPlus ⋙
        (proEtaleConstantModuleDirectImage f' A).rightDerivedFunctorPlus :=
  (mateEquiv (sfIntrinsicConstantModuleAdjunction f A).derivedPlus
    (sfIntrinsicConstantModuleAdjunction f' A).derivedPlus
    (TwoSquare.mk _ _ _ _
      ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso
          (sfIntrinsicSquarePullback A g' f' f g sq.w).symm ≪≫
        Functor.mapDerivedCategoryPlusCompIso _ _).hom)).natTrans

/-- Finite compact-support exchange on the ambient unbounded intrinsic categories.
The two Cartesian squares exhibit the base-changed chosen compactification. The open
isomorphism is determined by its inverse being the canonical open-adjunction mate.
The formula is the proper direct-image mate at j!K followed by Rp'_* of open exchange.
Source: blueprint order 1701, second exchange; def-exchange-projection, chosen
compactification formula (blueprint: sk-def-sf-exchanges). -/
def sfExchangeShriek (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (properSquare : IsPullback gbar c'.g c.g g)
    (openSquare : IsPullback g' c'.i c.i gbar) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  let A := Padic.coefficientExtensionRing l E n
  CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
    (sfIntrinsicDerivedOpen A c.i) (sfIntrinsicDerivedOpen A c'.i)
    (sfIntrinsicDerivedPullback A c.g) (proEtaleConstantDerivedDirectImage c.g A)
    (sfIntrinsicConstantModuleAdjunction c.g A).mapDerivedCategoryRightDerivedAdjunction
    (sfIntrinsicDerivedPullback A c'.g) (proEtaleConstantDerivedDirectImage c'.g A)
    (sfIntrinsicConstantModuleAdjunction c'.g A).mapDerivedCategoryRightDerivedAdjunction
    (sfIntrinsicDerivedPullback A g) (sfIntrinsicDerivedPullback A g')
    (sfIntrinsicDerivedPullback A gbar)
    (sfIntrinsicDerivedSquarePullback A gbar c'.g c.g g properSquare.w).symm
    ((Classical.choice (proEtale_openSquareExchange l E n hn)).exchange
      g' c'.i c.i gbar openSquare)

/-- The ambient finite projection, restricted in its two arguments to Db_c and Dctf.
Its bifunctor source and target are the canonical fixed-scalar realizations of
Rf!K tensor L and Rf!(K tensor Lf*L), respectively. Both arguments are variable in
the existing natural transformation, so this restriction retains both naturalities.
Source: blueprint order 1701, projection display; Stacks 0F0G
(blueprint: sk-def-sf-exchanges). -/
def sfFiniteProjectionAmbient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : (intrinsicFiniteTorsionConstructible l E n hn X).FullSubcategory)
    (L : (WeilConjectures.finiteTorConstructible l E n hn Y).FullSubcategory) :
    Arrow (proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  Arrow.mk (((finiteRingCompactSupportProjection
    (Padic.coefficientExtensionRing l E n) c).app K.obj).app L.obj)

/-- The bounded-below typing facts implicit in the projection display. No projection
formula or invertibility is asserted. Only L, not K, has finite Tor amplitude.
Source: blueprint order 1701, the phrase "in D+(Y,Lambda)"; Stacks 0F0G
(blueprint: sk-def-sf-exchanges).

Proof (postponed): intrinsic constructibility gives a bounded complex K and the
finite-Tor predicate gives a bounded constructible L with a uniform Tor interval.
Exact pullback preserves that interval. The tensor of bounded-below K with Lf*L
is bounded below, by the flat resolution computing that Tor interval. Exact open
extension preserves lower cohomological bounds and a right-derived left-exact
proper image preserves bounded-below objects. Thus Rf!(K tensor Lf*L) is bounded
below. Likewise Rf!K is bounded below, and tensoring it with the finite-Tor L
is bounded below. Canonical coefficient realization is exact and its induced
derived equivalence preserves the standard t-structure, giving precisely the
two displayed predicates for the existing projection's endpoints. -/
theorem sfFiniteProjection_boundedBelow (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : (intrinsicFiniteTorsionConstructible l E n hn X).FullSubcategory)
    (L : (WeilConjectures.finiteTorConstructible l E n hn Y).FullSubcategory) :
    let P := sfFiniteProjectionAmbient l E n hn c K L
    (DerivedCategory.TStructure.t (C := proEtaleRingModules Y
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n)))).plus P.left ∧
    (DerivedCategory.TStructure.t (C := proEtaleRingModules Y
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n)))).plus P.right := by
  sorry

/-- The specified finite-coefficient projection as a morphism in D+(Y,A).
The full-subcategory lift uses the typing lemma, leaving the canonical arrow intact.
Source: blueprint order 1701, final display (blueprint: sk-def-sf-exchanges). -/
def sfFiniteProjectionPlus (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : (intrinsicFiniteTorsionConstructible l E n hn X).FullSubcategory)
    (L : (WeilConjectures.finiteTorConstructible l E n hn Y).FullSubcategory) :
    let P := sfFiniteProjectionAmbient l E n hn c K L
    (⟨P.left, (sfFiniteProjection_boundedBelow l E n hn c K L).1⟩ :
      DerivedCategory.Plus (proEtaleRingModules Y
        (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n)))) ⟶
    (⟨P.right, (sfFiniteProjection_boundedBelow l E n hn c K L).2⟩ :
      DerivedCategory.Plus (proEtaleRingModules Y
        (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n)))) :=
  ObjectProperty.homMk (sfFiniteProjectionAmbient l E n hn c K L).hom

/-- The adic clause uses precisely the existing completed compact-support exchange.
The horizontal functors here are completed pullbacks. The coefficient datum and
complete-object predicate retain the actual adic hypotheses and completion model.
Source: blueprint order 1701, adic parenthesis; Definition 1939
(blueprint: sk-def-sf-exchanges). -/
def sfExchangeShriekCompleted
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
    (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory) :=
  completedCompactSupportExchange d c c' gbar properSquare openSquare r a ha K

end AlgebraicGeometry.Scheme

namespace CategoryTheory.SuppliedExchangeProjection

variable {DX : Type uX} {DB : Type uB} {DY : Type uY}
  {DX' : Type uX'} {DB' : Type uB'} {DY' : Type uY'}
  [Category.{vX} DX] [Category.{vB} DB] [Category.{vY} DY]
  [Category.{vX'} DX'] [Category.{vB'} DB'] [Category.{vY'} DY']

/-- The three typed maps on the prescribed supplied coefficient domains, packaged
together. At the integral stage these data use completed pullback and tensor;
rational maps are their localizations and algebraically closed maps their common
finite-field representatives. The data, reductions and scalar normalizations are
those of def-exchange-projection, not freely supplied exchange/projection arrows.
`exchange` is the unit/comparison/counit mate, `compactExchange` its proper/open
composite, and `projection` the proper-counit/open-projection composite. Components
of the last map at Db_c K and Dctf L give the displayed projection. All three are
natural transformations on the closed full domains specified in sk-def-sf-operations.
Source: blueprint order 1701 and def-exchange-projection, supplied-domain paragraph
(blueprint: sk-def-sf-exchanges). -/
def sfExchangeProjection
    (d : ExchangeProjectionStage (DX := DX) (DB := DB) (DY := DY)
      (DX' := DX') (DB' := DB') (DY' := DY')) :
    (d.push ⋙ d.horizontal ⟶ d.horizontal' ⋙ d.push') ×
      (d.compactSupport ⋙ d.horizontal ⟶ d.horizontal' ⋙ d.compactSupport') ×
      (d.compactSupport ⋙ d.tensorY ⟶
        (Functor.postcompose₂.obj d.compactSupport).obj
          ((((Functor.whiskeringLeft₂ DX).obj (𝟭 DX)).obj d.pull).obj d.tensorX)) :=
  ⟨d.exchange, d.compactExchange, d.projection⟩

end CategoryTheory.SuppliedExchangeProjection
