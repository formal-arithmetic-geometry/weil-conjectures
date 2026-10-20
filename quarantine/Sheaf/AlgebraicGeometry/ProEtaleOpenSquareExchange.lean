/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleExtensionByZeroAdjunction

/-!
# Canonical open-square exchange on the small pro-etale site

Source: Weil blueprint, trace formula, order 2367; Stacks Project, Tags 03S6 and 04J0
(blueprint: lem-trf-open-square-exchange).

All functors act on the published intrinsic constant-ring module categories.
The comparison is fixed as the inverse of the open-adjunction mate; the data below
include restriction normalization, both identity laws and both pasting laws.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- The open adjunction transported through the canonical realization equivalences.
Source: Stacks, Tags 03DI and 00YV (blueprint: lem-trf-open-square-exchange). -/
noncomputable def sfIntrinsicOpenAdjunction {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] : sfIntrinsicExtensionByZero j A ⊣ sfIntrinsicPullback A j :=
  ((sfIntrinsicModuleEquivalence U A).symm.toAdjunction.comp
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).comp
    (sfIntrinsicModuleEquivalence Y A).toAdjunction

/-- Composition of open extensions is the unique comparison respecting composite units.
Source: Stacks, Tag 03DI (blueprint: lem-trf-open-square-exchange). -/
noncomputable def sfIntrinsicOpenComp {V U Y : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    sfIntrinsicExtensionByZero (i ≫ j) A ≅
      sfIntrinsicExtensionByZero i A ⋙ sfIntrinsicExtensionByZero j A :=
  (((sfIntrinsicOpenAdjunction A i).comp (sfIntrinsicOpenAdjunction A j)).ofNatIsoRight
    (sfIntrinsicPullbackComp A i j).symm).leftAdjointUniq
      (sfIntrinsicOpenAdjunction A (i ≫ j)) |>.symm

/-- Identity open extension, normalized by its adjunction unit.
Source: Stacks, Tag 03DI (blueprint: lem-trf-open-square-exchange). -/
noncomputable def sfIntrinsicOpenId (Y : Scheme.{u}) :
    sfIntrinsicExtensionByZero (𝟙 Y) A ≅ 𝟭 _ :=
  ((sfIntrinsicOpenAdjunction A (𝟙 Y)).ofNatIsoRight
    (sfIntrinsicPullbackId A Y)).leftAdjointUniq Adjunction.id

/-- Commuting pullbacks for a commutative square, with the canonical coefficient action.
Source: Stacks, Tag 04J0 (blueprint: lem-trf-open-square-exchange). -/
noncomputable def sfIntrinsicSquarePullback {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    (w : gU ≫ j = j' ≫ g) :
    sfIntrinsicPullback A j ⋙ sfIntrinsicPullback A gU ≅
      sfIntrinsicPullback A g ⋙ sfIntrinsicPullback A j' :=
  (sfIntrinsicPullbackComp A gU j).symm ≪≫
    eqToIso (congrArg (sfIntrinsicPullback A) w) ≪≫ sfIntrinsicPullbackComp A j' g

/-- The reverse exchange map is the mate of the pullback square. Explicitly it applies
`j'_!` to `g_U^*` of the open unit, then the pullback-square comparison, and finally the
open counit. Thus it is a specified map, rather than a freely chosen isomorphism.
Source: Stacks, Tag 03S6 (blueprint: lem-trf-open-square-exchange). -/
noncomputable def sfIntrinsicOpenMate {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : gU ≫ j = j' ≫ g) :
    sfIntrinsicPullback A gU ⋙ sfIntrinsicExtensionByZero j' A ⟶
      sfIntrinsicExtensionByZero j A ⋙ sfIntrinsicPullback A g :=
  whiskerRight (whiskerRight (sfIntrinsicOpenAdjunction A j).unit
    (sfIntrinsicPullback A gU)) (sfIntrinsicExtensionByZero j' A) ≫
  whiskerRight (whiskerLeft (sfIntrinsicExtensionByZero j A)
    (sfIntrinsicSquarePullback A gU j' j g w).hom) (sfIntrinsicExtensionByZero j' A) ≫
  whiskerLeft (sfIntrinsicExtensionByZero j A ⋙ sfIntrinsicPullback A g)
    (sfIntrinsicOpenAdjunction A j').counit

/-- Exact extension by zero on the full, unbounded intrinsic derived category.
Source: blueprint order 2367, termwise derivation (blueprint: lem-trf-open-square-exchange). -/
noncomputable abbrev sfIntrinsicDerivedOpen {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] : proEtaleDerivedCategory U A ⥤ proEtaleDerivedCategory Y A :=
  (sfIntrinsicExtensionByZero j A).mapDerivedCategory

/-- Descend an actual natural transformation of exact intrinsic functors termwise.
Source: Stacks, Tag 05RU (blueprint: lem-trf-open-square-exchange). -/
noncomputable def sfIntrinsicDeriveMap {X Y : Scheme.{u}}
    {F G : proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      proEtaleRingModules Y (proEtaleConstantRing Y A)}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (whiskerRight (NatTrans.mapHomologicalComplex a (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- The specified derived reverse exchange is the exact termwise descent of the open mate.
Source: blueprint order 2367; Stacks, Tag 03S6 (blueprint: lem-trf-open-square-exchange). -/
noncomputable def sfIntrinsicDerivedOpenMate {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : gU ≫ j = j' ≫ g) :
    sfIntrinsicDerivedPullback A gU ⋙ sfIntrinsicDerivedOpen A j' ⟶
      sfIntrinsicDerivedOpen A j ⋙ sfIntrinsicDerivedPullback A g :=
  (mapDerivedCategoryCompIso (sfIntrinsicPullback A gU)
    (sfIntrinsicExtensionByZero j' A)).inv ≫
  sfIntrinsicDeriveMap A (sfIntrinsicOpenMate A gU j' j g w) ≫
  (mapDerivedCategoryCompIso (sfIntrinsicExtensionByZero j A)
    (sfIntrinsicPullback A g)).hom

/-- The derived open unit, with the localization identity and composition comparisons.
Source: Stacks, Tag 05RU (blueprint: lem-trf-open-square-exchange). -/
noncomputable def sfIntrinsicDerivedOpenUnit {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] : 𝟭 (proEtaleDerivedCategory U A) ⟶
      sfIntrinsicDerivedOpen A j ⋙ sfIntrinsicDerivedPullback A j :=
  (mapDerivedCategoryIdIso _).inv ≫
    sfIntrinsicDeriveMap A (sfIntrinsicOpenAdjunction A j).unit ≫
    (mapDerivedCategoryCompIso (sfIntrinsicExtensionByZero j A)
      (sfIntrinsicPullback A j)).hom

/-- Pullback composition on unbounded derived categories.
Source: Stacks, Section 0735 (blueprint: lem-trf-open-square-exchange). -/
noncomputable def sfIntrinsicDerivedPullbackComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    sfIntrinsicDerivedPullback A (f ≫ g) ≅
      sfIntrinsicDerivedPullback A g ⋙ sfIntrinsicDerivedPullback A f :=
  mapDerivedCategoryNatIso (sfIntrinsicPullbackComp A f g) ≪≫
    mapDerivedCategoryCompIso (sfIntrinsicPullback A g) (sfIntrinsicPullback A f)

/-- Open-extension composition on unbounded derived categories.
Source: blueprint order 2367 (blueprint: lem-trf-open-square-exchange). -/
noncomputable def sfIntrinsicDerivedOpenComp {V U Y : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    sfIntrinsicDerivedOpen A (i ≫ j) ≅ sfIntrinsicDerivedOpen A i ⋙ sfIntrinsicDerivedOpen A j :=
  mapDerivedCategoryNatIso (sfIntrinsicOpenComp A i j) ≪≫
    mapDerivedCategoryCompIso (sfIntrinsicExtensionByZero i A) (sfIntrinsicExtensionByZero j A)

/-- Identity pullback on the unbounded derived category.
Source: Stacks, Section 0735 (blueprint: lem-trf-open-square-exchange). -/
noncomputable def sfIntrinsicDerivedPullbackId (Y : Scheme.{u}) :
    sfIntrinsicDerivedPullback A (𝟙 Y) ≅ 𝟭 _ :=
  mapDerivedCategoryNatIso (sfIntrinsicPullbackId A Y) ≪≫ mapDerivedCategoryIdIso _

/-- Identity open extension on the unbounded derived category.
Source: blueprint order 2367 (blueprint: lem-trf-open-square-exchange). -/
noncomputable def sfIntrinsicDerivedOpenId (Y : Scheme.{u}) :
    sfIntrinsicDerivedOpen A (𝟙 Y) ≅ 𝟭 _ :=
  mapDerivedCategoryNatIso (sfIntrinsicOpenId A Y) ≪≫ mapDerivedCategoryIdIso _

/-- The derived pullback identification used to restrict the exchange to the open.
Source: Stacks, Tag 04J0 (blueprint: lem-trf-open-square-exchange). -/
noncomputable def sfIntrinsicDerivedSquarePullback {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    (w : gU ≫ j = j' ≫ g) :
    sfIntrinsicDerivedPullback A j ⋙ sfIntrinsicDerivedPullback A gU ≅
      sfIntrinsicDerivedPullback A g ⋙ sfIntrinsicDerivedPullback A j' :=
  (mapDerivedCategoryCompIso (sfIntrinsicPullback A j) (sfIntrinsicPullback A gU)).symm ≪≫
    mapDerivedCategoryNatIso (sfIntrinsicSquarePullback A gU j' j g w) ≪≫
    mapDerivedCategoryCompIso (sfIntrinsicPullback A g) (sfIntrinsicPullback A j')

/-- A coherent family of the canonical exchange isomorphisms. The `canonical` field fixes
its inverse to the specified mate, so none of its isomorphisms is arbitrary. The restriction
field is precisely the identity after the two open units and the pullback identification.
The last four fields express horizontal/vertical identity and pasting, respectively.
Source: blueprint order 2367; Stacks, Tags 03S6 and 04J0
(blueprint: lem-trf-open-square-exchange). -/
structure SfOpenSquareExchangeData where
  exchange : ∀ {U' U Y' Y : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ Y')
    (j : U ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion j']
    (_sq : IsPullback gU j' j g),
    sfIntrinsicDerivedOpen A j ⋙ sfIntrinsicDerivedPullback A g ≅
      sfIntrinsicDerivedPullback A gU ⋙ sfIntrinsicDerivedOpen A j'
  canonical : ∀ {U' U Y' Y : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ Y')
    (j : U ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g),
    (exchange gU j' j g sq).inv = sfIntrinsicDerivedOpenMate A gU j' j g sq.w
  restriction : ∀ {U' U Y' Y : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ Y')
    (j : U ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g) (K : proEtaleDerivedCategory U A),
    (sfIntrinsicDerivedPullback A gU).map ((sfIntrinsicDerivedOpenUnit A j).app K) ≫
      (sfIntrinsicDerivedSquarePullback A gU j' j g sq.w).hom.app
        ((sfIntrinsicDerivedOpen A j).obj K) ≫
      (sfIntrinsicDerivedPullback A j').map ((exchange gU j' j g sq).hom.app K) =
        (sfIntrinsicDerivedOpenUnit A j').app ((sfIntrinsicDerivedPullback A gU).obj K)
  horizontal_id : ∀ {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (sq : IsPullback (𝟙 U) j j (𝟙 Y)),
    (exchange (𝟙 U) j j (𝟙 Y) sq).hom =
      (isoWhiskerLeft (sfIntrinsicDerivedOpen A j) (sfIntrinsicDerivedPullbackId A Y)).hom ≫
      (isoWhiskerRight (sfIntrinsicDerivedPullbackId A U) (sfIntrinsicDerivedOpen A j)).inv
  vertical_id : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y)
    (sq : IsPullback g (𝟙 X) (𝟙 Y) g),
    (exchange g (𝟙 X) (𝟙 Y) g sq).hom =
      (isoWhiskerRight (sfIntrinsicDerivedOpenId A Y) (sfIntrinsicDerivedPullback A g)).hom ≫
      (isoWhiskerLeft (sfIntrinsicDerivedPullback A g) (sfIntrinsicDerivedOpenId A X)).inv
  horizontal_pasting : ∀ {U'' U' U Y'' Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (hU : U'' ⟶ U') (j : U ⟶ Y) (j' : U' ⟶ Y') (j'' : U'' ⟶ Y'')
    (g : Y' ⟶ Y) (h : Y'' ⟶ Y')
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    (sq : IsPullback gU j' j g) (sq' : IsPullback hU j'' j' h)
    (outer : IsPullback (hU ≫ gU) j'' j (h ≫ g)),
    (exchange (hU ≫ gU) j'' j (h ≫ g) outer).hom =
      (isoWhiskerLeft (sfIntrinsicDerivedOpen A j)
        (sfIntrinsicDerivedPullbackComp A h g)).hom ≫
      whiskerRight (exchange gU j' j g sq).hom (sfIntrinsicDerivedPullback A h) ≫
      whiskerLeft (sfIntrinsicDerivedPullback A gU) (exchange hU j'' j' h sq').hom ≫
      (isoWhiskerRight (sfIntrinsicDerivedPullbackComp A hU gU)
        (sfIntrinsicDerivedOpen A j'')).inv
  vertical_pasting : ∀ {V' V U' U Y' Y : Scheme.{u}}
    (i : V ⟶ U) (i' : V' ⟶ U') (j : U ⟶ Y) (j' : U' ⟶ Y')
    (gV : V' ⟶ V) (gU : U' ⟶ U) (g : Y' ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion i'] [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g) (sq' : IsPullback gV i' i gU)
    (outer : IsPullback gV (i' ≫ j') (i ≫ j) g),
    (exchange gV (i' ≫ j') (i ≫ j) g outer).hom =
      (isoWhiskerRight (sfIntrinsicDerivedOpenComp A i j)
        (sfIntrinsicDerivedPullback A g)).hom ≫
      whiskerLeft (sfIntrinsicDerivedOpen A i) (exchange gU j' j g sq).hom ≫
      whiskerRight (exchange gV i' i gU sq').hom (sfIntrinsicDerivedOpen A j') ≫
      (isoWhiskerLeft (sfIntrinsicDerivedPullback A gV)
        (sfIntrinsicDerivedOpenComp A i' j')).inv

/-- Canonical open-square exchange with finite coefficient ring `A_{E,n}`.
Source: Weil blueprint, trace formula, order 2367; Stacks, Tags 03S6 and 04J0
(blueprint: lem-trf-open-square-exchange).

Proof: first work with all sheaves over the constant ring. The localization equivalence
identifies restriction with open pullback. Evaluate both `j^* g_*` and `g_{U*} j'^*` on
`V -> U`: both are sections on `Y' ×_Y V = U' ×_U V`. The same fibre-product maps induce
restriction maps, and constant scalar sections induce the same scalar action, giving a
natural linear isomorphism. Take its left-adjoint conjugate using the composite units;
this gives the inverse of `sfIntrinsicOpenMate`, by the adjunction triangle identities.
To normalize, test against `j'_* N`. Open restriction cancels open direct image, and the
middle section identification becomes the identity on `N(U' ×_U V)`. The resulting Hom
bijection is the identity; Yoneda yields the displayed restriction equation. For two
horizontal squares the section comparisons compose by fibre-product associativity.
Their Hom bijections compose using the composite adjunction, so uniqueness of the
conjugate gives horizontal pasting. For nested opens the restriction comparisons compose;
the intervening open-adjunction bijections cancel, giving vertical pasting under the
specified open-composition comparisons. Identity comparisons give both identity laws.
Finally open extension and constant-coefficient pullback are exact. Apply their maps and
the comparison termwise to every unbounded cochain complex. They preserve quasi-isomorphisms,
so localization descends the isomorphism and all equations. Equality after localization
is detected by precomposition with the localization functor. Canonical realization
transports the same argument to the intrinsic coefficient category used throughout.
No boundedness, constructibility or stalk-conservativity hypothesis is used. -/
theorem proEtale_openSquareExchange (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (@SfOpenSquareExchangeData (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n hn)) := by
  sorry

end AlgebraicGeometry.Scheme
