/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.DerivedDirectImageOpenCoherence
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.SectionDerivedPushpullNormalization
import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Adjunction
import Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The supported open-square counit and restriction of scalars

Source: blueprint main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md,
paragraph (3), the all-continuous tame-boundary input
(blueprint: lem-sfb-open-square-support-scalar-counit).

All comparison arrows below are constructions from the specified geometric adjunctions.
In particular the derived direct-image scalar comparison is its inverse-image mate; its
invertibility for arbitrary coefficient morphisms is an assertion, not a flatness assumption.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]

/-- The composite denoted B_R in the statement, using the actual derived direct image.
Source: blueprint paragraph (3) (blueprint: lem-sfb-open-square-support-scalar-counit). -/
def openSquareB {W V Y : Scheme.{u}} (b : W ⟶ V) [IsOpenImmersion b] (j : V ⟶ Y) :=
  (openImmersionLowerShriek R b).mapDerivedCategory ⋙ moduleObjectDerivedPushforward R j

/-- The source of the counit, c_! Ra_*.
Source: blueprint paragraph (3) (blueprint: lem-sfb-open-square-support-scalar-counit). -/
def openSquareA {W O Y : Scheme.{u}} (a : W ⟶ O) (c : O ⟶ Y) [IsOpenImmersion c] :=
  moduleObjectDerivedPushforward R a ⋙ (openImmersionLowerShriek R c).mapDerivedCategory

/-- The actual derived open unit as an isomorphism, using full faithfulness of extension
by zero and the published derived-unit normalization.
Source: Stacks Tag 08FJ (blueprint: lem-sfb-open-square-support-scalar-counit). -/
def openSquareOpenUnitIso {S T : Scheme.{u}} (f : S ⟶ T) [IsOpenImmersion f] :
    𝟭 _ ≅ (openImmersionLowerShriek R f).mapDerivedCategory ⋙
      (upperStar R f).mapDerivedCategory := by
  haveI : IsIso (openImmersionLowerShriekUpperStarAdjunction R f).unit :=
    (openImmersionLowerShriekUpperStarAdjunction R f).unit_isIso_of_L_fully_faithful
  haveI : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction R f).unit := by
    unfold derivedOpenImmersionLowerShriekUpperStarAdjunction
    infer_instance
  exact asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction R f).unit

/-- The prescribed rho arrow: the derived restriction mate, followed by Ra_* of the
inverse of the actual derived open unit. This definition asserts no invertibility of rho.
Source: blueprint paragraph (3) (blueprint: lem-sfb-open-square-support-scalar-counit). -/
def openSquareRho {W V O Y : Scheme.{u}} (b : W ⟶ V) [IsOpenImmersion b]
    (a : W ⟶ O) (j : V ⟶ Y) (c : O ⟶ Y) (sq : CommSq b a j c) :
    openSquareB R b j ⋙ (upperStar R c).mapDerivedCategory ⟶
      moduleObjectDerivedPushforward R a :=
  Functor.whiskerLeft (openImmersionLowerShriek R b).mapDerivedCategory
      (derivedDirectImageOpenRestriction R sq) ≫
    Functor.whiskerRight
      (openSquareOpenUnitIso R b).inv
      (moduleObjectDerivedPushforward R a)

/-- The actual inverse adjunct of rho inverse, with rho supplied as an isomorphism.
Its hom is pinned to openSquareRho in the theorem, so this introduces no arbitrary map.
Source: blueprint paragraph (3) (blueprint: lem-sfb-open-square-support-scalar-counit). -/
def openSquareCounit {W V O Y : Scheme.{u}} (b : W ⟶ V) [IsOpenImmersion b]
    (a : W ⟶ O) (j : V ⟶ Y) (c : O ⟶ Y) [IsOpenImmersion c]
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj R W)))
    (rho : ((upperStar R c).mapDerivedCategory).obj ((openSquareB R b j).obj M) ≅
      (moduleObjectDerivedPushforward R a).obj M) :
    (openSquareA R a c).obj M ⟶ (openSquareB R b j).obj M :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction R c).homEquiv _ _).symm rho.inv

variable {R}
  {R' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R'] [IsCommMonObj R']
  (phi : R ⟶ R') [IsMonHom phi]

/-- Exact restriction along p_T^* phi on the ordinary unbounded derived category.
Source: blueprint paragraph (3) (blueprint: lem-sfb-open-square-support-scalar-counit). -/
def openSquareRes (T : Scheme.{u}) :=
  (Mod.comap (coefficientMap phi T) :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj R' T) ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj R T)).mapDerivedCategory

/-- The canonical derived direct-image scalar comparison, defined as the mate of the
canonical inverse-image scalar isomorphism under the exact-left derived adjunctions.
Unlike derivedComapLowerStarIso, its construction needs no flatness hypothesis.
Source: Stacks Tags 0D6D, 0D6E (blueprint: lem-sfb-open-square-support-scalar-counit). -/
def openSquarePushScalar {S T : Scheme.{u}} (f : S ⟶ T) :
    moduleObjectDerivedPushforward R' f ⋙ openSquareRes phi T ⟶
      openSquareRes phi S ⋙ moduleObjectDerivedPushforward R f :=
  (mateEquiv
    (upperStarLowerStarAdjunction R' f).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction R f).mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (derivedComapUpperStarIso phi f).inv)).natTrans

/-- Derive the identical-underlying-extension comparison termwise, inserting the
canonical comparisons for exact derived composites.
Source: Stacks Tag 03DI (blueprint: lem-sfb-open-square-support-scalar-counit). -/
def openSquareShriekScalar {S T : Scheme.{u}} (f : S ⟶ T) [IsOpenImmersion f] :
    (openImmersionLowerShriek R' f).mapDerivedCategory ⋙ openSquareRes phi T ≅
      openSquareRes phi S ⋙ (openImmersionLowerShriek R f).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (comapOpenImmersionLowerShriekIso phi f) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The comparison on B obtained by composing the direct-image and open-extension
scalar comparisons, with the standard associators.
Source: blueprint paragraph (3) (blueprint: lem-sfb-open-square-support-scalar-counit). -/
def openSquareBScalar {W V Y : Scheme.{u}} (b : W ⟶ V) [IsOpenImmersion b]
    (j : V ⟶ Y)
    (hj : moduleObjectDerivedPushforward R' j ⋙ openSquareRes phi Y ≅
      openSquareRes phi V ⋙ moduleObjectDerivedPushforward R j) :
    openSquareB R' b j ⋙ openSquareRes phi Y ≅ openSquareRes phi W ⋙ openSquareB R b j :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (openImmersionLowerShriek R' b).mapDerivedCategory hj ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openSquareShriekScalar phi b)
      (moduleObjectDerivedPushforward R j) ≪≫ Functor.associator _ _ _

/-- The comparison on c_! Ra_* obtained by composing the direct-image and
open-extension scalar comparisons, with the standard associators.
Source: blueprint paragraph (3) (blueprint: lem-sfb-open-square-support-scalar-counit). -/
def openSquareAScalar {W O Y : Scheme.{u}} (a : W ⟶ O) (c : O ⟶ Y) [IsOpenImmersion c]
    (ha : moduleObjectDerivedPushforward R' a ⋙ openSquareRes phi O ≅
      openSquareRes phi W ⋙ moduleObjectDerivedPushforward R a) :
    openSquareA R' a c ⋙ openSquareRes phi Y ≅ openSquareRes phi W ⋙ openSquareA R a c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleObjectDerivedPushforward R' a)
      (openSquareShriekScalar phi c) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ha (openImmersionLowerShriek R c).mapDerivedCategory ≪≫
      Functor.associator _ _ _

variable (R)

/-- The family of isomorphisms whose homs are required to be the prescribed rho arrows.
The domain is exactly D^+(W,R), with its ordinary unbounded derived-category inclusion.
Source: blueprint paragraph (3) (blueprint: lem-sfb-open-square-support-scalar-counit). -/
abbrev OpenSquareRhoFamily {W V O Y : Scheme.{u}} (b : W ⟶ V) [IsOpenImmersion b]
    (a : W ⟶ O) (j : V ⟶ Y) (c : O ⟶ Y) :=
  ∀ M : DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
    (condensedRingObj R W)),
    ((upperStar R c).mapDerivedCategory).obj ((openSquareB R b j).obj M.obj) ≅
      (moduleObjectDerivedPushforward R a).obj M.obj

/-- Exactly the normalization, counit formula, naturality and support clauses over R.
The closed restriction is the actual exact inverse image; its vanishing is used only
in the implication asserting invertibility of the counit.
Source: blueprint paragraph (3) (blueprint: lem-sfb-open-square-support-scalar-counit). -/
def OpenSquareCounitAssertions {W V O Y Z : Scheme.{u}}
    (b : W ⟶ V) [IsOpenImmersion b] (a : W ⟶ O) (j : V ⟶ Y)
    (c : O ⟶ Y) [IsOpenImmersion c] (sq : CommSq b a j c) (i : Z ⟶ Y)
    (rho : OpenSquareRhoFamily R b a j c) : Prop :=
  (∀ M, (rho M).hom = (openSquareRho R b a j c sq).app M.obj) ∧
  (∀ M, openSquareCounit R b a j c M.obj (rho M) =
    (openImmersionLowerShriek R c).mapDerivedCategory.map (rho M).inv ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction R c).counit.app
        ((openSquareB R b j).obj M.obj)) ∧
  (∀ (M N : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj R W)))
      (mu : M ⟶ N),
    (upperStar R c).mapDerivedCategory.map ((openSquareB R b j).map mu.hom) ≫
        (rho N).hom = (rho M).hom ≫ (moduleObjectDerivedPushforward R a).map mu.hom) ∧
  (∀ (M N : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj R W)))
      (mu : M ⟶ N),
    (openSquareA R a c).map mu.hom ≫ openSquareCounit R b a j c N.obj (rho N) =
      openSquareCounit R b a j c M.obj (rho M) ≫ (openSquareB R b j).map mu.hom) ∧
  (∀ M, IsZero ((upperStar R i).mapDerivedCategory.obj ((openSquareB R b j).obj M.obj)) →
    IsIso (openSquareCounit R b a j c M.obj (rho M)))

variable {R}

/-- Preservation of the two actual derived open adjunction maps under the specified
scalar comparisons. Both equations are assertions on all unbounded derived objects.
Source: Stacks Tags 03DI, 08FJ (blueprint: lem-sfb-open-square-support-scalar-counit). -/
def OpenSquareScalarOpenAdjunction {S T : Scheme.{u}} (f : S ⟶ T)
    [IsOpenImmersion f] : Prop :=
  (∀ M,
    (openSquareRes phi S).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction R' f).unit.app M) ≫
      (derivedComapUpperStarIso phi f).hom.app
        ((openImmersionLowerShriek R' f).mapDerivedCategory.obj M) ≫
      (upperStar R f).mapDerivedCategory.map ((openSquareShriekScalar phi f).hom.app M) =
    (derivedOpenImmersionLowerShriekUpperStarAdjunction R f).unit.app
      ((openSquareRes phi S).obj M)) ∧
  (∀ N,
    (openSquareShriekScalar phi f).hom.app ((upperStar R' f).mapDerivedCategory.obj N) ≫
      (openImmersionLowerShriek R f).mapDerivedCategory.map
        ((derivedComapUpperStarIso phi f).hom.app N) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction R f).counit.app
        ((openSquareRes phi T).obj N) =
    (openSquareRes phi T).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction R' f).counit.app N))

/-- Preservation of the ordinary open unit and counit by the existing underived
scalar comparisons; these are the identical-extension-presheaf comparisons.
Source: Stacks Tag 03DI (blueprint: lem-sfb-open-square-support-scalar-counit). -/
def OpenSquareScalarUnderivedOpenAdjunction {S T : Scheme.{u}} (f : S ⟶ T)
    [IsOpenImmersion f] : Prop :=
  (∀ M,
    (Mod.comap (coefficientMap phi S)).map
        ((openImmersionLowerShriekUpperStarAdjunction R' f).unit.app M) ≫
      (comapUpperStarIso phi f).hom.app ((openImmersionLowerShriek R' f).obj M) ≫
      (upperStar R f).map ((comapOpenImmersionLowerShriekIso phi f).hom.app M) =
    (openImmersionLowerShriekUpperStarAdjunction R f).unit.app
      ((Mod.comap (coefficientMap phi S)).obj M)) ∧
  (∀ N,
    (comapOpenImmersionLowerShriekIso phi f).hom.app ((upperStar R' f).obj N) ≫
      (openImmersionLowerShriek R f).map ((comapUpperStarIso phi f).hom.app N) ≫
      (openImmersionLowerShriekUpperStarAdjunction R f).counit.app
        ((Mod.comap (coefficientMap phi T)).obj N) =
    (Mod.comap (coefficientMap phi T)).map
      ((openImmersionLowerShriekUpperStarAdjunction R' f).counit.app N))

/-- The scalar clauses, retaining the actual comparisons, rho normalization, and
all mixed-coefficient arrows. The last equation has no closed-support hypothesis.
Source: blueprint paragraph (3) (blueprint: lem-sfb-open-square-support-scalar-counit). -/
def OpenSquareScalarAssertions {W V O Y : Scheme.{u}}
    (b : W ⟶ V) [IsOpenImmersion b] (a : W ⟶ O) (j : V ⟶ Y)
    (c : O ⟶ Y) [IsOpenImmersion c] (sq : CommSq b a j c)
    (rho : OpenSquareRhoFamily R b a j c) (rho' : OpenSquareRhoFamily R' b a j c) : Prop :=
  ∃ hj : moduleObjectDerivedPushforward R' j ⋙ openSquareRes phi Y ≅
      openSquareRes phi V ⋙ moduleObjectDerivedPushforward R j,
  ∃ ha : moduleObjectDerivedPushforward R' a ⋙ openSquareRes phi O ≅
      openSquareRes phi W ⋙ moduleObjectDerivedPushforward R a,
    hj.hom = openSquarePushScalar phi j ∧ ha.hom = openSquarePushScalar phi a ∧
    OpenSquareScalarUnderivedOpenAdjunction phi b ∧
    OpenSquareScalarUnderivedOpenAdjunction phi c ∧
    OpenSquareScalarOpenAdjunction phi b ∧ OpenSquareScalarOpenAdjunction phi c ∧
    (∀ M', (openSquareRes phi O).map (rho' M').hom ≫ ha.hom.app M'.obj =
      (derivedComapUpperStarIso phi c).hom.app ((openSquareB R' b j).obj M'.obj) ≫
        (upperStar R c).mapDerivedCategory.map
          ((openSquareBScalar phi b j hj).hom.app M'.obj) ≫
        (openSquareRho R b a j c
          sq).app ((openSquareRes phi W).obj M'.obj)) ∧
    (∀ (M : DerivedCategory.Plus
        (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj R W)))
      (M' : DerivedCategory.Plus
        (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj R' W)))
      (mu : M.obj ⟶ (openSquareRes phi W).obj M'.obj),
      (openSquareA R a c).map mu ≫ (openSquareAScalar phi a c ha).inv.app M'.obj ≫
        (openSquareRes phi Y).map (openSquareCounit R' b a j c M'.obj (rho' M')) ≫
        (openSquareBScalar phi b j hj).hom.app M'.obj =
      openSquareCounit R b a j c M.obj (rho M) ≫ (openSquareB R b j).map mu)

/-- The open-square counit with its actual adjunction normalization, support criterion
and arbitrary scalar-restriction compatibility.

Source: blueprint main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md,
paragraph (3), the all-continuous tame-boundary input; this is the agent-extracted lemma,
not a separately printed theorem (blueprint: lem-sfb-open-square-support-scalar-counit).

Proof plan. Transport internal modules to the reconstructed section-ring sheaves using
lem-pd-section-derived-pushpull-normalization and lem-sfb-internal-section-scalar-adjunction.
The coefficient alpha isomorphisms make inverse images exact. Noetherianity makes all
opens quasi-compact. By lem-weil-pbc-proetale-ringed-open-closed, the exact open adjunction
has invertible unit. Termwise homotopy adjunction and lem-sfb-adjunction-localization give
the specified derived units and counits. For a K-injective I on V, b^*I is K-injective,
since b_! is its exact left adjoint (lem-weil-pbc-right-adjoint-preserves-kinjective).
The slice identification I(V times_Y E) = I(W times_O E), normalized by
lem-sfb-proetale-open-restriction-counit, computes the derived restriction mate. Compose
with Ra_* of the inverse open unit to obtain precisely rho and its naturality.
The inverse adjunction bijection sends t to c_!(t) followed by the actual counit, proving
the formula for e and its naturality by the triangle identity. If i^* B vanishes, the
09AH short exact localization sequence applied to each cohomology sheaf makes the actual
counit an isomorphism on cohomology, hence in the derived category. Thus e is invertible.
For an arbitrary coefficient map, lem-weil-pbc-ring-sheaf-change-adjunction identifies
restriction with inverse and derived direct images and their actual adjunctions. No
preservation of injectives by restriction is needed. Extension by zero has the identical
underlying presheaf, action and sheafification before and after restriction; its units
and counits therefore agree. Termwise localization retains these equations. The open
slice comparison is the mate of the sectionwise open-extension comparison, so
lem-sf-ring-sheaf-base-change-mates and lem-weil-pbc-mate-pasting identify its scalar
restriction, and also rho, since the open unit is preserved. Finally naturality of rho
on mu gives equality of the two transposes of the displayed mixed-coefficient arrows.
Injectivity of the actual open adjunction Hom bijection proves that equality without
any vanishing hypothesis or scalar-extension/direct-image interchange. -/
theorem openSquare_support_scalar_counit
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {V O Y Z : Scheme.{u}} [IsLocallyNoetherian Y] [CompactSpace Y]
    (j : V ⟶ Y) (c : O ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion c]
    (i : Z ⟶ Y) [IsClosedImmersion i] [IsReduced Z]
    (hcomplement : Set.range i = (Set.range c)ᶜ) :
    ∃ rho : OpenSquareRhoFamily R (pullback.fst j c) (pullback.snd j c) j c,
      OpenSquareCounitAssertions R (pullback.fst j c) (pullback.snd j c) j c
        (CommSq.mk (pullback.condition (f := j) (g := c))) i rho ∧
      ∀ (R' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        [MonObj R'] [IsCommMonObj R'] (phi : R ⟶ R') [IsMonHom phi],
        ∃ rho' : OpenSquareRhoFamily R' (pullback.fst j c) (pullback.snd j c) j c,
          OpenSquareCounitAssertions R' (pullback.fst j c) (pullback.snd j c) j c
            (CommSq.mk (pullback.condition (f := j) (g := c))) i rho' ∧
          OpenSquareScalarAssertions phi (pullback.fst j c) (pullback.snd j c) j c
            (CommSq.mk (pullback.condition (f := j) (g := c))) rho rho' := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
