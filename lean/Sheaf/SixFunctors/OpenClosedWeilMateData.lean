/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.WeilIndSheafCategory
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.IntegralPullbackCompletedComparison
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.Paper.IntegralCompactSupportCoefficientData
public import Sheaf.Paper.FieldWeilShriekShiftData
public import Sheaf.Paper.ZlFrobeniusCompactSupportComparison
public import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison


/-! # Explicit open and closed Frobenius mates

Source: main-20261015, open/closed localization proof, Weil-structures paragraph
(blueprint: lem-sf-open-closed-weil-mate-structures).

## Main declarations

* `OpenClosedWeilMateAssertions`: the literal three-factor words and Weil squares.
* `RestrictedOpenClosedWeilMateAssertions`: those words on finite and integral objects.
* `OpenClosedScalarMateWords`: normalized scalar transport of the same maps.
* `sfCompletionOpenClosedWeilMateAssertions`: normalized ordinary-to-tower transport.
* `sfRationalizationOpenClosedWeilMateAssertions`: pinned integral-to-rational transport.
* `sf_openClosed_weil_mate_structures`: the four stages and their fixed comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe uX vX uU vU uZ vZ uX' vX' uU' vU' uZ' vZ' u v
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory
namespace WeilConjectures

attribute [local instance 2000] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory

/-- The explicit mate words, normalized equations, and induced outer Weil structures.
All functors and adjunctions are arguments, so the words use their actual units and counits.
Source: main-20261015, open/closed localization, Weil-structures paragraph
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def OpenClosedWeilMateAssertions
    {X : Type uX} [Category.{vX} X]
    {U : Type uU} [Category.{vU} U]
    {Z : Type uZ} [Category.{vZ} Z]
    (jL : U ⥤ X) (jR : X ⥤ U) (iL : X ⥤ Z) (iR : Z ⥤ X)
    (adjJ : jL ⊣ jR) (adjI : iL ⊣ iR)
    (FX : X ⥤ X) (FU : U ⥤ U) (FZ : Z ⥤ Z)
    (b : jR ⋙ FU ≅ FX ⋙ jR) (d : iL ⋙ FZ ≅ FX ⋙ iL) : Prop :=
  ∃ (alpha : FU ⋙ jL ≅ jL ⋙ FX) (c : iR ⋙ FX ≅ FZ ⋙ iR),
    alpha.hom = ((mateEquiv adjJ adjJ).symm
      (TwoSquare.mk _ _ _ _ b.hom)).natTrans ∧
    c.hom = (mateEquiv adjI adjI (TwoSquare.mk _ _ _ _ d.inv)).natTrans ∧
    (∀ N : U, alpha.hom.app N =
      jL.map (FU.map (adjJ.unit.app N)) ≫
        jL.map (b.hom.app (jL.obj N)) ≫ adjJ.counit.app (FX.obj (jL.obj N))) ∧
    (∀ M : Z, c.hom.app M = adjI.unit.app (FX.obj (iR.obj M)) ≫
      iR.map (d.inv.app (iR.obj M)) ≫ iR.map (FZ.map (adjI.counit.app M))) ∧
    (∀ K : X, FX.map (adjJ.counit.app K) =
      alpha.inv.app (jR.obj K) ≫ jL.map (b.hom.app K) ≫ adjJ.counit.app (FX.obj K)) ∧
    (∀ K : X, FX.map (adjI.unit.app K) ≫ c.hom.app (iL.obj K) ≫
      iR.map (d.hom.app K) = adjI.unit.app (FX.obj K)) ∧
    (∀ (K : X) (theta : FX.obj K ≅ K),
      IsIso (alpha.inv.app (jR.obj K) ≫ jL.map (b.hom.app K) ≫
        jL.map (jR.map theta.hom)) ∧
      IsIso (c.hom.app (iL.obj K) ≫ iR.map (d.hom.app K) ≫
        iR.map (iL.map theta.hom)) ∧
      (alpha.inv.app (jR.obj K) ≫ jL.map (b.hom.app K) ≫
          jL.map (jR.map theta.hom)) ≫ adjJ.counit.app K =
        FX.map (adjJ.counit.app K) ≫ theta.hom ∧
      theta.hom ≫ adjI.unit.app K =
        FX.map (adjI.unit.app K) ≫ (c.hom.app (iL.obj K) ≫
          iR.map (d.hom.app K) ≫ iR.map (iL.map theta.hom)))

/-- The canonical left-adjoint mate of the pullback square, before inversion.
Source: main-20261015, localization, explicit alpha formula
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def openClosedAlpha
    {X : Type uX} [Category.{vX} X] {U : Type uU} [Category.{vU} U]
    {jL : U ⥤ X} {jR : X ⥤ U} (adjJ : jL ⊣ jR)
    {FX : X ⥤ X} {FU : U ⥤ U} (b : jR ⋙ FU ≅ FX ⋙ jR) :
    FU ⋙ jL ⟶ jL ⋙ FX :=
  ((mateEquiv adjJ adjJ).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans

/-- The canonical right-adjoint mate of the inverse closed pullback square.
Source: main-20261015, localization, explicit c formula
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def openClosedC
    {X : Type uX} [Category.{vX} X] {Z : Type uZ} [Category.{vZ} Z]
    {iL : X ⥤ Z} {iR : Z ⥤ X} (adjI : iL ⊣ iR)
    {FX : X ⥤ X} {FZ : Z ⥤ Z} (d : iL ⋙ FZ ≅ FX ⋙ iL) :
    iR ⋙ FX ⟶ FZ ⋙ iR :=
  (mateEquiv adjI adjI (TwoSquare.mk _ _ _ _ d.inv)).natTrans

/-- The same assertions on specified full bounded constructible subcategories.
The ordinary derived adjunctions supply the maps. Invertibility is asserted only on
objects in the indicated subcategories; no statement on arbitrary unbounded inputs is made.
Sources: main-20261015 localization, finite and integral paragraphs and Weil paragraph
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def RestrictedOpenClosedWeilMateAssertions
    {X : Type uX} [Category.{vX} X]
    {U : Type uU} [Category.{vU} U]
    {Z : Type uZ} [Category.{vZ} Z]
    (PX : ObjectProperty X) (PU : ObjectProperty U) (PZ : ObjectProperty Z)
    (jL : U ⥤ X) (jR : X ⥤ U) (iL : X ⥤ Z) (iR : Z ⥤ X)
    (adjJ : jL ⊣ jR) (adjI : iL ⊣ iR)
    (FX : X ⥤ X) (FU : U ⥤ U) (FZ : Z ⥤ Z)
    (b : jR ⋙ FU ≅ FX ⋙ jR) (d : iL ⋙ FZ ≅ FX ⋙ iL) : Prop :=
  (∀ N : U, PU N → IsIso ((openClosedAlpha adjJ b).app N)) ∧
  (∀ M : Z, PZ M → IsIso ((openClosedC adjI d).app M)) ∧
  (∀ N : U, PU N → (openClosedAlpha adjJ b).app N =
    jL.map (FU.map (adjJ.unit.app N)) ≫ jL.map (b.hom.app (jL.obj N)) ≫
      adjJ.counit.app (FX.obj (jL.obj N))) ∧
  (∀ M : Z, PZ M → (openClosedC adjI d).app M =
    adjI.unit.app (FX.obj (iR.obj M)) ≫ iR.map (d.inv.app (iR.obj M)) ≫
      iR.map (FZ.map (adjI.counit.app M))) ∧
  (∀ K : X, PX K → PU (jR.obj K) ∧ PZ (iL.obj K) ∧
    PX (jL.obj (jR.obj K)) ∧ PX (iR.obj (iL.obj K)) ∧
    ∃ (a : FX.obj (jL.obj (jR.obj K)) ≅ jL.obj (FU.obj (jR.obj K)))
      (c : FX.obj (iR.obj (iL.obj K)) ≅ iR.obj (FZ.obj (iL.obj K))),
      a.inv = (openClosedAlpha adjJ b).app (jR.obj K) ∧
      c.hom = (openClosedC adjI d).app (iL.obj K) ∧
      FX.map (adjJ.counit.app K) =
        a.hom ≫ jL.map (b.hom.app K) ≫ adjJ.counit.app (FX.obj K) ∧
      FX.map (adjI.unit.app K) ≫ c.hom ≫ iR.map (d.hom.app K) =
        adjI.unit.app (FX.obj K))

/-- Preservation of the actual adjunction maps and the two three-factor mate words.
The comparison arrows need not be invertible away from the bounded finite-Tor domain.
Source: main-20261015 localization, coefficient passage and Weil paragraph
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def OpenClosedScalarMateWords
    {X : Type uX} [Category.{vX} X] {U : Type uU} [Category.{vU} U]
    {Z : Type uZ} [Category.{vZ} Z]
    {X' : Type uX'} [Category.{vX'} X'] {U' : Type uU'} [Category.{vU'} U']
    {Z' : Type uZ'} [Category.{vZ'} Z']
    (PX : ObjectProperty X) (PU : ObjectProperty U) (PZ : ObjectProperty Z)
    {J : U ⥤ X} {j : X ⥤ U} {i : X ⥤ Z} {I : Z ⥤ X}
    {J' : U' ⥤ X'} {j' : X' ⥤ U'} {i' : X' ⥤ Z'} {I' : Z' ⥤ X'}
    (aj : J ⊣ j) (ai : i ⊣ I) (aj' : J' ⊣ j') (ai' : i' ⊣ I')
    {FX : X ⥤ X} {FU : U ⥤ U} {FZ : Z ⥤ Z}
    {FX' : X' ⥤ X'} {FU' : U' ⥤ U'} {FZ' : Z' ⥤ Z'}
    (b : j ⋙ FU ≅ FX ⋙ j) (d : i ⋙ FZ ≅ FX ⋙ i)
    (b' : j' ⋙ FU' ≅ FX' ⋙ j') (d' : i' ⋙ FZ' ≅ FX' ⋙ i')
    (TX : X ⥤ X') (TU : U ⥤ U') (TZ : Z ⥤ Z')
    (sJ : J ⋙ TX ⟶ TU ⋙ J') (sj : j ⋙ TU ≅ TX ⋙ j')
    (si : i ⋙ TZ ≅ TX ⋙ i') (sI : I ⋙ TX ⟶ TZ ⋙ I')
    (sFX : FX ⋙ TX ≅ TX ⋙ FX') (sFU : FU ⋙ TU ≅ TU ⋙ FU')
    (sFZ : FZ ⋙ TZ ≅ TZ ⋙ FZ') : Prop :=
  (∀ N : U, PU N → IsIso (sJ.app N)) ∧
  (∀ M : Z, PZ M → IsIso (sI.app M)) ∧
  (∀ K : X, PX K → TU.map (b.hom.app K) ≫ sj.hom.app (FX.obj K) ≫
      j'.map (sFX.hom.app K) =
    sFU.hom.app (j.obj K) ≫ FU'.map (sj.hom.app K) ≫ b'.hom.app (TX.obj K)) ∧
  (∀ K : X, PX K → TZ.map (d.hom.app K) ≫ si.hom.app (FX.obj K) ≫
      i'.map (sFX.hom.app K) =
    sFZ.hom.app (i.obj K) ≫ FZ'.map (si.hom.app K) ≫ d'.hom.app (TX.obj K)) ∧
  (∀ N : U, PU N → TU.map (aj.unit.app N) ≫ sj.hom.app (J.obj N) ≫
    j'.map (sJ.app N) = aj'.unit.app (TU.obj N)) ∧
  (∀ K : X, PX K → sJ.app (j.obj K) ≫ J'.map (sj.hom.app K) ≫
    aj'.counit.app (TX.obj K) = TX.map (aj.counit.app K)) ∧
  (∀ K : X, PX K → ai'.unit.app (TX.obj K) ≫ I'.map (si.inv.app K) =
    TX.map (ai.unit.app K) ≫ sI.app (i.obj K)) ∧
  (∀ M : Z, PZ M → i'.map (sI.app M) ≫ ai'.counit.app (TZ.obj M) =
    si.inv.app (I.obj M) ≫ TZ.map (ai.counit.app M)) ∧
  (∀ N : U, PU N → TX.map ((openClosedAlpha aj b).app N) ≫
      sFX.hom.app (J.obj N) ≫ FX'.map (sJ.app N) =
    sJ.app (FU.obj N) ≫ J'.map (sFU.hom.app N) ≫
      (openClosedAlpha aj' b').app (TU.obj N)) ∧
  (∀ M : Z, PZ M → TX.map ((openClosedC ai d).app M) ≫
      sI.app (FZ.obj M) ≫ I'.map (sFZ.hom.app M) =
    sFX.hom.app (I.obj M) ≫ FX'.map (sI.app M) ≫
      (openClosedC ai' d').app (TZ.obj M))

/-- The coefficient comparisons for the adjoints are their specified mates.
The inverse open comparison and the forward closed comparison are fixed, so the
existential isomorphism cannot be chosen independently of the pullback comparison.
Source: main-20261015 localization, rationalization and common-stage paragraphs
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def OpenClosedScalarMateLift
    {X : Type uX} [Category.{vX} X] {U : Type uU} [Category.{vU} U]
    {Z : Type uZ} [Category.{vZ} Z]
    {X' : Type uX'} [Category.{vX'} X'] {U' : Type uU'} [Category.{vU'} U']
    {Z' : Type uZ'} [Category.{vZ'} Z']
    {J : U ⥤ X} {j : X ⥤ U} {i : X ⥤ Z} {I : Z ⥤ X}
    {J' : U' ⥤ X'} {j' : X' ⥤ U'} {i' : X' ⥤ Z'} {I' : Z' ⥤ X'}
    (aj : J ⊣ j) (ai : i ⊣ I) (aj' : J' ⊣ j') (ai' : i' ⊣ I')
    {FX : X ⥤ X} {FU : U ⥤ U} {FZ : Z ⥤ Z}
    {FX' : X' ⥤ X'} {FU' : U' ⥤ U'} {FZ' : Z' ⥤ Z'}
    (b : j ⋙ FU ≅ FX ⋙ j) (d : i ⋙ FZ ≅ FX ⋙ i)
    (b' : j' ⋙ FU' ≅ FX' ⋙ j') (d' : i' ⋙ FZ' ≅ FX' ⋙ i')
    (TX : X ⥤ X') (TU : U ⥤ U') (TZ : Z ⥤ Z')
    (sj : j ⋙ TU ≅ TX ⋙ j') (si : i ⋙ TZ ≅ TX ⋙ i')
    (sFX : FX ⋙ TX ≅ TX ⋙ FX') (sFU : FU ⋙ TU ≅ TU ⋙ FU')
    (sFZ : FZ ⋙ TZ ≅ TZ ⋙ FZ') : Prop :=
  ∃ sJ : J ⋙ TX ≅ TU ⋙ J',
    sJ.inv = ((mateEquiv aj aj').symm (TwoSquare.mk _ _ _ _ sj.hom)).natTrans ∧
    OpenClosedScalarMateWords (fun _ ↦ True) (fun _ ↦ True) (fun _ ↦ True)
      aj ai aj' ai' b d b' d' TX TU TZ sJ.hom sj si
      (mateEquiv ai ai' (TwoSquare.mk _ _ _ _ si.inv)).natTrans sFX sFU sFZ

open AlgebraicGeometry AlgebraicGeometry.Scheme

/-- The finite statement on the literal bounded constructible full subcategories,
using exact intrinsic module pullback and the K-injective right-derived direct image.
The index n denotes exponent n+1, so every and only positive coefficient levels occur.
Source: main-20261015 localization, finite paragraph and Weil paragraph
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def sfFiniteOpenClosedWeilMateAssertions
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left] [IsClosedImmersion i₀.left]
    (n : ℕ) : Prop :=
  letI : IsOpenImmersion (zlFiberMap D j₀) :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance
  let A := Padic.coefficientExtensionRing l E (n + 1)
  letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  let J := sfIntrinsicDerivedOpen A (zlFiberMap D j₀)
  let jR := sfIntrinsicDerivedPullback A (zlFiberMap D j₀)
  let iL := sfIntrinsicDerivedPullback A (zlFiberMap D i₀)
  let I := proEtaleConstantDerivedDirectImage (zlFiberMap D i₀) A
  let FX := sfIntrinsicDerivedPullback A (D.geometricFrobenius X₀).hom
  let FU := sfIntrinsicDerivedPullback A (D.geometricFrobenius U₀).hom
  let FZ := sfIntrinsicDerivedPullback A (D.geometricFrobenius Z₀).hom
  let b := sfIntrinsicDerivedSquarePullback A (D.geometricFrobenius U₀).hom
    (zlFiberMap D j₀) (zlFiberMap D j₀) (D.geometricFrobenius X₀).hom
    (zlFrobenius_naturality D j₀)
  let d := sfIntrinsicDerivedSquarePullback A (D.geometricFrobenius Z₀).hom
    (zlFiberMap D i₀) (zlFiberMap D i₀) (D.geometricFrobenius X₀).hom
    (zlFrobenius_naturality D i₀)
  RestrictedOpenClosedWeilMateAssertions
    (X := proEtaleDerivedCategory (D.geometricFiber X₀).left A)
    (U := proEtaleDerivedCategory (D.geometricFiber U₀).left A)
    (Z := proEtaleDerivedCategory (D.geometricFiber Z₀).left A)
    (intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (D.geometricFiber X₀).left)
    (intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (D.geometricFiber U₀).left)
    (intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (D.geometricFiber Z₀).left)
    J jR iL I (exceptionalOpenAdjunction (zlFiberMap D j₀) A)
    ((sfIntrinsicConstantModuleAdjunction (zlFiberMap D i₀) A)
      |>.mapDerivedCategoryRightDerivedAdjunction.{u+1,u+1,u+2,u+2,u+2,u+2}) FX FU FZ b d

/-- Integral mate formulas in the ordinary completed-ring presentation, restricted
exactly to the recorded derived-complete constructible objects. The ordinary
adjunction units are retained; the completion identifications are separate below.
Source: main-20261015 localization, integral and Weil paragraphs
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def sfIntegralOpenClosedWeilMateAssertions
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left] : Prop :=
  letI : IsOpenImmersion (zlFiberMap D j₀) :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance
  let R := PurCompactSupport.completed l E
  let j := zlFiberMap D j₀
  let i := zlFiberMap D i₀
  RestrictedOpenClosedWeilMateAssertions
    (X := DerivedCategory.{u+2} (proEtaleRingModules (D.geometricFiber X₀).left
      (R.ring (D.geometricFiber X₀).left)))
    (U := DerivedCategory.{u+2} (proEtaleRingModules (D.geometricFiber U₀).left
      (R.ring (D.geometricFiber U₀).left)))
    (Z := DerivedCategory.{u+2} (proEtaleRingModules (D.geometricFiber Z₀).left
      (R.ring (D.geometricFiber Z₀).left)))
    (sfIntegralConstructible l E (D.geometricFiber X₀).left)
    (sfIntegralConstructible l E (D.geometricFiber U₀).left)
    (sfIntegralConstructible l E (D.geometricFiber Z₀).left)
    (PurCompactSupport.openExtension R j).mapDerivedCategory.{u+2,u+2}
    (PurCompactSupport.pull R j) (PurCompactSupport.pull R i) (PurCompactSupport.push R i)
    (PurCompactSupport.openDerivedAdjunction R j)
    (proEtaleRingDerivedAdjunction i (R.ring _) (R.ring _) (R.pull i))
    (zlAmbientFrobenius D l E X₀) (zlAmbientFrobenius D l E U₀)
    (zlAmbientFrobenius D l E Z₀)
    (zlAmbientFrobeniusSquare D j₀ l E) (zlAmbientFrobeniusSquare D i₀ l E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized finite ringed-site pullback in intrinsic constant-module coordinates.
Source: constant-section comparison in the coefficient-reduction construction
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def sfFiniteRingPullIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {V W : Scheme.{u}} (f : V ⟶ W) :
    PurCompactSupport.pull
        (PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)) f ≅
      sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  letI : (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f).Additive :=
    sfIntrinsicPullback_additive (Padic.coefficientExtensionRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteLimits
    (Padic.coefficientExtensionRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteColimits
    (Padic.coefficientExtensionRing l E (n + 1)) f
  Functor.mapDerivedCategoryNatIso (PurCompactSupport.finitePullbackIso l E n f)

/-- Finite Frobenius square in the normalized ringed-site presentation.
It is the intrinsic square conjugated by the fixed constant-section comparisons.
Source: main-20261015 localization, finite reduction and Weil paragraph
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def sfFiniteRingFrobeniusSquare
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {V₀ W₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType V₀.hom] [QuasiCompact V₀.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom] (f₀ : V₀ ⟶ W₀) :
    PurCompactSupport.pull
        (PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)) (zlFiberMap D f₀) ⋙
        PurCompactSupport.pull
          (PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n))
          (D.geometricFrobenius V₀).hom ≅
      PurCompactSupport.pull
        (PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n))
        (D.geometricFrobenius W₀).hom ⋙
        PurCompactSupport.pull
          (PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)) (zlFiberMap D f₀) :=
  let A := Padic.coefficientExtensionRing l E (n + 1)
  letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.le_add_left 1 n)
  Functor.isoWhiskerRight (sfFiniteRingPullIso l E n (zlFiberMap D f₀)) _ ≪≫
    Functor.isoWhiskerLeft _ (sfFiniteRingPullIso l E n (D.geometricFrobenius V₀).hom) ≪≫
    sfIntrinsicDerivedSquarePullback A (D.geometricFrobenius V₀).hom
      (zlFiberMap D f₀) (zlFiberMap D f₀) (D.geometricFrobenius W₀).hom
      (zlFrobenius_naturality D f₀) ≪≫
    Functor.isoWhiskerRight (sfFiniteRingPullIso l E n
      (D.geometricFrobenius W₀).hom).symm _ ≪≫
    Functor.isoWhiskerLeft _ (sfFiniteRingPullIso l E n (zlFiberMap D f₀)).symm

/-- Scalar transport of the two mate words through the actual coefficient adjunctions.
`a` is instantiated below by the fixed integral quotient, finite quotient, or completed
coefficient inclusion. The predicates specify only the bounded constructible inputs.
Source: main-20261015 localization, integral coefficient passage and Weil paragraph
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def sfRingScalarMateWords
    (D : FiniteFieldDatum.{u}) {R S : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S)
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    (PX : ObjectProperty (DerivedCategory (proEtaleRingModules (D.geometricFiber X₀).left
      (R.ring (D.geometricFiber X₀).left))))
    (PU : ObjectProperty (DerivedCategory (proEtaleRingModules (D.geometricFiber U₀).left
      (R.ring (D.geometricFiber U₀).left))))
    (PZ : ObjectProperty (DerivedCategory (proEtaleRingModules (D.geometricFiber Z₀).left
      (R.ring (D.geometricFiber Z₀).left))))
    (bR : PurCompactSupport.pull R (zlFiberMap D j₀) ⋙
        PurCompactSupport.pull R (D.geometricFrobenius U₀).hom ≅
      PurCompactSupport.pull R (D.geometricFrobenius X₀).hom ⋙
        PurCompactSupport.pull R (zlFiberMap D j₀))
    (dR : PurCompactSupport.pull R (zlFiberMap D i₀) ⋙
        PurCompactSupport.pull R (D.geometricFrobenius Z₀).hom ≅
      PurCompactSupport.pull R (D.geometricFrobenius X₀).hom ⋙
        PurCompactSupport.pull R (zlFiberMap D i₀))
    (bS : PurCompactSupport.pull S (zlFiberMap D j₀) ⋙
        PurCompactSupport.pull S (D.geometricFrobenius U₀).hom ≅
      PurCompactSupport.pull S (D.geometricFrobenius X₀).hom ⋙
        PurCompactSupport.pull S (zlFiberMap D j₀))
    (dS : PurCompactSupport.pull S (zlFiberMap D i₀) ⋙
        PurCompactSupport.pull S (D.geometricFrobenius Z₀).hom ≅
      PurCompactSupport.pull S (D.geometricFrobenius X₀).hom ⋙
        PurCompactSupport.pull S (zlFiberMap D i₀)) : Prop :=
  letI : IsOpenImmersion (zlFiberMap D j₀) :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance
  let j := zlFiberMap D j₀
  let i := zlFiberMap D i₀
  OpenClosedScalarMateWords PX PU PZ
    (PurCompactSupport.openDerivedAdjunction R j)
    (proEtaleRingDerivedAdjunction i (R.ring _) (R.ring _) (R.pull i))
    (PurCompactSupport.openDerivedAdjunction S j)
    (proEtaleRingDerivedAdjunction i (S.ring _) (S.ring _) (S.pull i)) bR dR bS dS
    (pbcDerivedExtend (a.map (D.geometricFiber X₀).left))
    (pbcDerivedExtend (a.map (D.geometricFiber U₀).left))
    (pbcDerivedExtend (a.map (D.geometricFiber Z₀).left))
    (PurCompactSupport.openComparison a j) (PurCompactSupport.scalarPull a j)
    (PurCompactSupport.scalarPull a i) (PurCompactSupport.properComparison a i)
    (PurCompactSupport.scalarPull a (D.geometricFrobenius X₀).hom)
    (PurCompactSupport.scalarPull a (D.geometricFrobenius U₀).hom)
    (PurCompactSupport.scalarPull a (D.geometricFrobenius Z₀).hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finite ringed and intrinsic presentations preserve the same specified mates.
The pullback comparisons are the published constant-section comparisons; the open
and direct-image comparisons are their adjunction mates, fixing both units and counits.
Source: main-20261015 localization, finite and coefficient paragraphs
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def sfFinitePresentationOpenClosedWeilMateAssertions
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    (n : ℕ) : Prop :=
  letI : IsOpenImmersion (zlFiberMap D j₀) :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance
  let A := Padic.coefficientExtensionRing l E (n + 1)
  letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.le_add_left 1 n)
  let R := PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)
  let j := zlFiberMap D j₀
  let i := zlFiberMap D i₀
  OpenClosedScalarMateLift
    (PurCompactSupport.openDerivedAdjunction R j)
    (proEtaleRingDerivedAdjunction i (R.ring _) (R.ring _) (R.pull i))
    (exceptionalOpenAdjunction j A)
    ((sfIntrinsicConstantModuleAdjunction i A)
      |>.mapDerivedCategoryRightDerivedAdjunction.{u+1,u+1,u+2,u+2,u+2,u+2})
    (sfFiniteRingFrobeniusSquare D l E n j₀) (sfFiniteRingFrobeniusSquare D l E n i₀)
    (sfIntrinsicDerivedSquarePullback A (D.geometricFrobenius U₀).hom j j
      (D.geometricFrobenius X₀).hom (zlFrobenius_naturality D j₀))
    (sfIntrinsicDerivedSquarePullback A (D.geometricFrobenius Z₀).hom i i
      (D.geometricFrobenius X₀).hom (zlFrobenius_naturality D i₀))
    (𝟭 _) (𝟭 _) (𝟭 _)
    (sfFiniteRingPullIso l E n j) (sfFiniteRingPullIso l E n i)
    (sfFiniteRingPullIso l E n (D.geometricFrobenius X₀).hom)
    (sfFiniteRingPullIso l E n (D.geometricFrobenius U₀).hom)
    (sfFiniteRingPullIso l E n (D.geometricFrobenius Z₀).hom)

/-- All integral quotient levels, all quotient transitions, and all finite extensions
use their prescribed scalar mates. The finite-to-finite clauses are restricted
to the finite-Tor constructible domain, and include repeated levels.
Source: main-20261015 localization, coefficient passage and Weil paragraph
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def sfCoefficientOpenClosedWeilMateAssertions
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀) [IsOpenImmersion j₀.left] : Prop :=
  (∀ n : ℕ, sfRingScalarMateWords D (PurCompactSupport.reduction l E (n + 1)
    (Nat.le_add_left 1 n)) j₀ i₀
    (sfIntegralConstructible l E (D.geometricFiber X₀).left)
    (sfIntegralConstructible l E (D.geometricFiber U₀).left)
    (sfIntegralConstructible l E (D.geometricFiber Z₀).left)
    (zlAmbientFrobeniusSquare D j₀ l E) (zlAmbientFrobeniusSquare D i₀ l E)
    (sfFiniteRingFrobeniusSquare D l E n j₀) (sfFiniteRingFrobeniusSquare D l E n i₀)) ∧
  (∀ (m n : ℕ) (h : n ≤ m), sfRingScalarMateWords D
    (PurCompactSupport.finiteQuotientChange l E (m + 1) (n + 1)
      (Nat.le_add_left 1 m) (Nat.le_add_left 1 n) (Nat.succ_le_succ h)) j₀ i₀
    (finiteTorConstructible l E (m + 1)
      (Nat.le_add_left 1 m) (D.geometricFiber X₀).left)
    (finiteTorConstructible l E (m + 1)
      (Nat.le_add_left 1 m) (D.geometricFiber U₀).left)
    (finiteTorConstructible l E (m + 1)
      (Nat.le_add_left 1 m) (D.geometricFiber Z₀).left)
    (sfFiniteRingFrobeniusSquare D l E m j₀) (sfFiniteRingFrobeniusSquare D l E m i₀)
    (sfFiniteRingFrobeniusSquare D l E n j₀) (sfFiniteRingFrobeniusSquare D l E n i₀)) ∧
  (∀ (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L), sfRingScalarMateWords D
    (PurCompactSupport.completedChange l E L ι) j₀ i₀
    (sfIntegralConstructible l E (D.geometricFiber X₀).left)
    (sfIntegralConstructible l E (D.geometricFiber U₀).left)
    (sfIntegralConstructible l E (D.geometricFiber Z₀).left)
    (zlAmbientFrobeniusSquare D j₀ l E) (zlAmbientFrobeniusSquare D i₀ l E)
    (zlAmbientFrobeniusSquare D j₀ l L) (zlAmbientFrobeniusSquare D i₀ l L))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The integral square on exactly the constructible functors that rational pullback
localizes. Its compositors are the fixed finite-reduction-normalized ones.
Source: main-20261015 localization, rational and Weil paragraphs
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def sfConstructibleIntegralFrobeniusSquare
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {V₀ W₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType V₀.hom] [QuasiCompact V₀.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom] (f₀ : V₀ ⟶ W₀) :=
  letI : ∀ x : (D.geometricFiber V₀).left,
      Invertible (l : (D.geometricFiber V₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl V₀ x
  letI : ∀ x : (D.geometricFiber W₀).left,
      Invertible (l : (D.geometricFiber W₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl W₀ x
  (zlIntegralPullComp l E (D.geometricFrobenius V₀).hom (zlFiberMap D f₀)).symm ≪≫
    eqToIso (congrArg (fun f ↦ constructibleIntegralPullback l E f)
      (zlFrobenius_naturality D f₀)) ≪≫
    zlIntegralPullComp l E (zlFiberMap D f₀) (D.geometricFrobenius W₀).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pin the tower-to-ordinary comparison by the actual completion unit and gamma.
The ordinary coefficient transport is fixed first on every tensor-unit generator
and then by its derived computation counit. Every constructible object is covered
by a complete coefficient representative; the equation holds for every such
representative and every identification, so it cannot hide an automorphism.
Comparison includes its finite-generator, projection and shift normalizations.
Source: main-20261015 localization, completion passage and Weil paragraph
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def sfCompletionPullbackComparisonPin
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {V W : Scheme.{u}} (f : V ⟶ W)
    [∀ x : V, Invertible (l : V.residueField x)]
    [∀ x : W, Invertible (l : W.residueField x)]
    (C : IntegralCompletedComparison.Comparison l E f)
    (s : constructibleIntegralPullback l E f ⋙ (sfIntegralConstructible l E V).ι ≅
      (sfIntegralConstructible l E W).ι ⋙ PurCompactSupport.pull
        (PurCompactSupport.completed l E) f) : Prop :=
  let R := PurCompactSupport.completed l E
  let d := pbcIntegralDatum l E
  let mV := IntegralCompletedComparison.modules l E V
  let mW := IntegralCompletedComparison.modules l E W
  let tV := IntegralCompletedComparison.derived l E V
  let tW := IntegralCompletedComparison.derived l E W
  let p := proEtaleRingModulePullback f (R.ring W) (R.ring V) (R.pull f)
  (∀ K : sfIntegralConstructibleCategory l E W,
    ∃ (M : PbcCompletedDerived W d) (_hM : IntegralCompletedComparison.Complete l E M),
      Nonempty (tW.obj M ≅ K.obj)) ∧
  ∃ (rho₀ : pbcActualModulePull f d ⋙ mV ≅ mW ⋙ p)
    (rho : pbcActualDerivedPull f d ⋙ tV ≅ tW ⋙ PurCompactSupport.pull R f),
    (∀ (M : pbcModules W (pbcAdicCompletion W d)) (A : W.ProEt)
      (x : M.val.obj (Opposite.op A)),
      ((rho₀.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj A)))
          (pbcActualModuleUnitSection f d M A x) =
        proEtaleRingModuleUnitSection f (R.ring W) (R.ring V) (R.pull f)
          (mW.obj M) A x) ∧
    (∀ P : CochainComplex (pbcModules W (pbcAdicCompletion W d)) ℤ,
      rho.hom.app (DerivedCategory.Q.obj P) ≫
          (PurCompactSupport.pull R f).map (mW.mapDerivedCategoryFactors.hom.app P) ≫
          (proEtaleRingDerivedPullbackFactors f (R.ring W) (R.ring V) (R.pull f)).hom.app
            ((mW.mapHomologicalComplex (.up ℤ)).obj P) =
        tV.map (pbcActualPullComplexCounit f d P) ≫
          mV.mapDerivedCategoryFactors.hom.app
            (((pbcActualModulePull f d).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex rho₀.hom (.up ℤ)).app P)) ∧
    (∀ (K : sfIntegralConstructibleCategory l E W) (M : PbcCompletedDerived W d)
      (hM : IntegralCompletedComparison.Complete l E M) (e : tW.obj M ≅ K.obj),
      (PurCompactSupport.pull R f).map e.hom ≫ s.inv.app K =
        rho.inv.app M ≫
          tV.map ((pbcActualStrictCompletedPullUnit d f).app M ≫
            (IntegralCompletedComparison.towerIso l E f).hom.app ⟨M, C.intrinsic M hM⟩) ≫
          (C.gamma M hM).inv ≫ (integralDerivedPullback l E f).map e.hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completion carries the ordinary integral mate words to the very tower functors
subsequently rationalized. The inclusion comparisons are pinned to the actual
completion map by sfCompletionPullbackComparisonPin, for every normalized gamma.
The adjoint comparisons are fixed mates. The b/d equations, all four adjunction
maps and both three-factor words are the content of OpenClosedScalarMateLift.
Its direction is tower to ordinary along the full inclusions; invertibility
therefore identifies the ordinary maps with these same integral maps.
Source: main-20261015 localization, integral and rational passages and Weil paragraph
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def sfCompletionOpenClosedWeilMateAssertions
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left] [IsClosedImmersion i₀.left] : Prop :=
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl U₀
  letI := sfWeilPrimeInvertible D l hl Z₀
  letI : IsOpenImmersion (zlFiberMap D j₀) :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance
  let R := PurCompactSupport.completed l E
  let j := constructibleIntegralPullback l E (zlFiberMap D j₀)
  let i := constructibleIntegralPullback l E (zlFiberMap D i₀)
  let FX := constructibleIntegralPullback l E (D.geometricFrobenius X₀).hom
  let FU := constructibleIntegralPullback l E (D.geometricFrobenius U₀).hom
  let FZ := constructibleIntegralPullback l E (D.geometricFrobenius Z₀).hom
  let b := sfConstructibleIntegralFrobeniusSquare D l hl E j₀
  let d := sfConstructibleIntegralFrobeniusSquare D l hl E i₀
  let TX := (sfIntegralConstructible l E (D.geometricFiber X₀).left).ι
  let TU := (sfIntegralConstructible l E (D.geometricFiber U₀).left).ι
  let TZ := (sfIntegralConstructible l E (D.geometricFiber Z₀).left).ι
  ∀ (Cj : IntegralCompletedComparison.Comparison l E (zlFiberMap D j₀))
    (Ci : IntegralCompletedComparison.Comparison l E (zlFiberMap D i₀))
    (CX : IntegralCompletedComparison.Comparison l E (D.geometricFrobenius X₀).hom)
    (CU : IntegralCompletedComparison.Comparison l E (D.geometricFrobenius U₀).hom)
    (CZ : IntegralCompletedComparison.Comparison l E (D.geometricFrobenius Z₀).hom),
  ∃ (J : sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left ⥤
        sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
    (I : sfIntegralConstructibleCategory l E (D.geometricFiber Z₀).left ⥤
        sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
    (aj : J ⊣ j) (ai : i ⊣ I)
    (sj : j ⋙ TU ≅ TX ⋙ PurCompactSupport.pull R (zlFiberMap D j₀))
    (si : i ⋙ TZ ≅ TX ⋙ PurCompactSupport.pull R (zlFiberMap D i₀))
    (sFX : FX ⋙ TX ≅ TX ⋙ zlAmbientFrobenius D l E X₀)
    (sFU : FU ⋙ TU ≅ TU ⋙ zlAmbientFrobenius D l E U₀)
    (sFZ : FZ ⋙ TZ ≅ TZ ⋙ zlAmbientFrobenius D l E Z₀),
    sfCompletionPullbackComparisonPin l E (zlFiberMap D j₀) Cj sj ∧
    sfCompletionPullbackComparisonPin l E (zlFiberMap D i₀) Ci si ∧
    sfCompletionPullbackComparisonPin l E (D.geometricFrobenius X₀).hom CX sFX ∧
    sfCompletionPullbackComparisonPin l E (D.geometricFrobenius U₀).hom CU sFU ∧
    sfCompletionPullbackComparisonPin l E (D.geometricFrobenius Z₀).hom CZ sFZ ∧
    OpenClosedScalarMateLift aj ai (PurCompactSupport.openDerivedAdjunction R
      (zlFiberMap D j₀)) (proEtaleRingDerivedAdjunction (zlFiberMap D i₀)
        (R.ring _) (R.ring _) (R.pull (zlFiberMap D i₀)))
      b d (zlAmbientFrobeniusSquare D j₀ l E) (zlAmbientFrobeniusSquare D i₀ l E)
      TX TU TZ sj si sFX sFU sFZ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rationalization of the specified integral mates and all four adjunction maps.
The source pullbacks are literally those localized by rationalDerivedPullback.
The five pullback comparisons have identity components under that construction's
object identification. The open and closed operation comparisons are their fixed
mates, and OpenClosedScalarMateWords explicitly preserves alpha, c, b, d, both
units and both counits. Thus no choice of a rational adjoint can hide a change
of the mate maps during rationalization.
Source: main-20261015 localization, rational and Weil paragraphs
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def sfRationalizationOpenClosedWeilMateAssertions
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left] [IsClosedImmersion i₀.left] : Prop :=
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl U₀
  letI := sfWeilPrimeInvertible D l hl Z₀
  let j := constructibleIntegralPullback l E (zlFiberMap D j₀)
  let i := constructibleIntegralPullback l E (zlFiberMap D i₀)
  let FX := constructibleIntegralPullback l E (D.geometricFrobenius X₀).hom
  let FU := constructibleIntegralPullback l E (D.geometricFrobenius U₀).hom
  let FZ := constructibleIntegralPullback l E (D.geometricFrobenius Z₀).hom
  let b := sfConstructibleIntegralFrobeniusSquare D l hl E j₀
  let d := sfConstructibleIntegralFrobeniusSquare D l hl E i₀
  let TX := sfRationalConstructibleLocalization l E (D.geometricFiber X₀).left
  let TU := sfRationalConstructibleLocalization l E (D.geometricFiber U₀).left
  let TZ := sfRationalConstructibleLocalization l E (D.geometricFiber Z₀).left
  ∃ (J : sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left ⥤
        sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
    (I : sfIntegralConstructibleCategory l E (D.geometricFiber Z₀).left ⥤
        sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
    (aj : J ⊣ j) (ai : i ⊣ I)
    (sj : j ⋙ TU ≅ TX ⋙ fieldWeilPull D l hl E j₀)
    (si : i ⋙ TZ ≅ TX ⋙ fieldWeilPull D l hl E i₀)
    (sFX : FX ⋙ TX ≅ TX ⋙ sfWeilFrobeniusPullback D l hl X₀ E)
    (sFU : FU ⋙ TU ≅ TU ⋙ sfWeilFrobeniusPullback D l hl U₀ E)
    (sFZ : FZ ⋙ TZ ≅ TZ ⋙ sfWeilFrobeniusPullback D l hl Z₀ E),
    (∀ N, IsIso ((openClosedAlpha aj b).app N)) ∧
    (∀ M, IsIso ((openClosedC ai d).app M)) ∧
    (∀ K, HEq (sj.hom.app K) (𝟙 (TU.obj (j.obj K)))) ∧
    (∀ K, HEq (si.hom.app K) (𝟙 (TZ.obj (i.obj K)))) ∧
    (∀ K, HEq (sFX.hom.app K) (𝟙 (TX.obj (FX.obj K)))) ∧
    (∀ K, HEq (sFU.hom.app K) (𝟙 (TU.obj (FU.obj K)))) ∧
    (∀ K, HEq (sFZ.hom.app K) (𝟙 (TZ.obj (FZ.obj K)))) ∧
    OpenClosedScalarMateLift aj ai
      (fieldWeilOpenAdj D l hl E j₀) (fieldWeilProperAdj D l hl E i₀)
      b d (fieldWeilPullSquare D l hl E j₀) (fieldWeilPullSquare D l hl E i₀)
      TX TU TZ sj si sFX sFU sFZ

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Rational scalar extension preserves the actual mate words and adjunction maps.
The scalar pullback isomorphisms are the published maps obtained by localizing the
integral comparison with one, with its prescribed pure-tensor Hom formula.
Source: main-20261015 localization, rational and Weil paragraphs
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def sfRationalScalarOpenClosedWeilMateAssertions
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left] [IsClosedImmersion i₀.left] : Prop :=
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl U₀
  letI := sfWeilPrimeInvertible D l hl Z₀
  ∀ (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L),
    ∃ (sj : fieldWeilPull D l hl E j₀ ⋙
          sfRationalScalarExtension l E (D.geometricFiber U₀).left 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
        sfRationalScalarExtension l E (D.geometricFiber X₀).left 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙ fieldWeilPull D l hl L j₀)
      (si : fieldWeilPull D l hl E i₀ ⋙
          sfRationalScalarExtension l E (D.geometricFiber Z₀).left 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
        sfRationalScalarExtension l E (D.geometricFiber X₀).left 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙ fieldWeilPull D l hl L i₀)
      (sFX : sfWeilFrobeniusPullback D l hl X₀ E ⋙
          sfRationalScalarExtension l E (D.geometricFiber X₀).left 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
        sfRationalScalarExtension l E (D.geometricFiber X₀).left 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙
          sfWeilFrobeniusPullback D l hl X₀ L)
      (sFU : sfWeilFrobeniusPullback D l hl U₀ E ⋙
          sfRationalScalarExtension l E (D.geometricFiber U₀).left 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
        sfRationalScalarExtension l E (D.geometricFiber U₀).left 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙
          sfWeilFrobeniusPullback D l hl U₀ L)
      (sFZ : sfWeilFrobeniusPullback D l hl Z₀ E ⋙
          sfRationalScalarExtension l E (D.geometricFiber Z₀).left 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
        sfRationalScalarExtension l E (D.geometricFiber Z₀).left 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙
          sfWeilFrobeniusPullback D l hl Z₀ L),
      HEq sj (rationalPullbackScalarComparison (X := (D.geometricFiber U₀).left)
        (Y := (D.geometricFiber X₀).left) l E L ι (zlFiberMap D j₀)) ∧
      HEq si (rationalPullbackScalarComparison (X := (D.geometricFiber Z₀).left)
        (Y := (D.geometricFiber X₀).left) l E L ι (zlFiberMap D i₀)) ∧
      HEq sFX (rationalPullbackScalarComparison
        (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber X₀).left)
        l E L ι (D.geometricFrobenius X₀).hom) ∧
      HEq sFU (rationalPullbackScalarComparison
        (X := (D.geometricFiber U₀).left) (Y := (D.geometricFiber U₀).left)
        l E L ι (D.geometricFrobenius U₀).hom) ∧
      HEq sFZ (rationalPullbackScalarComparison
        (X := (D.geometricFiber Z₀).left) (Y := (D.geometricFiber Z₀).left)
        l E L ι (D.geometricFrobenius Z₀).hom) ∧
      OpenClosedScalarMateLift
        (fieldWeilOpenAdj D l hl E j₀) (fieldWeilProperAdj D l hl E i₀)
        (fieldWeilOpenAdj D l hl L j₀) (fieldWeilProperAdj D l hl L i₀)
        (fieldWeilPullSquare D l hl E j₀) (fieldWeilPullSquare D l hl E i₀)
        (fieldWeilPullSquare D l hl L j₀) (fieldWeilPullSquare D l hl L i₀)
        (sfRationalScalarExtension l E (D.geometricFiber X₀).left 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι)
        (sfRationalScalarExtension l E (D.geometricFiber U₀).left 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι)
        (sfRationalScalarExtension l E (D.geometricFiber Z₀).left 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι)
        sj si sFX sFU sFZ

/-- Descent of the same normalized words through every actual finite coefficient stage.
The inclusion/pullback comparisons have identity components under the published
object identification; the adjoint comparisons are their fixed mates.
Source: main-20261015 localization, common-stage and Weil paragraphs
(blueprint: lem-sf-open-closed-weil-mate-structures). -/
def sfCommonStageOpenClosedWeilMateAssertions
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left] [IsClosedImmersion i₀.left] : Prop :=
  ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
    let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L
    let TX := GeneralAlgebraicallyClosedCoefficients.inclusion
      (Y := (D.geometricFiber X₀).left) L
    let TU := GeneralAlgebraicallyClosedCoefficients.inclusion
      (Y := (D.geometricFiber U₀).left) L
    let TZ := GeneralAlgebraicallyClosedCoefficients.inclusion
      (Y := (D.geometricFiber Z₀).left) L
    ∃ (sj : fieldWeilPull D l hl E j₀ ⋙ TU ≅ TX ⋙ zlPull D l hl Ω j₀)
      (si : fieldWeilPull D l hl E i₀ ⋙ TZ ≅ TX ⋙ zlPull D l hl Ω i₀)
      (sFX : sfWeilFrobeniusPullback D l hl X₀ E ⋙ TX ≅
        TX ⋙ sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
      (sFU : sfWeilFrobeniusPullback D l hl U₀ E ⋙ TU ≅
        TU ⋙ sfCommonStageWeilFrobeniusPullback D l hl U₀ Ω)
      (sFZ : sfWeilFrobeniusPullback D l hl Z₀ E ⋙ TZ ≅
        TZ ⋙ sfCommonStageWeilFrobeniusPullback D l hl Z₀ Ω),
      (∀ K, HEq (sj.hom.app K) (𝟙 (TU.obj ((fieldWeilPull D l hl E j₀).obj K)))) ∧
      (∀ K, HEq (si.hom.app K) (𝟙 (TZ.obj ((fieldWeilPull D l hl E i₀).obj K)))) ∧
      (∀ K, HEq (sFX.hom.app K)
        (𝟙 (TX.obj ((sfWeilFrobeniusPullback D l hl X₀ E).obj K)))) ∧
      (∀ K, HEq (sFU.hom.app K)
        (𝟙 (TU.obj ((sfWeilFrobeniusPullback D l hl U₀ E).obj K)))) ∧
      (∀ K, HEq (sFZ.hom.app K)
        (𝟙 (TZ.obj ((sfWeilFrobeniusPullback D l hl Z₀ E).obj K)))) ∧
      OpenClosedScalarMateLift
        (fieldWeilOpenAdj D l hl E j₀) (fieldWeilProperAdj D l hl E i₀)
        (zlCommonStageOpenAdjunction D l hl Ω j₀)
        (zlCommonStageProperAdjunction D l hl Ω i₀)
        (fieldWeilPullSquare D l hl E j₀) (fieldWeilPullSquare D l hl E i₀)
        (zlFrobeniusSquare D l hl Ω j₀) (zlFrobeniusSquare D l hl Ω i₀)
        TX TU TZ sj si sFX sFU sFZ

end WeilConjectures
