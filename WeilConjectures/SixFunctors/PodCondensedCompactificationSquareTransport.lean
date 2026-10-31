/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.AlgebraicGeometry.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.CompactificationCoherenceCocycle
public import WeilConjectures.AlgebraicGeometry.CompactificationRefinementLocalizing
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenCoherenceData
public import WeilConjectures.CategoryTheory.ExactDerivedAdjunctionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenCoherence
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionNormalization
import WeilConjectures.AlgebraicGeometry.CondensedPullbackCoherence
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Canonical compactification mates under an isomorphic Cartesian realization

Source: latest blueprint, sec-six-functors-basics/sk-thm-sf-comp-composition/
det-sf-comp-composition-base-change.proof.md,
Clauses (1) and (3).
(blueprint: lem-pod-condensed-compactification-square-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
attribute [local irreducible] HasDerivedCategory.standard
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory DerivedCategory.monoidalClosed

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The dependency internal-module category, with its existing coefficient ring.
Source: clauses (1), (3), module-derived convention
(blueprint: lem-pod-condensed-compactification-square-transport). -/
abbrev PodModules (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)

/-- The ordinary unbounded derived category of the dependency module category.
Source: clauses (1), (3), module-derived convention
(blueprint: lem-pod-condensed-compactification-square-transport). -/
abbrev PodDerived (T : Scheme.{u}) := DerivedCategory (PodModules Λ T)

/-- The recorded total left derived module pullback.
Source: clauses (1), (3), module-derived convention
(blueprint: lem-pod-condensed-compactification-square-transport). -/
abbrev PodPullback {A B : Scheme.{u}} (a : A ⟶ B) :
    PodDerived Λ B ⥤ PodDerived Λ A := moduleObjectDerivedPullback Λ a

/-- The recorded total right derived module direct image.
Source: clauses (1), (3), module-derived convention
(blueprint: lem-pod-condensed-compactification-square-transport). -/
abbrev PodPushforward {A B : Scheme.{u}} (a : A ⟶ B) :
    PodDerived Λ A ⥤ PodDerived Λ B := moduleObjectDerivedPushforward Λ a

/-- The recorded exact extension by zero, derived termwise.
Source: clauses (1), (3), module-derived convention
(blueprint: lem-pod-condensed-compactification-square-transport). -/
abbrev PodOpenLowerShriek {A B : Scheme.{u}} (a : A ⟶ B) [IsOpenImmersion a] :
    PodDerived Λ A ⥤ PodDerived Λ B :=
  (openImmersionLowerShriek Λ a).mapDerivedCategory

/-- The dependency compactification lower shriek, in diagrammatic functor order.
Source: clauses (1), (3), module-derived convention
(blueprint: lem-pod-condensed-compactification-square-transport). -/
abbrev PodCompactSupport {A B : Scheme.{u}} {f : A ⟶ B}
    (c : Compactification f) : PodDerived Λ A ⥤ PodDerived Λ B :=
  rightDerivedLowerShriekOfCompactification Λ c

/-- Transport a literal pullback compactification through the supplied source and ambient
scheme isomorphisms.
Source: coordinate paragraph of clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podRealizedCompactification {X X' Z Y : Scheme.{u}}
    {f : X' ⟶ Y} (c : Compactification f) (eX : X ≅ X') (eZ : Z ≅ c.Z) :
    Compactification (eX.hom ≫ f) where
  Z := Z
  g := eZ.hom ≫ c.g
  i := eX.hom ≫ c.i ≫ eZ.inv
  comm := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun a ↦ eX.hom ≫ a) c.comm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The literal pulled-back boundary compactification.
Source: base change in clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podPullbackBoundary {X Y Y' : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c : Compactification.BoundaryCompactification f) (v : Y' ⟶ Y) :
    Compactification.BoundaryCompactification (pullback.snd f v) :=
  detSfBoundaryCompactification (c.obj.obj.baseChange v)

/-- The realized boundary compactification, with the prescribed coordinate formulas.
Source: the coordinate paragraph in clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podRealizedBoundary {X X' Z Y : Scheme.{u}} {f : X' ⟶ Y} [QuasiCompact f]
    (c : Compactification.BoundaryCompactification f) (eX : X ≅ X')
    (eZ : Z ≅ c.obj.obj.Z) :
    Compactification.BoundaryCompactification (eX.hom ≫ f) :=
  detSfBoundaryCompactification (podRealizedCompactification c.obj.obj eX eZ)

/-- Record the canonical fibre-product identification of a proved Cartesian square.
This only packages the existing universal-property isomorphism and its projection equations.
Source: the chosen Cartesian realizations in clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podChosenCartesianSquare {A B C D : Scheme.{u}} {a : A ⟶ B} {b : A ⟶ C}
    {c : B ⟶ D} {d : C ⟶ D} (sq : IsPullback a b c d) :
    ChosenCartesianSquare a b c d where
  toCommSq := sq.toCommSq
  isoPullback := sq.isoPullback
  hom_fst := sq.isoPullback_hom_fst
  hom_snd := sq.isoPullback_hom_snd

/-- The canonical inverse open exchange on a chosen Cartesian square, with the original exact
open units and counits. This is the recipe of `detSfOpenBaseChangeMap` on any Cartesian realization.
Source: clause (1), open unit--square--counit recipe
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podInverseOpenExchange {A B A' B' : Scheme.{u}}
    {i : A ⟶ B} {i' : A' ⟶ B'} {a : A' ⟶ A} {b : B' ⟶ B}
    [IsOpenImmersion i] [IsOpenImmersion i'] (sq : ChosenCartesianSquare a i' i b) :
    PodPullback Λ a ⋙ PodOpenLowerShriek Λ i' ⟶
      PodOpenLowerShriek Λ i ⋙ PodPullback Λ b :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).unit
      (PodPullback Λ a ⋙ PodOpenLowerShriek Λ i') ≫
    (Functor.squareTransport (PodOpenLowerShriek Λ i) (PodOpenLowerShriek Λ i')
      (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ i).symm
          (PodPullback Λ a) ≪≫
        (condensedAmbientPullbackComparison Λ sq).symm ≪≫
        Functor.isoWhiskerLeft (PodPullback Λ b)
          (leftDerivedUpperStarIsoMapDerivedCategory Λ i'))).hom ≫
    Functor.whiskerLeft (PodOpenLowerShriek Λ i ⋙ PodPullback Λ b)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i').counit ≫
    (Functor.rightUnitor _).hom

/-- Proper mate over the identity of the base; the identity comparison is the canonical
module-derived one, not a selected automorphism of the identity.
Source: definition of chi in clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podProperIdentityExchange {Z Z' Y : Scheme.{u}} (p : Z ⟶ Y)
    (e : Z' ≅ Z) :
    PodPushforward Λ p ⟶ PodPullback Λ e.hom ⋙ PodPushforward Λ (e.hom ≫ p) :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft (PodPushforward Λ p) (leftDerivedUpperStarId Λ Y).inv ≫
    condensedAmbientExchange Λ (podChosenCartesianSquare
      (IsPullback.of_horiz_isIso
        (⟨(Category.comp_id (e.hom ≫ p)).symm⟩ :
          CommSq e.hom (e.hom ≫ p) p (𝟙 Y))))

/-- The open square on the realized pullback, with both coordinate maps fixed.
Source: the coordinate paragraph of clauses (1), (3).
Proof: compose the literal open square with eX, insert eZ inverse followed by eZ,
and cancel that identity. The resulting equation is the literal open projection equation.
Transport its pullback universal property along eX and eZ; the inverse isomorphisms
transport each cone and the unique map back, so the square remains Cartesian.
(blueprint: lem-pod-condensed-compactification-square-transport). -/
theorem podRealizedOpenSquare {X Y Y' T Z : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (v : Y' ⟶ Y) (eX : T ≅ pullback f v)
    (eZ : Z ≅ pullback c.g v) :
    IsPullback (eX.hom ≫ pullback.fst f v)
      (podRealizedCompactification (c.baseChange v) eX eZ).i c.i
      (eZ.hom ≫ pullback.fst c.g v) := by
  have h := c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f v)
  apply h.of_iso eX.symm (Iso.refl _) eZ.symm (Iso.refl _)
  · simp
  · simp [podRealizedCompactification, Compactification.baseChange,
      Compactification.ofIsPullback]
  · simp
  · simp

/-- The proper square on the realized pullback.
Source: the coordinate paragraph of clauses (1), (3).
Proof: precompose the literal pullback projection equation with eZ and use associativity.
Transport the literal pullback universal property along eZ, using its inverse to
transport the unique cone map. This also proves the Cartesian assertion.
(blueprint: lem-pod-condensed-compactification-square-transport). -/
theorem podRealizedProperSquare {X Y Y' T Z : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (v : Y' ⟶ Y) (eX : T ≅ pullback f v)
    (eZ : Z ≅ pullback c.g v) :
    IsPullback (eZ.hom ≫ pullback.fst c.g v)
      (podRealizedCompactification (c.baseChange v) eX eZ).g c.g v := by
  have h := IsPullback.of_hasPullback c.g v
  apply h.of_iso eZ.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · simp [podRealizedCompactification]
  · simp
  · simp

/-- The normalized coordinate square for the open part of chi.
Source: the definition of chi in clauses (1), (3).
Proof: expand the realized open as eX followed by the old open and eZ inverse;
postcomposition with eZ cancels the inverse, giving the required commutative square.
Its two horizontal maps are isomorphisms, so the square has the pullback universal property.
(blueprint: lem-pod-condensed-compactification-square-transport). -/
theorem podCoordinateOpenSquare {A B T Z : Scheme.{u}} {f : A ⟶ B}
    (c : Compactification f) (eX : T ≅ A) (eZ : Z ≅ c.Z) :
    IsPullback eX.hom (podRealizedCompactification c eX eZ).i c.i eZ.hom := by
  apply IsPullback.of_horiz_isIso
  simp [podRealizedCompactification]

/-- The proper-mate-then-open composite on any realized compactification square.
Source: the recipe for B in clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podCompactSupportExchange {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f') (v : Y' ⟶ Y)
    (u : X' ⟶ X) (z : c'.Z ⟶ c.Z) (sq : ChosenCartesianSquare z c'.g c.g v)
    (b : PodOpenLowerShriek Λ c.i ⋙ PodPullback Λ z ≅
      PodPullback Λ u ⋙ PodOpenLowerShriek Λ c'.i) :
    PodCompactSupport Λ c ⋙ PodPullback Λ v ⟶
      PodPullback Λ u ⋙ PodCompactSupport Λ c' :=
  Functor.whiskerLeft (PodOpenLowerShriek Λ c.i) (condensedAmbientExchange Λ sq) ≫
    Functor.whiskerRight b.hom (PodPushforward Λ c'.g)

/-- The comparison chi, formed from precisely its proper mate and open exchange factors.
Source: the displayed definition of chi in clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podCompactificationComparison {A B T Z : Scheme.{u}} {f : A ⟶ B}
    (c : Compactification f) (eX : T ≅ A) (eZ : Z ≅ c.Z)
    (q : PodPushforward Λ c.g ≅
      PodPullback Λ eZ.hom ⋙ PodPushforward Λ (eZ.hom ≫ c.g))
    (b : PodOpenLowerShriek Λ c.i ⋙ PodPullback Λ eZ.hom ≅
      PodPullback Λ eX.hom ⋙
        PodOpenLowerShriek Λ (podRealizedCompactification c eX eZ).i) :
    PodCompactSupport Λ c ≅
      PodPullback Λ eX.hom ⋙
        PodCompactSupport Λ (podRealizedCompactification c eX eZ) :=
  Functor.isoWhiskerLeft (PodOpenLowerShriek Λ c.i) q ≪≫
    Functor.isoWhiskerRight b (PodPushforward Λ (eZ.hom ≫ c.g))

/-- One compactification's fixed coordinate comparisons, their separate factor equalities,
and the resulting compact-support transport equation. The inverse open arrows and q.hom
are fixed by the published units, counits and pullback compositors.
Source: clauses (1), (3), expanded in the node proof steps 2--5
(blueprint: lem-pod-condensed-compactification-square-transport). -/
structure PodCompactificationCoordinateData {X Y Y' T Z : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (v : Y' ⟶ Y) (eX : T ≅ pullback f v)
    (eZ : Z ≅ pullback c.g v) where
  /-- Proper comparison on the entire unbounded category. -/
  properIso : PodPushforward Λ (pullback.snd c.g v) ≅
    PodPullback Λ eZ.hom ⋙ PodPushforward Λ (eZ.hom ≫ pullback.snd c.g v)
  /-- The identity-base proper mate, with canonical identity comparison. -/
  properIso_hom : properIso.hom = podProperIdentityExchange Λ (pullback.snd c.g v) eZ
  /-- Open coordinate exchange on the entire unbounded category. -/
  openIso : PodOpenLowerShriek Λ (c.baseChange v).i ⋙ PodPullback Λ eZ.hom ≅
    PodPullback Λ eX.hom ⋙
      PodOpenLowerShriek Λ (podRealizedCompactification (c.baseChange v) eX eZ).i
  /-- Original unit--square--counit normalization of the inverse open coordinate map. -/
  openIso_inv : openIso.inv =
    podInverseOpenExchange Λ
      (podChosenCartesianSquare (podCoordinateOpenSquare (c.baseChange v) eX eZ))
  /-- The normalized open exchange for the literal base change. -/
  literalOpenIso : PodOpenLowerShriek Λ c.i ⋙ PodPullback Λ (pullback.fst c.g v) ≅
    PodPullback Λ (pullback.fst f v) ⋙ PodOpenLowerShriek Λ (c.baseChange v).i
  /-- Pins the literal open exchange to the dependency's actual arrow. -/
  literalOpenIso_inv : literalOpenIso.inv = detSfOpenBaseChangeMap Λ f v c
  /-- The same recipe on the realized square. -/
  realizedOpenIso :
    PodOpenLowerShriek Λ c.i ⋙ PodPullback Λ (eZ.hom ≫ pullback.fst c.g v) ≅
      PodPullback Λ (eX.hom ≫ pullback.fst f v) ⋙
        PodOpenLowerShriek Λ (podRealizedCompactification (c.baseChange v) eX eZ).i
  /-- Pins the realized open exchange to its unit--square--counit mate. -/
  realizedOpenIso_inv : realizedOpenIso.inv =
    podInverseOpenExchange Λ
      (podChosenCartesianSquare (podRealizedOpenSquare c v eX eZ))
  /-- The proper factors separately identify by the inverse pullback compositor. -/
  proper_factor (M : PodDerived Λ c.Z) :
    (condensedAmbientExchange Λ
      (podChosenCartesianSquare (podRealizedProperSquare c v eX eZ))).app M =
      (detSfProperBaseChangeMap Λ c.g v).app M ≫
        properIso.hom.app ((PodPullback Λ (pullback.fst c.g v)).obj M) ≫
        (PodPushforward Λ (eZ.hom ≫ pullback.snd c.g v)).map
          ((leftDerivedUpperStarComp Λ eZ.hom (pullback.fst c.g v)).inv.app M)
  /-- The open factors separately identify by the same two pullback compositors. -/
  open_factor (K : PodDerived Λ X) :
    (PodPullback Λ eZ.hom).map (literalOpenIso.hom.app K) ≫
        openIso.hom.app ((PodPullback Λ (pullback.fst f v)).obj K) ≫
        (PodOpenLowerShriek Λ
          (podRealizedCompactification (c.baseChange v) eX eZ).i).map
          ((leftDerivedUpperStarComp Λ eX.hom (pullback.fst f v)).inv.app K) =
      (leftDerivedUpperStarComp Λ eZ.hom (pullback.fst c.g v)).inv.app
          ((PodOpenLowerShriek Λ c.i).obj K) ≫ realizedOpenIso.hom.app K
  /-- The stated equation for B, using the actual two-factor composite on both sides. -/
  compactSupport_transport (K : PodDerived Λ X) :
    (podCompactSupportExchange Λ c
        (podRealizedCompactification (c.baseChange v) eX eZ) v
        (eX.hom ≫ pullback.fst f v) (eZ.hom ≫ pullback.fst c.g v)
        (podChosenCartesianSquare (podRealizedProperSquare c v eX eZ)) realizedOpenIso).app K =
      (detSfCompactSupportBaseChangeComposite Λ f v c literalOpenIso).app K ≫
        (podCompactificationComparison Λ (c.baseChange v) eX eZ properIso openIso).hom.app
          ((PodPullback Λ (pullback.fst f v)).obj K) ≫
        (PodCompactSupport Λ
          (podRealizedCompactification (c.baseChange v) eX eZ)).map
          ((leftDerivedUpperStarComp Λ eX.hom (pullback.fst f v)).inv.app K)

/-- The realized pullback as a boundary compactification; its arrows are the coordinate
formulas, and its quasi-compactness follows from that of f.
Source: coordinate paragraph of clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podRealizedPullbackBoundary {X Y Y' T Z : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c : Compactification.BoundaryCompactification f) (v : Y' ⟶ Y)
    (eX : T ≅ pullback f v) (eZ : Z ≅ pullback c.obj.obj.g v) :
    Compactification.BoundaryCompactification (eX.hom ≫ pullback.snd f v) :=
  podRealizedBoundary (podPullbackBoundary c v) eX eZ

/-- The dependency's normalized direct-image compositor, including the refinement triangle's
canonical equality identification. Its inverse is exactly the proper factor in rho.
Source: refinement formula in clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podRefinementDirectImage {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (h : d ⟶ c) :
    PodPushforward Λ d.obj.obj.g ≅
      PodPushforward Λ h.hom.hom.hom ⋙ PodPushforward Λ c.obj.obj.g :=
  (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ h.hom.hom.hom_g)).symm ≪≫
    refinementDerivedLowerStarComp Λ h.hom.hom.hom c.obj.obj.g

set_option maxHeartbeats 1600000 in
-- The normalized refinement equations across several derived functors need this budget.
/-- The full coordinate-invariance assertion, packaged with the coordinate formulas and
normalizations which uniquely fix its data. In particular the two refinements are fixed
by the projection equation and conjugation equation, and every exchange is fixed by its
mate. No comparison on a restricted category, nor arbitrary choice of an arrow, is used.
Source: clauses (1), (3), and node proof steps 1--9
(blueprint: lem-pod-condensed-compactification-square-transport). -/
structure PodCompactificationSquareTransport {X Y Y' T Zc Zd : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] (v : Y' ⟶ Y)
    (c d : Compactification.BoundaryCompactification f) (h : d ⟶ c)
    (eX : T ≅ pullback f v) (ec : Zc ≅ pullback c.obj.obj.g v)
    (ed : Zd ≅ pullback d.obj.obj.g v) where
  /-- The c comparison and its proper, open and compact-support equations. -/
  cData : PodCompactificationCoordinateData Λ c.obj.obj v eX ec
  /-- The analogous d comparison and equations. -/
  dData : PodCompactificationCoordinateData Λ d.obj.obj v eX ed
  /-- The literal pullback refinement, including boundary preservation. -/
  pullbackRefinement : podPullbackBoundary d v ⟶ podPullbackBoundary c v
  /-- Together with its structural triangle this fixes h' as the literal base change of h. -/
  pullbackRefinement_fst :
    pullbackRefinement.hom.hom.hom ≫ pullback.fst c.obj.obj.g v =
      pullback.fst d.obj.obj.g v ≫ h.hom.hom.hom
  /-- The realized refinement, including boundary preservation. -/
  realizedRefinement : podRealizedPullbackBoundary d v eX ed ⟶
    podRealizedPullbackBoundary c v eX ec
  /-- The stated formula for the realized refinement; it is not asserted equal to h. -/
  realizedRefinement_hom : realizedRefinement.hom.hom.hom =
    ed.hom ≫ pullbackRefinement.hom.hom.hom ≫ ec.inv
  /-- The square whose actual proper mate enters the refinement factor calculation. -/
  refinementSquare : ChosenCartesianSquare ed.hom realizedRefinement.hom.hom.hom
    pullbackRefinement.hom.hom.hom ec.hom
  /-- The isomorphism-square proper mate on the entire unbounded category. -/
  refinementProperIso :
    PodPushforward Λ pullbackRefinement.hom.hom.hom ⋙ PodPullback Λ ec.hom ≅
      PodPullback Λ ed.hom ⋙ PodPushforward Λ realizedRefinement.hom.hom.hom
  /-- Fixes tau to the specified derived adjunction mate. -/
  refinementProperIso_hom :
    refinementProperIso.hom = condensedAmbientExchange Λ refinementSquare
  /-- Separate transport of the actual open-adjunction refinement maps. -/
  open_refinement (K : PodDerived Λ (pullback f v)) :
    (PodPullback Λ ec.hom).map (localizingRefinementMap Λ pullbackRefinement K) ≫
        refinementProperIso.hom.app
          ((PodOpenLowerShriek Λ (d.obj.obj.baseChange v).i).obj K) ≫
        (PodPushforward Λ realizedRefinement.hom.hom.hom).map
          (dData.openIso.hom.app K) =
      cData.openIso.hom.app K ≫ localizingRefinementMap Λ realizedRefinement
        ((PodPullback Λ eX.hom).obj K)
  /-- Separate transport of the specified K-injective-normalized direct-image compositors. -/
  proper_refinement (M : PodDerived Λ (pullback d.obj.obj.g v)) :
    cData.properIso.hom.app ((PodPushforward Λ pullbackRefinement.hom.hom.hom).obj M) ≫
        (PodPushforward Λ (ec.hom ≫ pullback.snd c.obj.obj.g v)).map
          (refinementProperIso.hom.app M) ≫
        (podRefinementDirectImage Λ realizedRefinement).inv.app
          ((PodPullback Λ ed.hom).obj M) =
      (podRefinementDirectImage Λ pullbackRefinement).inv.app M ≫
        dData.properIso.hom.app M
  /-- The claimed equality of the dependency's actual canonical refinement components. -/
  refinement (K : PodDerived Λ (pullback f v)) :
    compactificationRefinementComponent Λ pullbackRefinement K ≫
        (podCompactificationComparison Λ (d.obj.obj.baseChange v) eX ed
          dData.properIso dData.openIso).hom.app K =
      (podCompactificationComparison Λ (c.obj.obj.baseChange v) eX ec
          cData.properIso cData.openIso).hom.app K ≫
        compactificationRefinementComponent Λ realizedRefinement
          ((PodPullback Λ eX.hom).obj K)

/-- Canonical compactification mates and refinement components are invariant under the
specified isomorphic Cartesian realization, on ordinary unbounded derived categories.

Source: latest blueprint, sec-six-functors-basics/sk-thm-sf-comp-composition/
det-sf-comp-composition-base-change.proof.md, clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport).

Proof plan (the nine steps of the node):
1. Base change the compactifications and h. Cancel the scheme isomorphisms in the
coordinate formulas; inverse images of distinguished opens prove boundary preservation.
2. The identity-base proper mates and normalized open coordinate exchanges are isomorphisms
on the entire unbounded category by isomorphism-square exchange. Their composite is chi.
3. Paste the proper square with the coordinate square. Canonical pullback coherence and
vertical mate pasting give proper_factor, with the inverse compositor n.
4. Paste the inverse open mates under the specified exact open adjunctions. Invert the
resulting equation, retaining the original units and counits, to obtain open_factor.
5. Substitute both factor equations in the two-factor recipe for B. Naturality of q
moves it past the open factor and leaves exactly compactSupport_transport, for c and d.
6. Paste the pullback-comparison cube for h' and its conjugate. Mate pasting identifies
the actual open restriction comparisons, including their canonical identity comparisons.
7. Express theta as restriction followed by the inverse open unit. The normalized open
mate unit equation identifies the transported theta maps after cancelling those units.
8. Both transported open refinement arrows have adjunct theta inverse. Injectivity of
the specified adjunction bijection gives open_refinement for the actual refinement arrows.
9. Horizontal mate pasting, canonical direct-image conjugation and its K-injective
normalization give proper_refinement, including the structural triangle identifications.
Combine it with step 8 and naturality to get refinement for the actual rho components.
No constructibility, Frobenius, density, finite-coefficient or absolute separatedness
hypothesis is used. Empty schemes and the zero coefficient ring are included. -/
theorem podCompactificationSquareTransport
    {X Y Y' T Zc Zd : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (v : Y' ⟶ Y)
    (c d : Compactification.BoundaryCompactification f) (h : d ⟶ c)
    (eX : T ≅ pullback f v) (ec : Zc ≅ pullback c.obj.obj.g v)
    (ed : Zd ≅ pullback d.obj.obj.g v) :
    Nonempty (PodCompactificationSquareTransport Λ f v c d h eX ec ed) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
