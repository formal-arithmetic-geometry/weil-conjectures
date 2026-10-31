/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Blowup.Affine.Defs
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Sites.GrothendieckTopos
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections

/-! # The cohomology presentation by admissible modifications

Source: ILO, Travaux de Gabber, XX 4.4, printed pages 373–374.
(blueprint: def-per-admissible-modification-limit-site-data).
-/

@[expose] public section

set_option autoImplicit false

-- Avoid generating unused constructor injectivity lemmas for the large interfaces.
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

/-- The full-support finitely generated centres in ILO XX 4.4, page 373.
(blueprint: def-per-admissible-modification-limit-site-data). -/
def AdmissibleCentre {A : Type u} [CommRing A] (I : Ideal A) :=
  {J : Ideal A // J.FG ∧ PrimeSpectrum.zeroLocus (J : Set A) =
    PrimeSpectrum.zeroLocus (I : Set A)}

/-- The actual category of blowups over the affine base, before taking its skeleton.
Source: ILO XX 4.4, page 373; its opposite is the domination preorder.
(blueprint: def-per-admissible-modification-limit-site-data). -/
abbrev AdmissibleModification {A : Type u} [CommRing A] (I : Ideal A) :=
  InducedCategory (Over (Spec (CommRingCat.of A)))
    (fun J : AdmissibleCentre I ↦ Over.mk (AffineBlowup.toSpec J.val))

/-- The diagram of closed fibres, formed by genuine scheme-theoretic base change.
Source: ILO XX 4.4, page 373.
(blueprint: def-per-admissible-modification-limit-site-data). -/
def admissibleClosedFibres {A : Type u} [CommRing A] (I : Ideal A) :
    AdmissibleModification I ⥤ Scheme.{u} :=
  inducedFunctor _ ⋙ Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⋙
    Over.forget _

/-- A cone of geometric morphisms to the closed-fibre étale topoi. The cocycle is
written on direct images using the canonical pullback-pasting comparison.
Source: ILO XX 4.4, page 373; Stacks 00XA.
(blueprint: def-per-admissible-modification-limit-site-data). -/
structure AdmissibleToposCone {T : Type v} [Category.{w} T]
    {A : Type u} [CommRing A] (I : Ideal A) where
  projection (J : AdmissibleModification I) :
    GeometricMorphism T
      (Sheaf ((admissibleClosedFibres I).obj J).smallEtaleTopology (Type (u + 1)))
  transition {J K : AdmissibleModification I} (f : J ⟶ K) :
    (projection J).direct ⋙
      Etale.lowerStar (Type (u + 1)) ((admissibleClosedFibres I).map f) ≅
      (projection K).direct
  cocycle {J K L : AdmissibleModification I} (f : J ⟶ K) (g : K ⟶ L) (x : T) :
    (Etale.lowerStar (Type (u + 1)) ((admissibleClosedFibres I).map g)).map
        ((transition f).hom.app x) ≫ (transition g).hom.app x =
      (Etale.lowerStarComp (Type (u + 1))
        ((admissibleClosedFibres I).map f) ((admissibleClosedFibres I).map g)
        ((admissibleClosedFibres I).map (f ≫ g))
        ((admissibleClosedFibres I).map_comp f g)).hom.app ((projection J).direct.obj x) ≫
          (transition (f ≫ g)).hom.app x

/-- The full two-dimensional universal property of the limit topos: every cone lifts,
and compatible transformations between two lifts lift uniquely. Test topoi are given
by small-site presentations in the same coefficient universe.
Source: ILO XX 4.4, page 373; Stacks 00XA and 09YL.
(blueprint: def-per-admissible-modification-limit-site-data). -/
def AdmissibleToposCone.IsLimit {A : Type u} [CommRing A] {I : Ideal A}
    {C : Type (u + 1)} [SmallCategory C] {τ : GrothendieckTopology C}
    (P : AdmissibleToposCone (T := Sheaf τ (Type (u + 1))) I) : Prop :=
  (∀ (D : Type (u + 1)) [SmallCategory D] (σ : GrothendieckTopology D)
      (Q : AdmissibleToposCone (T := Sheaf σ (Type (u + 1))) I),
    ∃ (g : GeometricMorphism (Sheaf σ (Type (u + 1))) (Sheaf τ (Type (u + 1))))
      (e : ∀ J, g.direct ⋙ (P.projection J).direct ≅ (Q.projection J).direct),
      ∀ (J K : AdmissibleModification I) (f : J ⟶ K) (x : Sheaf σ (Type (u + 1))),
        (Etale.lowerStar (Type (u + 1)) ((admissibleClosedFibres I).map f)).map
            ((e J).hom.app x) ≫ (Q.transition f).hom.app x =
          (P.transition f).hom.app (g.direct.obj x) ≫ (e K).hom.app x) ∧
  (∀ (D : Type (u + 1)) [SmallCategory D] (σ : GrothendieckTopology D)
      (g h : GeometricMorphism (Sheaf σ (Type (u + 1))) (Sheaf τ (Type (u + 1))))
      (a : ∀ J, g.direct ⋙ (P.projection J).direct ⟶
        h.direct ⋙ (P.projection J).direct),
      (∀ (J K : AdmissibleModification I) (f : J ⟶ K) (x : Sheaf σ (Type (u + 1))),
        (Etale.lowerStar (Type (u + 1)) ((admissibleClosedFibres I).map f)).map
            ((a J).app x) ≫ (P.transition f).hom.app (h.direct.obj x) =
          (P.transition f).hom.app (g.direct.obj x) ≫ (a K).app x) →
      ∃! b : g.direct ⟶ h.direct,
        ∀ J, Functor.whiskerRight b (P.projection J).direct = a J)

/-- A site presentation of the projections from the admissible limit topos. Both
set and abelian inverse images are the usual sheafified Kan extensions along these
same functors; no independent coefficient functor is chosen.
Source: ILO XX 4.4, page 373; Stacks 09YL and 0A35.
(blueprint: def-per-admissible-modification-limit-site-data). -/
structure AdmissibleLimitSite {A : Type u} [CommRing A] (I : Ideal A)
    (C : Type (u + 1)) [SmallCategory C] (τ : GrothendieckTopology C) where
  inclusion (J : AdmissibleModification I) : ((admissibleClosedFibres I).obj J).Etale ⥤ C
  continuous (J : AdmissibleModification I) :
    (inclusion J).IsContinuous ((admissibleClosedFibres I).obj J).smallEtaleTopology τ
  leftExact (J : AdmissibleModification I) : PreservesFiniteLimits
    (Functor.sheafPullbackConstruction.sheafPullback (inclusion J) (Type (u + 1))
      ((admissibleClosedFibres I).obj J).smallEtaleTopology τ)
  comparison {J K : AdmissibleModification I} (f : J ⟶ K) :
    ((admissibleClosedFibres I).map f).Etale ⋙ inclusion J ≅ inclusion K

attribute [instance] AdmissibleLimitSite.continuous

/-- The abelian inverse-image projection, using the same site functor as for sets.
Source: ILO XX 4.4, page 373; Stacks 0A35.
(blueprint: def-per-admissible-modification-limit-site-data). -/
def AdmissibleLimitSite.inverseAb {A : Type u} [CommRing A] {I : Ideal A}
    {C : Type (u + 1)} [SmallCategory C] {τ : GrothendieckTopology C}
    (P : AdmissibleLimitSite I C τ) (J : AdmissibleModification I) :
    Sheaf ((admissibleClosedFibres I).obj J).smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf τ AddCommGrpCat.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback (P.inclusion J) AddCommGrpCat.{u + 1}
    ((admissibleClosedFibres I).obj J).smallEtaleTopology τ

/-- Direct-image transport induced by the site comparison, with its canonical
pullback-pasting normalization. Source: ILO XX 4.4, page 373; Stacks 0A35.
(blueprint: def-per-admissible-modification-limit-site-data). -/
def AdmissibleLimitSite.directComparison {A : Type u} [CommRing A] {I : Ideal A}
    {C : Type (u + 1)} [SmallCategory C] {τ : GrothendieckTopology C}
    (P : AdmissibleLimitSite I C τ) (B : Type (u + 2)) [Category.{u + 1} B]
    {J K : AdmissibleModification I} (f : J ⟶ K) :
    (P.inclusion J).sheafPushforwardContinuous B
        ((admissibleClosedFibres I).obj J).smallEtaleTopology τ ⋙
      Etale.lowerStar B ((admissibleClosedFibres I).map f) ≅
      (P.inclusion K).sheafPushforwardContinuous B
        ((admissibleClosedFibres I).obj K).smallEtaleTopology τ :=
  Functor.sheafPushforwardContinuousComp' (eFG := P.comparison f) B
    ((admissibleClosedFibres I).obj K).smallEtaleTopology
    ((admissibleClosedFibres I).obj J).smallEtaleTopology τ

/-- Canonical transport of abelian inverse images, the mate of the normalized
site direct-image comparison. Source: ILO XX 4.4, page 373; Stacks 0A35.
(blueprint: def-per-admissible-modification-limit-site-data). -/
def AdmissibleLimitSite.inverseComparison {A : Type u} [CommRing A] {I : Ideal A}
    {C : Type (u + 1)} [SmallCategory C] {τ : GrothendieckTopology C}
    (P : AdmissibleLimitSite I C τ) {J K : AdmissibleModification I} (f : J ⟶ K) :
    Etale.upperStar AddCommGrpCat.{u + 1} ((admissibleClosedFibres I).map f) ⋙
      P.inverseAb J ≅ P.inverseAb K :=
  (conjugateIsoEquiv
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (P.inclusion K)
      AddCommGrpCat.{u + 1} ((admissibleClosedFibres I).obj K).smallEtaleTopology τ)
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      ((admissibleClosedFibres I).map f)).comp
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (P.inclusion J)
        AddCommGrpCat.{u + 1} ((admissibleClosedFibres I).obj J).smallEtaleTopology τ))).symm
      (P.directComparison AddCommGrpCat.{u + 1} f).symm

/-- The coherence condition on the site presentation, tested after the canonical
pushforward construction. Source: ILO XX 4.4, page 373; Stacks 09YL.
(blueprint: def-per-admissible-modification-limit-site-data). -/
def AdmissibleLimitSite.IsCoherent {A : Type u} [CommRing A] {I : Ideal A}
    {C : Type (u + 1)} [SmallCategory C] {τ : GrothendieckTopology C}
    (P : AdmissibleLimitSite I C τ) : Prop :=
  ∀ (B : Type (u + 2)) [Category.{u + 1} B]
    (J K L : AdmissibleModification I) (f : J ⟶ K) (g : K ⟶ L) (x : Sheaf τ B),
    (Etale.lowerStar B ((admissibleClosedFibres I).map g)).map
        ((P.directComparison B f).hom.app x) ≫ (P.directComparison B g).hom.app x =
      (Etale.lowerStarComp B ((admissibleClosedFibres I).map f)
        ((admissibleClosedFibres I).map g) ((admissibleClosedFibres I).map (f ≫ g))
        ((admissibleClosedFibres I).map_comp f g)).hom.app
          (((P.inclusion J).sheafPushforwardContinuous B
            ((admissibleClosedFibres I).obj J).smallEtaleTopology τ).obj x) ≫
              (P.directComparison B (f ≫ g)).hom.app x

/-- The geometric cone attached to a coherent site presentation.
Source: ILO XX 4.4, page 373; Stacks 00XA, 09YL.
(blueprint: def-per-admissible-modification-limit-site-data). -/
def AdmissibleLimitSite.cone {A : Type u} [CommRing A] {I : Ideal A}
    {C : Type (u + 1)} [SmallCategory C] {τ : GrothendieckTopology C}
    (P : AdmissibleLimitSite I C τ) (hP : P.IsCoherent) :
    AdmissibleToposCone (T := Sheaf τ (Type (u + 1))) I where
  projection J :=
    { inverse := Functor.sheafPullbackConstruction.sheafPullback (P.inclusion J)
        (Type (u + 1)) ((admissibleClosedFibres I).obj J).smallEtaleTopology τ
      direct := (P.inclusion J).sheafPushforwardContinuous (Type (u + 1))
        ((admissibleClosedFibres I).obj J).smallEtaleTopology τ
      adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (P.inclusion J)
        (Type (u + 1)) ((admissibleClosedFibres I).obj J).smallEtaleTopology τ
      leftExact := P.leftExact J }
  transition f := P.directComparison (Type (u + 1)) f
  cocycle f g x := hP (Type (u + 1)) _ _ _ f g x

/-- Points whose projections are geometric points of every closed fibre. Their
compatibility is through the fixed site comparisons, so includes all cocycle data.
Source: ILO XX 4.4, page 373; Stacks 00YQ.
(blueprint: def-per-admissible-modification-limit-site-data). -/
def AdmissibleLimitSite.IsGeometricPoint {A : Type u} [CommRing A] {I : Ideal A}
    {C : Type (u + 1)} [SmallCategory C] {τ : GrothendieckTopology C}
    (P : AdmissibleLimitSite I C τ) (Φ : τ.Point.{u + 1}) : Prop :=
  ∀ J : AdmissibleModification I,
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω)
      (z : Spec (CommRingCat.of Ω) ⟶ (admissibleClosedFibres I).obj J),
      Nonempty (P.inclusion J ⋙ Φ.fiber ≅
        (Scheme.pointSmallEtale z).fiber ⋙ uliftFunctor.{u + 1, u})

end

end AlgebraicGeometry
