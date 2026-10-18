/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Irreducible
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Orgogozo's induction data

Source: Orgogozo, Modifications et cycles proches sur une base générale, §§1, 3.1, 3.3
(blueprint: def-trf-orgogozo-induction-data).

The geometric data here retain the proper tower underlying the projective plurinodal
morphisms in the source. Each factor also records a finite closed subscheme with smooth
complement. The universal truncated condition tests two successive arbitrary base changes.

## Main definitions

* `UniversalTruncatedComparison` is the universal property `P_r(f,K)`.
* `IsModification` and `IsAlteration` specify the modification and alteration geometry.
* `SemistableTower` and `AlmostPlurinodalDatum` retain the chosen geometric tower data.
* `IsExcellentScheme` tests excellence on every affine coordinate ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.Orgogozo

/-- Vanishing through degree `r` for any cone of a derived morphism. Distinguished triangles
make this independent of a choice of cone. Source: Orgogozo §3.1
(blueprint: def-trf-orgogozo-induction-data). -/
def ConeVanishesThrough (S : CategoryTheory.AdicSites.Site.{w})
    (A : Type w) [CommRing A] {L M : S.derived A} (β : L ⟶ M) (r : ℤ) : Prop :=
  ∀ (C : S.derived A) (g : M ⟶ C) (h : C ⟶ L⟦(1 : ℤ)⟧),
    Triangle.mk β g h ∈ distTriang (S.derived A) →
      ∀ i : ℤ, i ≤ r → IsZero ((DerivedCategory.homologyFunctor (S.modules A) i).obj C)

/-- `P_r(f,K)`: ordinary comparison cones vanish in degrees at most `r` after an arbitrary
preliminary base change and a further arbitrary base change. The coefficient ring is finite
and `K` is a bounded derived object. Source: Orgogozo §§1, 3.1
(blueprint: def-trf-orgogozo-induction-data). -/
def UniversalTruncatedComparison {X S : Scheme.{u}} (f : X ⟶ S)
    (Λ : Type v) [CommRing Λ] [Finite Λ]
    (K : {L : EtaleDerived.{u, v} X Λ //
      IsBounded.{max (u + 1) v} (etaleDatum.{u, v} X) (Coeff.{u, v} Λ) L}) (r : ℤ) : Prop :=
  ∀ (T : Scheme.{u}) (a : T ⟶ S) (T' : Scheme.{u}) (b : T' ⟶ T),
    ConeVanishesThrough
      (vanishingDatum.{u, v} (pullback.snd (pullback.snd f a) b)) (Coeff.{u, v} Λ)
      (baseChange.{u, v} (pullback.snd f a) (pullback.snd (pullback.snd f a) b)
        (pullback.fst (pullback.snd f a) b) b
        (pullback.condition (f := pullback.snd f a) (g := b)) Λ
        (((etaleModules.{u, v} (pullback.fst f a)).pull (Coeff.{u, v} Λ)).obj K.val)) r

/-- A modification over a reduced Noetherian base, with a dense isomorphism locus whose
inverse image is dense. Source: Orgogozo §1
(blueprint: def-trf-orgogozo-induction-data). -/
def IsModification {S' S : Scheme.{u}} [IsReduced S] [IsLocallyNoetherian S]
    [CompactSpace S] (p : S' ⟶ S) : Prop :=
  IsProper p ∧ ∃ U : S.Opens, Dense (U : Set S) ∧
    IsIso (pullback.snd p U.ι) ∧ Dense (p ⁻¹' (U : Set S))

/-- A proper surjective morphism finite over a dense open, each source component dominating
a target component. Source: Orgogozo §1
(blueprint: def-trf-orgogozo-induction-data). -/
def IsAlteration {S' S : Scheme.{u}} (p : S' ⟶ S) : Prop :=
  IsProper p ∧ Surjective p ∧
    (∃ U : S.Opens, Dense (U : Set S) ∧ IsFinite (pullback.snd p U.ι)) ∧
    ∀ Z : Set S', Z ∈ irreducibleComponents S' →
      ∃ W : Set S, W ∈ irreducibleComponents S ∧ closure (p '' Z) = W

/-- The nodal completed local ring `Ω[[u,v]]/(uv)`. Source: Orgogozo §3.3, ordinary quadratic
singularities of geometric fibres (blueprint: def-trf-orgogozo-induction-data). -/
abbrev nodeRing (Ω : Type u) [Field Ω] :=
  MvPowerSeries (Fin 2) Ω ⧸
    (Ideal.span {MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)} :
      Ideal (MvPowerSeries (Fin 2) Ω))

/-- The canonical scalar map to a fibre local ring, using global sections and the germ.
Source: Orgogozo §3.3 (blueprint: def-trf-orgogozo-induction-data). -/
def localScalar {Ω : Type u} [Field Ω] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of Ω)) (x : C) : Ω →+* C.presheaf.stalk x :=
  (C.presheaf.germ ⊤ x (Set.mem_univ x)).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (.of Ω)).inv.hom)

/-- A geometric ordinary double point: its maximal-ideal completion is the nodal ring,
compatibly with the specified scalar field. Source: Orgogozo §3.3
(blueprint: def-trf-orgogozo-induction-data). -/
def IsOrdinaryDoublePoint {Ω : Type u} [Field Ω] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of Ω)) (x : C) : Prop :=
  ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
      (C.presheaf.stalk x) ≃+* nodeRing Ω,
    ∀ a : Ω, e (AdicCompletion.of (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
      (C.presheaf.stalk x) (localScalar p x a)) =
        Ideal.Quotient.mk _ (MvPowerSeries.C a)

/-- A connected reduced geometric curve of pure dimension one whose points are either
smooth or ordinary double points. Source: Orgogozo §3.3
(blueprint: def-trf-orgogozo-induction-data). -/
def IsSemistableGeometricCurve {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {C : Scheme.{u}} (p : C ⟶ Spec (.of Ω)) : Prop :=
  ConnectedSpace C ∧ IsReduced C ∧ C.IsPureDimension 1 ∧
    ∀ x : C, (∃ U : C.Opens, x ∈ U ∧ Smooth (U.ι ≫ p)) ∨ IsOrdinaryDoublePoint p x

/-- The chosen algebraic-closure geometric point over `y`. Source: Orgogozo §3.3 and the
geometric-fibre convention (blueprint: def-trf-orgogozo-induction-data). -/
def geometricPoint (S : Scheme.{u}) (y : S) :
    Spec (.of (AlgebraicClosure (S.residueField y))) ⟶ S :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (S.residueField y) (AlgebraicClosure (S.residueField y)))) ≫
      S.fromSpecResidueField y

/-- A proper flat semistable curve factor, with the chosen finite closed subscheme and
smooth complement required in the induction datum. Source: Orgogozo §3.3 and §9.3
(blueprint: def-trf-orgogozo-induction-data). -/
structure SemistableFactor {X S : Scheme.{u}} (f : X ⟶ S) where
  proper : IsProper f
  flat : Flat f
  fibres : ∀ y : S, IsSemistableGeometricCurve (pullback.snd f (geometricPoint S y))
  closed : Scheme.{u}
  inclusion : closed ⟶ X
  [isClosedImmersion : IsClosedImmersion inclusion]
  finite : IsFinite (inclusion ≫ f)
  smoothComplement : Smooth (Scheme.Opens.ι (X := X)
    ⟨(Set.range inclusion)ᶜ, inclusion.isClosedEmbedding.isClosed_range.isOpen_compl⟩ ≫ f)

/-- A finite semistable tower, including the identity as the length-zero tower.
Each successor carries the chosen finite closed subscheme in `SemistableFactor`.
Source: Orgogozo §3.3 (blueprint: def-trf-orgogozo-induction-data). -/
inductive SemistableTower (S : Scheme.{u}) : (X : Scheme.{u}) → (X ⟶ S) → Type (u + 1)
  | identity : SemistableTower S S (𝟙 S)
  | step {Y X : Scheme.{u}} {g : Y ⟶ S} (tower : SemistableTower S Y g)
      (f : X ⟶ Y) (factor : SemistableFactor f) : SemistableTower S X (f ≫ g)

/-- The data for a finite disjoint union of semistable towers and one proper morphism with
nowhere dense image. Source: Orgogozo §3.3
(blueprint: def-trf-orgogozo-induction-data). -/
structure AlmostPlurinodalDatum (S : Scheme.{u}) where
  count : ℕ
  pieces : Fin count → Scheme.{u}
  maps : ∀ i : Fin count, pieces i ⟶ S
  towers : ∀ i : Fin count, SemistableTower S (pieces i) (maps i)
  vertical : Scheme.{u}
  verticalMap : vertical ⟶ S
  verticalProper : IsProper verticalMap
  nowhereDense : interior (closure (Set.range verticalMap)) = ∅

/-- The actual disjoint-union source of the almost plurinodal datum. Source: Orgogozo §3.3
(blueprint: def-trf-orgogozo-induction-data). -/
def AlmostPlurinodalDatum.source {S : Scheme.{u}} (D : AlmostPlurinodalDatum S) : Scheme.{u} :=
  (∐ D.pieces) ⨿ D.vertical

/-- The morphism from that disjoint union, induced by the recorded component morphisms.
Source: Orgogozo §3.3 (blueprint: def-trf-orgogozo-induction-data). -/
def AlmostPlurinodalDatum.morphism {S : Scheme.{u}} (D : AlmostPlurinodalDatum S) :
    D.source ⟶ S :=
  coprod.desc (Sigma.desc D.maps) D.verticalMap

/-- Excellence of every affine coordinate ring of a scheme. Source: Orgogozo §§2.1, 3.3;
Stacks 07QT (blueprint: def-trf-orgogozo-induction-data). -/
def IsExcellentScheme (S : Scheme.{u}) : Prop :=
  ∀ U : S.affineOpens, IsExcellent Γ(S, U)

end AlgebraicGeometry.Orgogozo
