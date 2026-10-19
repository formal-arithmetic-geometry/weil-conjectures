/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
public import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Sheaf.AlgebraicGeometry.EtaleSectionProperSupport
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
public import WeilConjectures.Algebra.Category.ModuleCat.RingScalarExtension
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk
import Sheaf.AlgebraicGeometry.GeometricStalkColimits
import Mathlib.Algebra.Homology.Additive
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteMultiplePoints
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.SeparatedLqfBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionsGeometricGermExt
import Sheaf.AlgebraicGeometry.ZeroDimensionalSectionsStalks
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.QuasiFiniteIffFiniteFibres
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
/-!
# Finite-parts generators and relations for quasi-finite proper support

Source: SGA 4 XVII 6.2.1, (6.2.1.1–2), Proposition 6.2.2, pp. 420–422, and the
universal property in the proof of 6.2.3, p. 425
(blueprint: lem-pur-quasifinite-finite-parts-presentation).

Finite products of modules represent the finite direct sums. The maps below are recorded
on sections over the finite-presentation etale basis, including every restriction. Thus
they specify maps of the restricted sheaves, rather than just maps of their global sections.
The proper-support sheaf is specified by its inclusion into ordinary direct image, as in
`properSupportSheafComposition`; no choice of an unidentified support functor is made.

## Main definitions

- `FinitePartsDecomposition`, `FinitePartsRefinement`, `FinitePartsRestriction`: finite
  pointed clopen partitions and their refinement and localization data.
- `IsFinitePartsGenerator`, `FinitePartsCompatible`, `FinitePartsUniversal`: the canonical
  unit-and-zero generators, their relations, and the local colimit universal property.
- `FinitePartsStalkIso`, `FinitePartsBaseChangeCompatible`,
  `FinitePartsCoefficientCompatible`: geometric stalks and the two functorialities.

## Main statements

- `quasiFinite_finiteParts_presentation`: these generators and relations present the
  proper-support inverse-image sheaf, with special geometric-stalk decompositions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- A finite pointed clopen decomposition, with no finiteness requirement on its remainder.
Source: SGA 4 XVII 6.2.1 (blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
structure FinitePartsDecomposition {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale) where
  Index : Type u
  finite : Finite Index
  zero : Index
  piece : Index → ((f.Etale.obj U).left).Opens
  closed : ∀ i, IsClosed (piece i : Set (f.Etale.obj U).left)
  disjoint : Pairwise (fun i j ↦ Disjoint (piece i) (piece j))
  cover : iSup piece = ⊤
  finite_piece : ∀ i, i ≠ zero → IsFinite ((piece i).ι ≫ pullback.fst U.hom f)

open Classical in
/-- The zero/diagonal coordinate, including the remainder's prescribed zero.
Source: SGA 4 XVII (6.2.1.2)
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
noncomputable def finitePartsCoordinate
    {B : Type (u + 1)} [CommRing B] {X S : Scheme.{u}} {f : X ⟶ S} {U : S.Etale}
    (D : FinitePartsDecomposition f U) (M : ModuleCat.{u + 1} B) (i : D.Index) :
    ((j : {j : D.Index // j ≠ D.zero}) → M) →ₗ[B] M :=
  if h : i ≠ D.zero then LinearMap.proj ⟨i, h⟩ else 0

/-- The pointed refinement relation: each old piece is the union of its new labels.
Source: SGA 4 XVII 6.2.1 (blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
structure FinitePartsRefinement {X S : Scheme.{u}} {f : X ⟶ S} {U : S.Etale}
    (D D' : FinitePartsDecomposition f U) where
  label : D'.Index → D.Index
  pointed : label D'.zero = D.zero
  pieces : ∀ i, D.piece i = ⨆ (j : D'.Index) (_ : label j = i), D'.piece j

/-- Restriction of a decomposition, allowing an arbitrary relabelling of its finite
pointed index. Source: SGA 4 XVII 6.2.1, localization after (6.2.1.2)
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
structure FinitePartsRestriction {X S : Scheme.{u}} {f : X ⟶ S} {U T : S.Etale}
    (D : FinitePartsDecomposition f U) (D' : FinitePartsDecomposition f T) (q : T ⟶ U) where
  label : D'.Index ≃ D.Index
  pointed : label D'.zero = D.zero
  pieces : ∀ j, D'.piece j = (f.Etale.map q).left ⁻¹ᵁ D.piece (label j)

/-- Restrict sections and apply the zero/diagonal matrix of a pointed map.
Source: SGA 4 XVII (6.2.1.2)
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
noncomputable def finitePartsTransition
    {B : Type (u + 1)} [CommRing B] {X S : Scheme.{u}} {f : X ⟶ S}
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B)) {U T : S.Etale}
    (D : FinitePartsDecomposition f U) (D' : FinitePartsDecomposition f T)
    (q : T ⟶ U) (σ : D'.Index → D.Index) :
    ((j : {j : D.Index // j ≠ D.zero}) → F.obj.obj (op U)) →ₗ[B]
      ((j : {j : D'.Index // j ≠ D'.zero}) → F.obj.obj (op T)) :=
  LinearMap.pi fun j ↦
    (F.obj.map q.op).hom.comp (finitePartsCoordinate D (F.obj.obj (op U)) (σ j.1))

/-- The etale object given by a clopen piece of a pulled-back etale object.
Source: SGA 4 XVII (6.2.1.1)
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
noncomputable def finitePartsPieceObject {X S : Scheme.{u}} {f : X ⟶ S} {U : S.Etale}
    (D : FinitePartsDecomposition f U) (i : D.Index) : X.Etale :=
  Scheme.Etale.mk ((D.piece i).ι ≫ (f.Etale.obj U).hom)

/-- Inclusion of the piece into the pulled-back etale object.
Source: SGA 4 XVII (6.2.1.1)
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
noncomputable def finitePartsPieceInclusion {X S : Scheme.{u}} {f : X ⟶ S} {U : S.Etale}
    (D : FinitePartsDecomposition f U) (i : D.Index) :
    finitePartsPieceObject D i ⟶ f.Etale.obj U :=
  MorphismProperty.Over.homMk (D.piece i).ι rfl

/-- Sectionwise form of the maps on all finite-presentation etale objects. A family
with restriction compatibility below is exactly a family of local sheaf morphisms.
Source: SGA 4 XVII (6.2.1.1)
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
def FinitePartsMaps {B : Type (u + 1)} [CommRing B] {X S : Scheme.{u}} (f : X ⟶ S)
    (F H : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
  ∀ (U : S.Etale), QuasiCompact U.hom → QuasiSeparated U.hom →
    (D : FinitePartsDecomposition f U) →
      ((j : {j : D.Index // j ≠ D.zero}) → F.obj.obj (op U)) →ₗ[B] H.obj.obj (op U)

/-- All etale restrictions and all pointed refinement relations, with the prescribed
zero entries for pieces split off from the remainder.
Source: SGA 4 XVII (6.2.1.2) and Proposition 6.2.2
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
def FinitePartsCompatible {B : Type (u + 1)} [CommRing B] {X S : Scheme.{u}} {f : X ⟶ S}
    {F H : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (g : FinitePartsMaps f F H) : Prop :=
  (∀ (U T : S.Etale) (hU : QuasiCompact U.hom) (kU : QuasiSeparated U.hom)
    (hT : QuasiCompact T.hom) (kT : QuasiSeparated T.hom)
    (D : FinitePartsDecomposition f U) (D' : FinitePartsDecomposition f T)
    (q : T ⟶ U) (r : FinitePartsRestriction D D' q),
    (H.obj.map q.op).hom.comp (g U hU kU D) =
      (g T hT kT D').comp (finitePartsTransition F D D' q r.label)) ∧
  (∀ (U : S.Etale) (hU : QuasiCompact U.hom) (kU : QuasiSeparated U.hom)
    (D D' : FinitePartsDecomposition f U) (r : FinitePartsRefinement D D'),
    g U hU kU D =
      (g U hU kU D').comp (finitePartsTransition F D D' (𝟙 U) r.label))

/-- The generator is the adjunction unit on each finite piece and zero on the remainder,
characterized inside ordinary direct image. This fixes the map, not just its isomorphism
class. Source: SGA 4 XVII (6.2.1.1)
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
def IsFinitePartsGenerator {B : Type (u + 1)} [CommRing B] {X S : Scheme.{u}} (f : X ⟶ S)
    (F H : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B))
    (ι : H ⟶ (lowerStar (ModuleCat.{u + 1} B) f).obj
      ((upperStar (ModuleCat.{u + 1} B) f).obj F))
    (η : FinitePartsMaps f F H) : Prop :=
  ∀ (U : S.Etale) (hU : QuasiCompact U.hom) (kU : QuasiSeparated U.hom)
    (D : FinitePartsDecomposition f U) (i : D.Index)
    (a : (j : {j : D.Index // j ≠ D.zero}) → F.obj.obj (op U)),
    ((upperStar (ModuleCat.{u + 1} B) f).obj F).obj.map
        (finitePartsPieceInclusion D i).op (ι.hom.app (op U) (η U hU kU D a)) =
      ((upperStar (ModuleCat.{u + 1} B) f).obj F).obj.map
        (finitePartsPieceInclusion D i).op
        (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).unit.app F).hom.app
          (op U) (finitePartsCoordinate D (F.obj.obj (op U)) i a))

/-- A special decomposition at a specified lift of a geometric point: the remainder has
empty geometric fibre and every other piece has exactly one geometric point.
Source: SGA 4 XVII Proposition 6.2.2
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
def FinitePartsSpecial {X S : Scheme.{u}} {f : X ⟶ S} {U : S.Etale}
    (D : FinitePartsDecomposition f U) {Ω : Type u} [Field Ω]
    (t : Spec (.of Ω) ⟶ U.left) : Prop :=
  IsEmpty {x : Spec (.of Ω) ⟶ (D.piece D.zero).toScheme //
      x ≫ (D.piece D.zero).ι ≫ pullback.fst U.hom f = t} ∧
  ∀ i, i ≠ D.zero → ∃! x : Spec (.of Ω) ⟶ (D.piece i).toScheme,
      x ≫ (D.piece i).ι ≫ pullback.fst U.hom f = t

/-- The universal property is stated as unique descent of each compatible family. This
is the bijection obtained by composing with all the generators, or equivalently the
etale-local colimit universal property.
Source: SGA 4 XVII Proposition 6.2.2 and the proof of 6.2.3, p. 425
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
def FinitePartsUniversal {B : Type (u + 1)} [CommRing B] {X S : Scheme.{u}} {f : X ⟶ S}
    {F H : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (η : FinitePartsMaps f F H) : Prop :=
  ∀ (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B)) (g : FinitePartsMaps f F G),
    FinitePartsCompatible g → ∃! k : H ⟶ G,
      ∀ (U : S.Etale) (hU : QuasiCompact U.hom) (kU : QuasiSeparated U.hom)
        (D : FinitePartsDecomposition f U),
        (k.hom.app (op U)).hom.comp (η U hU kU D) = g U hU kU D

/-- The special generator induces the indicated isomorphism of geometric stalks. The
formula on all representatives fixes the isomorphism as the stalk of the generator.
Source: SGA 4 XVII Proposition 6.2.2, proof pp. 421–422
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
def FinitePartsStalkIso {B : Type (u + 1)} [CommRing B] {X S : Scheme.{u}} {f : X ⟶ S}
    {F H : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (η : FinitePartsMaps f F H) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (U : S.Etale) (D : FinitePartsDecomposition f U) (t : Spec (.of Ω) ⟶ U.left),
    t ≫ U.hom = s → FinitePartsSpecial D t →
    ∃ e : ModuleCat.of B ((j : {j : D.Index // j ≠ D.zero}) →
          ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} B)).obj F) ≅
        (Scheme.pointSmallEtale s).sheafFiber.obj H,
      ∀ (T : S.Etale) (hT : QuasiCompact T.hom) (kT : QuasiSeparated T.hom)
        (D' : FinitePartsDecomposition f T) (q : T ⟶ U)
        (r : FinitePartsRestriction D D' q)
        (t' : (Scheme.pointSmallEtale s).fiber.obj T),
        t'.left ≫ q.left = t →
        ∀ a : (j : {j : D'.Index // j ≠ D'.zero}) → F.obj.obj (op T),
          e.hom (fun j ↦ (Scheme.pointSmallEtale s).toPresheafFiber T t' F.obj
            (finitePartsCoordinate D' (F.obj.obj (op T)) (r.label.symm j.1) a)) =
              (Scheme.pointSmallEtale s).toPresheafFiber T t' H.obj (η T hT kT D' a)

/-- The actual morphism between the pulled-back ambient schemes in a base change.
Source: SGA 4 XVII 6.2.1, localization; 6.1.4(iii)
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
noncomputable def finitePartsBaseChangeMap {X S S' : Scheme.{u}} (f : X ⟶ S)
    (b : S' ⟶ S) (U : S.Etale) :
    ((pullback.snd f b).Etale.obj (b.Etale.obj U)).left ⟶ (f.Etale.obj U).left :=
  pullback.map (pullback.snd U.hom b) (pullback.snd f b) U.hom f
    (pullback.fst U.hom b) (pullback.fst f b) b
    (pullback.condition (f := U.hom) (g := b)).symm
    (pullback.condition (f := f) (g := b)).symm

/-- A pulled-back decomposition, up to relabelling, consists of the inverse images of
all the original clopen pieces, including the remainder.
Source: SGA 4 XVII 6.2.1 (blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
structure FinitePartsBaseChange {X S S' : Scheme.{u}} {f : X ⟶ S} (b : S' ⟶ S)
    {U : S.Etale} (D : FinitePartsDecomposition f U)
    (D' : FinitePartsDecomposition (pullback.snd f b) (b.Etale.obj U)) where
  label : D'.Index ≃ D.Index
  pointed : label D'.zero = D.zero
  pieces : ∀ j, D'.piece j = finitePartsBaseChangeMap f b U ⁻¹ᵁ D.piece (label j)

/-- Pull a tuple of sections back using the actual inverse-image unit.
Source: SGA 4 XVII 6.2.1 and 6.1.4(iii)
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
noncomputable def finitePartsBaseChangeTuple
    {B : Type (u + 1)} [CommRing B] {X S S' : Scheme.{u}} {f : X ⟶ S}
    (b : S' ⟶ S) (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B))
    {U : S.Etale} (D : FinitePartsDecomposition f U)
    (D' : FinitePartsDecomposition (pullback.snd f b) (b.Etale.obj U))
    (σ : D'.Index → D.Index) :
    ((j : {j : D.Index // j ≠ D.zero}) → F.obj.obj (op U)) →ₗ[B]
      ((j : {j : D'.Index // j ≠ D'.zero}) →
        ((upperStar (ModuleCat.{u + 1} B) b).obj F).obj.obj (op (b.Etale.obj U))) :=
  LinearMap.pi fun j ↦
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) b).unit.app F).hom.app
      (op U)).hom.comp (finitePartsCoordinate D (F.obj.obj (op U)) (σ j.1))

/-- The support inclusion's membership characterization, using the recorded proper-support
predicate on actual sections. This packages the defining property supplied by
`properSupportSheafComposition` and does not define a new support functor.
Source: Stacks 0F4X, SGA 4 XVII 6.1
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
def FinitePartsSupportCondition {B : Type (u + 1)} [CommRing B] {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f]
    (F H : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B))
    (ι : H ⟶ (lowerStar (ModuleCat.{u + 1} B) f).obj
      ((upperStar (ModuleCat.{u + 1} B) f).obj F)) : Prop :=
  ∀ (U : S.Etale)
    (s : ((upperStar (ModuleCat.{u + 1} B) f).obj F).obj.obj (op (f.Etale.obj U))),
    (∃ t, ι.hom.app (op U) t = s) ↔
      SectionHasProperSupport B ((upperStar (ModuleCat.{u + 1} B) f).obj F)
        (f.Etale.obj U) (pullback.fst U.hom f) s

/-- Generators commute with arbitrary base change under the support comparison. The
comparison is normalized by its composite into ordinary direct image; neither it nor
the pulled-back generator is an arbitrary map. No Noetherian or flatness hypothesis is
imposed on the new base.
Source: SGA 4 XVII 6.1.4(iii), 6.2.1–2
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
def FinitePartsBaseChangeCompatible
    {B : Type (u + 1)} [CommRing B] {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    {F H : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (ι : H ⟶ (lowerStar (ModuleCat.{u + 1} B) f).obj
      ((upperStar (ModuleCat.{u + 1} B) f).obj F))
    (η : FinitePartsMaps f F H) : Prop :=
  ∀ (S' : Scheme.{u}) (b : S' ⟶ S)
    (H' : Sheaf S'.smallEtaleTopology (ModuleCat.{u + 1} B))
    (ι' : H' ⟶ (lowerStar (ModuleCat.{u + 1} B) (pullback.snd f b)).obj
      ((upperStar (ModuleCat.{u + 1} B) (pullback.snd f b)).obj
        ((upperStar (ModuleCat.{u + 1} B) b).obj F))) [Mono ι'],
    FinitePartsSupportCondition (pullback.snd f b)
      ((upperStar (ModuleCat.{u + 1} B) b).obj F) H' ι' →
    ∃ (e : (upperStar (ModuleCat.{u + 1} B) b).obj H ≅ H')
      (η' : FinitePartsMaps (pullback.snd f b)
        ((upperStar (ModuleCat.{u + 1} B) b).obj F) H'),
      IsFinitePartsGenerator (pullback.snd f b)
        ((upperStar (ModuleCat.{u + 1} B) b).obj F) H' ι' η' ∧
      e.hom ≫ ι' = (upperStar (ModuleCat.{u + 1} B) b).map ι ≫
        (baseChangeMap (ModuleCat.{u + 1} B) (IsPullback.of_hasPullback f b).toCommSq).app
          ((upperStar (ModuleCat.{u + 1} B) f).obj F) ≫
        (lowerStar (ModuleCat.{u + 1} B) (pullback.snd f b)).map
          ((squareUpperStarIso (ModuleCat.{u + 1} B)
            (IsPullback.of_hasPullback f b).toCommSq).inv.app F) ∧
      ∀ (U : S.Etale) (hU : QuasiCompact U.hom) (kU : QuasiSeparated U.hom)
        (hU' : QuasiCompact (b.Etale.obj U).hom)
        (kU' : QuasiSeparated (b.Etale.obj U).hom) (D : FinitePartsDecomposition f U),
        (∃ D' : FinitePartsDecomposition (pullback.snd f b) (b.Etale.obj U),
          Nonempty (FinitePartsBaseChange b D D')) ∧
        ∀ (D' : FinitePartsDecomposition (pullback.snd f b) (b.Etale.obj U))
          (r : FinitePartsBaseChange b D D')
          (a : (j : {j : D.Index // j ≠ D.zero}) → F.obj.obj (op U)),
          e.hom.hom.app (op (b.Etale.obj U))
            (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) b).unit.app H).hom.app
              (op U) (η U hU kU D a)) =
          η' (b.Etale.obj U) hU' kU' D' (finitePartsBaseChangeTuple b F D D' r.label a)

/-- The ordinary direct-image map induced by a semilinear coefficient map, using the
recorded inverse-image/restriction-of-scalars comparison.
Source: SGA 4 XVII 6.2.1, coefficient functoriality of the unit
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
noncomputable def finitePartsCoefficientDirectImage
    {B B' : Type (u + 1)} [CommRing B] [CommRing B'] (φ : B →+* B')
    {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B))
    (F' : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B'))
    (α : F ⟶ (Sheaf.restrictScalars S.smallEtaleTopology φ).obj F') :
    (lowerStar (ModuleCat.{u + 1} B) f).obj
        ((upperStar (ModuleCat.{u + 1} B) f).obj F) ⟶
      (Sheaf.restrictScalars S.smallEtaleTopology φ).obj
        ((lowerStar (ModuleCat.{u + 1} B') f).obj
          ((upperStar (ModuleCat.{u + 1} B') f).obj F')) :=
  (lowerStar (ModuleCat.{u + 1} B) f).map
    ((upperStar (ModuleCat.{u + 1} B) f).map α ≫
      (upperStarRestrictScalarsIsoSheaf φ f).hom.app F') ≫
    (lowerStarRestrictScalarsIso φ f).inv.app
      ((upperStar (ModuleCat.{u + 1} B') f).obj F')

/-- The coefficient comparison is specified inside direct image, and it sends each
unit-and-zero generator to the corresponding generator over the new coefficient ring.
This includes ordinary linear naturality by taking the identity ring homomorphism.
Source: SGA 4 XVII 6.2.1–2 and the tensor functoriality of 6.2.3
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
def FinitePartsCoefficientMapCondition
    {B B' : Type (u + 1)} [CommRing B] [CommRing B'] (φ : B →+* B')
    {X S : Scheme.{u}} (f : X ⟶ S)
    {F H : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B)}
    {F' H' : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B')}
    (ι : H ⟶ (lowerStar (ModuleCat.{u + 1} B) f).obj
      ((upperStar (ModuleCat.{u + 1} B) f).obj F))
    (ι' : H' ⟶ (lowerStar (ModuleCat.{u + 1} B') f).obj
      ((upperStar (ModuleCat.{u + 1} B') f).obj F'))
    (η : FinitePartsMaps f F H) (η' : FinitePartsMaps f F' H')
    (α : F ⟶ (Sheaf.restrictScalars S.smallEtaleTopology φ).obj F')
    (γ : H ⟶ (Sheaf.restrictScalars S.smallEtaleTopology φ).obj H') : Prop :=
  γ ≫ (Sheaf.restrictScalars S.smallEtaleTopology φ).map ι' =
      ι ≫ finitePartsCoefficientDirectImage φ f F F' α ∧
  ∀ (U : S.Etale) (hU : QuasiCompact U.hom) (kU : QuasiSeparated U.hom)
    (D : FinitePartsDecomposition f U)
    (a : (j : {j : D.Index // j ≠ D.zero}) → F.obj.obj (op U)),
    γ.hom.app (op U) (η U hU kU D a) =
      η' U hU kU D (fun j ↦ α.hom.app (op U) (a j))

/-- Generators commute with all coefficient homomorphisms and semilinear sheaf maps.
The induced ordinary scalar-extension comparison is an isomorphism, including nonflat
coefficient changes. Scalar extension is specified by its sheaf adjunction; it is the
sheafification of sectionwise balanced tensor product.
Source: SGA 4 XVII 6.2.1–2, Stacks 007K, 008B, 03EL, 04FM
(blueprint: lem-pur-quasifinite-finite-parts-presentation). -/
def FinitePartsCoefficientCompatible
    {B : Type (u + 1)} [CommRing B] {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {F H : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (ι : H ⟶ (lowerStar (ModuleCat.{u + 1} B) f).obj
      ((upperStar (ModuleCat.{u + 1} B) f).obj F))
    (η : FinitePartsMaps f F H) : Prop :=
  ∀ (B' : Type (u + 1)) [CommRing B'] (φ : B →+* B')
    (F' H' : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B'))
    (ι' : H' ⟶ (lowerStar (ModuleCat.{u + 1} B') f).obj
      ((upperStar (ModuleCat.{u + 1} B') f).obj F')) [Mono ι'],
    FinitePartsSupportCondition f F' H' ι' →
    ∀ α : F ⟶ (Sheaf.restrictScalars S.smallEtaleTopology φ).obj F',
      ∃ (η' : FinitePartsMaps f F' H')
        (γ : H ⟶ (Sheaf.restrictScalars S.smallEtaleTopology φ).obj H'),
        IsFinitePartsGenerator f F' H' ι' η' ∧
        FinitePartsCoefficientMapCondition φ f ι ι' η η' α γ ∧
        ∀ (E : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
            Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B'))
          (adj : E ⊣ Sheaf.restrictScalars S.smallEtaleTopology φ)
          (e : E.obj F ≅ F'),
          α = adj.unit.app F ≫ (Sheaf.restrictScalars S.smallEtaleTopology φ).map e.hom →
          IsIso ((adj.homEquiv H H').symm γ)

/-- Finite clopen pieces present the proper-support direct image of an inverse image.
The support sheaf and its inclusion are specified by their defining membership property;
`properSupportSheafComposition` supplies such objects. Hence these arguments introduce
no extra geometric hypothesis or unspecified replacement for the canonical construction.

Source: SGA 4 XVII 6.2.1, (6.2.1.1–2), Proposition 6.2.2, pp. 420–422; the universal
property in the proof of 6.2.3, p. 425
(blueprint: lem-pur-quasifinite-finite-parts-presentation).

Proof:

1. Fix a basis of finite-presentation etale objects. The Noetherian hypothesis implies that $S$ is
locally Noetherian, so [lem-weil-pbc-locally-noetherian-quasi-separated] makes $S$
quasi-separated. By [lem-weil-pbc-qcqs-morphism-permanence](1), every affine etale $U\to S$ is of
finite presentation. The affine-shrink statement
[lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink] gives such an affine pointed
neighbourhood inside every given open neighbourhood of the marked point; objects of the small
etale site are covered by these affine objects [def-weil-pbc-etale-site]. Thus all subsequent
neighbourhoods may be replaced by objects of this basis. There is a set of isomorphism classes in
this basis: refine further so that $U$ maps into one member $\operatorname{Spec}R$ of a fixed
affine cover of $S$; its algebra is $R[t_1,\ldots,t_n]/(r_1,\ldots,r_m)$ for finite lists of
polynomials, and these lists form a set. Morphisms between two such algebras form a set as well.
Choosing representatives therefore gives a small basis; fibre products can be covered again by
this basis. This is the size convention for the etale-local colimit, not an assumption that an
arbitrary etale object is quasi-compact.

2. Fix $\bar s:\operatorname{Spec}\Omega\to S$ and let $s$ be its image. Quasi-finiteness gives a
finite list of all points of $X_s$ by [pqf-lem-qf-finitefibres]; they are isolated by the
definition [pqf-def-quasifinite]. Apply [lem-weil-pbc-etale-local-finite-multiple-points] to this
entire list. Its hypotheses hold: $f$ is locally of finite type (indeed of finite type) and the
listed fibre points are isolated. It gives an etale neighbourhood $(U,u)$ and finitely many finite
opens $V_a\subset X_U$, each with a unique point $v_a$ over $u$ and purely inseparable residue
extension $\kappa(v_a)/\kappa(u)$, the $v_a$ pairwise distinct and exhausting $(X_U)_u$. Choose a
lift of $\bar s$ to $U$ over the chosen $u$ using the more precise clause of
[lem-weil-pbc-etale-cover-geometric-point-lift], applied to the jointly surjective etale family
consisting of $U\to S$ and the identity of $S$. Restrict to an affine neighbourhood of $u$ as in
Step 1; [lem-weil-pbc-finite-morphism-permanence](a) preserves finiteness of the opens after this
restriction. If $X_s$ is empty use the trivial decomposition with only the remainder; no nonempty
finite piece is introduced.

3. Make those opens into the required disjoint clopen decomposition. The base-changed map $X_U\to
U$ is separated by [lem-weil-pbc-separated-lqf-base-change](1). Each $V_a\to U$ is proper by
[lem-weil-pbc-finite-proper], so its inclusion into $X_U$ is proper by
[lem-weil-pbc-proper-over-separated]; its image is closed by [lem-weil-pbc-proper-closed-image].
Thus $V_a$ is both open and closed in $X_U$. The intersection $V_a\cap V_b$ for $a\ne b$ is closed
in the proper $U$-scheme $V_a$, hence proper over $U$ by
[lem-weil-pbc-closed-immersion-proper](b). Its fibre at $u$ is empty, since its unique possible
points $v_a,v_b$ are distinct. Delete from $U$ the finitely many closed images of these
intersections, using [lem-weil-pbc-proper-closed-image]. The remaining open contains $u$, and the
$V_a$ are now disjoint. Let $V_0$ be their clopen complement; it has empty fibre at $u$. For each
$a\ne0$, the fibre $(V_a)_u\to\operatorname{Spec}\kappa(u)$ is radicial: it has a single point and
purely inseparable residue extension. The equivalence of radicial and universally injective in
[def-weil-radicial-morphism] implies that $(V_a)_{\bar s}$ has at most one point. It has a point
because the purely inseparable residue field embeds in the algebraically closed $\Omega$, and the
residue quotient followed by this embedding defines that point. Therefore each finite piece has
exactly one geometric fibre point, and the remainder has none. Take an affine neighbourhood of $u$
again to retain finite presentation as in Step 1. This proves the asserted existence of special
decompositions without assuming that $f$ is flat or etale.

4. Construct the generators for an arbitrary decomposition $\phi$. Write
$H=f_!^{\mathrm{supp}}f^*F$, $u:U\to S$, $p:X_U\to X$ and $v:X_U\to U$. The map $p$ is etale by
[lem-weil-pbc-etale-base-change-finite-limits](1). Identify inverse image along $u$ and $p$ with
restriction by [lem-weil-pbc-etale-inverse-image-restriction](1). The canonical proper-support
comparison [lem-cbc-proper-support-sheaf-composition] then identifies $H|_U$ with
$v_!^{\mathrm{supp}}p^{-1}f^*F$. Since $f\circ p=u\circ v$, the composition isomorphisms and their
unit formulas [lem-weil-pbc-sets-etale-inverse-image-composition-units](1) identify $p^{-1}f^*F$
with $v^*(F|_U)$, preserving pulled-back sections. These are identifications of module sheaves:
the actions and units have the stated underlying abelian-sheaf maps by
[prop-weil-pbc-inverse-image-modules-exact](2)–(3). By
[prop-weil-pbc-inverse-image-modules-exact](3), $v_i^*\dashv v_{i*}$ is the adjunction on
$B$-module sheaves, with the underlying inverse-image unit. On any etale $T\to U$, pull a section
$a\in F(T)$ back to $(V_i)_T$ by this unit, and extend it by zero on the other clopen pieces of
$X_T$. The sheaf axiom [def-weil-pbc-abelian-etale-sheaves] glues these sections uniquely on this
finite disjoint open cover. The resulting section has closed support contained in $(V_i)_T$, which
is finite over $T$ by [lem-weil-pbc-finite-morphism-permanence](a), hence proper by
[lem-weil-pbc-finite-proper]. Its closed support is proper by
[lem-weil-pbc-closed-subset-proper-over-base-properties](2). It therefore belongs to $H(T)$, by
the support-sheaf description [lem-cbc-proper-support-sheaf-composition]. Add these component maps
over $i\ne0$ to obtain $\eta_\phi$. Uniqueness of gluing and naturality of the unit make this a
$B$-linear sheaf map, compatible with etale restriction and natural in $F$.

5. Check the relations and the elementary common refinement. On a refined piece $V'_j$, the
section $\eta_\phi(a)$ is the pullback of $a_{\sigma(j)}$ if $\sigma(j)\ne0$, and zero otherwise.
These are exactly the restrictions of $\eta_{\phi'}t_\sigma(a)$. The sheaf axiom
[def-weil-pbc-abelian-etale-sheaves] gives equality on $X_T$ for every etale $T\to U$, hence
equality in the support subsheaf. The same coordinate calculation gives $t_{\sigma\rho}=t_\rho
t_\sigma$. Given two decompositions over $U$, take their intersections $V_i\cap W_j$ and label
$(0,0)$ as the remainder. Every other intersection is closed in a finite piece of at least one of
the decompositions; its inclusion is finite by [lem-weil-pbc-closed-immersion-finite], and its map
to $U$ is finite by [lem-weil-pbc-finite-composition]. The two index projections are pointed
refinement maps. This is an actual scheme-theoretic intersection of open subschemes, not a
factorization of a general immersion through a subset.

6. Compute the generator on each geometric stalk. The special decomposition of Steps 2–3
identifies $C=X_{\bar s}$ with a finite disjoint union of finite $\Omega$-schemes, one point in
each summand. The base-changed finite pieces are finite by
[lem-weil-pbc-finite-morphism-permanence](a); iterating [lem-weil-pbc-finite-coproduct] makes
$C\to\operatorname{Spec}\Omega$ finite (the empty union is $\operatorname{Spec}0$ and is finite).
Thus $C$ is proper by [lem-weil-pbc-finite-proper]; its underlying space is discrete, so it has
dimension at most zero. Every closed support on $C$ is proper by
[lem-weil-pbc-closed-subset-proper-over-base-properties](2). The restriction map of
[lem-cbc-proper-support-geometric-stalk], followed by the germ isomorphism
[lem-weil-pbc-zero-dimensional-sections-stalks], gives $$H_{\bar s}\cong
H^0_c(C,(f^*F)|_C)=\Gamma(C,(f^*F)|_C)\cong\prod_{x\in|C|}(f^*F)_{\bar
x}\cong\bigoplus_{x\in|C|}F_{\bar s}.$$ The last identifications use
[lem-weil-pbc-inverse-image-stalk-germ], applied to the projection $C\to X$ and then to $f$, and
finite product equals finite sum. The same lemma's unit formula identifies the map, not just its
source and target: for ANY decomposition $\phi$, $\eta_{\phi,\bar s}$ sends a tuple
$(a_i)_{i\ne0}$ to the tuple whose $x$-entry is $a_i$ when $x\in(V_i)_{\bar s}$ with $i\ne0$, and
zero when $x\in(V_0)_{\bar s}$. The source stalk is the finite sum of $F_{\bar s}$ by
[lem-kun-stalks-commute-colimits]. All maps are $B$-linear since they are restrictions and germs.
For a special decomposition this matrix is the identity after indexing its nonzero labels by the
fibre points, proving exactly the asserted stalk isomorphism.

7. A special decomposition can refine any prescribed finite list of decompositions after passing
to a smaller pointed neighbourhood. Choose a special decomposition $\theta=(W_j)$ near $\bar s$ by
Steps 2–3. Use the fibre-product clause of [lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered]
to pull it and all prescribed decompositions to one common pointed neighbourhood. It remains
special: finite pieces stay finite by [lem-weil-pbc-finite-morphism-permanence](a), and its
geometric fibre at the given lift is the same $\Omega$-scheme. For each prescribed $\phi=(V_i)$,
the unique geometric point of $(W_j)_{\bar s}$ for $j\ne0$ lies in a unique $V_{i(j)}$. Delete
from the base the images of $W_j\cap V_i$ for $j\ne0$, $i\ne i(j)$, and of $W_0\cap V_i$ for
$i\ne0$. Each of these intersections is finite over the base by Step 5, has empty geometric fibre
at the marked point, hence empty ordinary fibre there (a nonzero finite algebra over a field has a
point over an algebraic closure), and is proper by [lem-weil-pbc-finite-proper]. Its image is
closed by [lem-weil-pbc-proper-closed-image] and misses the marked point. There are only finitely
many intersections. After their deletion, $W_j\subseteq V_{i(j)}$ for $j\ne0$ and $W_0\subseteq
V_0$; setting $\sigma(0)=0$ and $\sigma(j)=i(j)$ gives the required refinement. The good finite
pieces keep their original single geometric points. Do this for every decomposition in the finite
list and take an affine neighbourhood as in Step 1. In particular, two presentations of a germ can
be compared in a refinement whose generator is an isomorphism at that germ. No generator is
asserted to be an isomorphism on an entire neighbourhood.

8. Prove the universal property on actual sections. Suppose a restriction-compatible
refinement-compatible family $g_\phi$ is given. For $h\in H(T)$ and each geometric point $\bar t$
of $T$, take a special decomposition near its image in $S$ and pull it to a pointed neighbourhood
of $\bar t$ in $T$; then take an affine neighbourhood as in Step 1. Its geometric fibre is
unchanged, so it is still special. This procedure uses the original $f$ and does not apply a
Noetherian-base assertion to an arbitrary non-quasi-compact etale $T$. By Step 6 the germ of $h$
has a unique tuple representative there. The neighbourhood category is cofiltered by
[lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered]. Consequently, in the stalk colimit
[def-weil-pbc-geometric-stalks], finitely many representatives can be restricted to one common
neighbourhood, and equality of two classes means equality after a further restriction: this is the
equivalence relation defining a filtered colimit of sets. Represent the finitely many tuple
coordinates this way; the equality with the germ of $h$ becomes an equality $h=\eta_\phi(a)$ after
further restriction. These neighbourhoods, one over every point of $T$, form an etale cover.
Assign to this local representative the section $g_\phi(a)$ of $G$. On an overlap compare two such
representatives at any geometric point, and choose the special common refinement of Step 7. Their
refined tuples have the same image under the injective stalk map $\eta_\theta$, hence are equal in
the finite tuple stalk. The refinement relations for $g$ show that the two candidate values have
equal germs. By [lem-weil-pbc-sets-sections-geometric-germ-ext] they agree as sections on the
overlap. Glue them uniquely by [def-weil-pbc-abelian-etale-sheaves]. This defines $g_T(h)\in G(T)$
independently of all choices. Restricting the chosen cover proves restriction compatibility. To
check addition and $B$-linearity, use common local refinements for the representatives of two
sections; there both assertions are the corresponding assertions for $g_\theta$, so descend by
uniqueness of gluing. For the generator identity, fix a tuple section $a$ for any $\phi$ and a
geometric point. Represent $h=\eta_\phi(a)$ locally by a tuple $b$ for a special decomposition
$\psi$ as above. Take a special common refinement $\theta$ with maps $\sigma:I_\theta\to I_\phi$
and $\rho:I_\theta\to I_\psi$. Step 5 gives $\eta_\theta(t_\sigma a)=h=\eta_\theta(t_\rho b)$.
Injectivity of $\eta_\theta$ at the chosen stalk gives $(t_\sigma a)_{\bar t}=(t_\rho b)_{\bar
t}$, so the family relations give $(g_\phi(a))_{\bar t}=(g_\theta(t_\sigma a))_{\bar
t}=(g_\theta(t_\rho b))_{\bar t}=(g_\psi(b))_{\bar t}=(g(h))_{\bar t}$. Germ extensionality now
proves $g\eta_\phi=g_\phi$. The morphism is unique because every section of $H$ locally has a
generator representative. Conversely a sheaf map gives such a family by Step 5 and restriction.
These constructions are inverse. This is the asserted etale-local colimit universal property
[def-weil-pbc-category-colimit], with the size convention of Step 1.

9. Check base change on the maps just constructed. For a Cartesian square with base map $b:S'\to
S$ and projection $a:X'\to X$, use the canonical comparison $b^{-1}H\cong
f'_!{}^{\mathrm{supp}}a^{-1}f^*F$ of [lem-cbc-proper-support-sheaf-composition]. An etale object
$U\to S$ pulls back to an etale object $U'=U\times_SS'\to S'$ by
[lem-weil-pbc-etale-base-change-finite-limits](1), and it is of finite presentation by
[lem-weil-pbc-qcqs-morphism-permanence](3). Clopen pieces pull back to clopen pieces (inverse
images of both the open and its complementary open), and finite pieces remain finite by
[lem-weil-pbc-finite-morphism-permanence](a). Inverse image preserves finite sums by
[prop-weil-pbc-inverse-image-modules-exact](3), and its module units are the underlying
abelian-sheaf units by the same clause. Its composition identifications respect pulled-back unit
sections by [lem-weil-pbc-sets-etale-inverse-image-composition-units](1); those identifications
also identify $a^{-1}f^*F$ with $f'^*b^{-1}F$. The support comparison is the restriction of the
ordinary pullback comparison on direct images, so it sends a unit section on $V_i$ extended by
zero to the pulled-back unit section on $V_i\times_SS'$ extended by zero. More explicitly, at a
geometric point of $S'$, both composites send $(a_i)$ to the tuple with entry $a_i$ on the
base-changed finite piece labelled $i$, and zero on its remainder, by Step 6 and
[lem-weil-pbc-inverse-image-stalk-germ]. Equality on these germs implies equality of maps on
sections by [lem-weil-pbc-sets-sections-geometric-germ-ext]. This proves base-change compatibility
of every generator and relation. This verification applies to any base map $b$: Step 4 constructs
the pulled-back generator using its given finite clopen pieces, and its stalk calculation uses
$X'_{\bar s'}\cong X_{b\bar s'}$, so the finite-fibre calculation of Step 6 applies directly.
Neither constructing a new basis on $S'$ nor assuming $S'$ Noetherian is required; the support
comparison has no flatness restriction on $b$.

10. Check coefficient homomorphisms, with ordinary sheaf scalar extension. Restriction of scalars
changes no underlying section, support, refinement matrix or unit-section formula. For $B\to B'$
put $F'=B'\otimes_BF$, defined by sectionwise scalar extension followed by sheafification
[def-pod-ring-scalar-extension]. The ordinary module adjunction on each section, together with the
universal property [def-weil-pbc-sheafification], gives the sheaf scalar-extension/restriction
adjunction: a map out of $B'\otimes_BM$ is precisely a compatible family of balanced maps
$B'\times M(T)\to N(T)$, equivalently a $B$-linear sheaf map $M\to\operatorname{Res}N$. Naturality
in $F$ from Step 4 applied to $F\to\operatorname{Res}F'$ therefore defines a canonical map
$$c:B'\otimes_B(f_!^{\mathrm{supp}}f^*F)\longrightarrow f_!^{\mathrm{supp}}f^*(B'\otimes_BF).$$ By
[lem-pod-etale-stalk-tensor-scalar](2) and the identifications in Step 6, its stalk is the
canonical map $$B'\otimes_B\bigoplus_xF_{\bar s}\longrightarrow\bigoplus_x(B'\otimes_BF_{\bar
s}),\qquad b'\otimes(a_x)_x\longmapsto(b'\otimes a_x)_x.$$ It is an isomorphism, with inverse the
sum of the tensor maps of the summand inclusions; the empty sum case is zero. Thus $c$ is an
isomorphism by [lemma-weil-pbc-geometric-stalk-conservative], applied to underlying abelian
sheaves. Under $c$ the scalar extension of each generator is the generator for $F'$: on tensor
elements the coordinate formula of Step 6 is unchanged, and
[lem-weil-pbc-sets-sections-geometric-germ-ext] makes the equality a sheaf equality. In particular
the same diagonal and zero matrices give all refinement relations over $B'$. No exactness or
flatness of $B'\otimes_B-$ is used. This completes all coefficient and base-change clauses.
-/
theorem quasiFinite_finiteParts_presentation
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFinitePresentation f]
    (hf : f.IsQuasiFinite) (B : Type (u + 1)) [CommRing B]
    (F H : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B))
    (ι : H ⟶ (lowerStar (ModuleCat.{u + 1} B) f).obj
      ((upperStar (ModuleCat.{u + 1} B) f).obj F)) [Mono ι]
    (hH : FinitePartsSupportCondition f F H ι) :
    (∃ η : FinitePartsMaps f F H,
      IsFinitePartsGenerator f F H ι η ∧ FinitePartsCompatible η ∧
      FinitePartsUniversal η ∧ FinitePartsStalkIso η ∧
      FinitePartsBaseChangeCompatible ι η ∧ FinitePartsCoefficientCompatible ι η) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      ∃ (U : S.Etale) (_ : QuasiCompact U.hom) (_ : QuasiSeparated U.hom)
        (t : Spec (.of Ω) ⟶ U.left) (D : FinitePartsDecomposition f U),
        t ≫ U.hom = s ∧ FinitePartsSpecial D t := by
  sorry

end AlgebraicGeometry.Etale
