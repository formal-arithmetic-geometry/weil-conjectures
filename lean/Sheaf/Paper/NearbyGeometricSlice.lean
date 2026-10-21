/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.Paper.GeneralNearbySliceTest
public import Sheaf.Paper.OrientedProductPointsConservative
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import Sheaf.TraceFormula.OrientedPointCohomology
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
import WeilConjectures.AlgebraicGeometry.FieldExtensionHigherDirectImageExchange
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf
import Sheaf.AlgebraicGeometry.StrictBaseClosedPointLocalizations
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.Paper.OrientedNearbyCycles
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.StrictHenselization

/-!
# The geometric generic slice of nearby cycles over a trait

Source: Illusie, Around the Thom--Sebastiani theorem, §§1.3--1.4,
(1.3.4) and (1.4.2)--(1.4.3) (blueprint: lem-trf-nearby-geometric-slice).

The generic object below is the chosen geometric point itself. The classical
comparison is the ordinary counit mate for j; its tensor map is the mate of the
tensor of counits. Neither map is assumed invertible.

## Main definitions

* `geometricSliceClassical`: the actual functor i* Rj* r*.
* `GeometricNearbySliceData`: the slice with its specified legs and specialization.
* `geometricSliceOrdinary`, `geometricSliceTensor`: the two classical comparison maps.

## Main statements

* `nearby_geometric_slice`: the bounded natural isomorphism and both compatibilities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v s

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.AdicSites

namespace AlgebraicGeometry.OrientedNearbyCycles

/-- The geometric fibre and strict-local base used in (1.3.4).
Source: Illusie §1.3 (blueprint: lem-trf-nearby-geometric-slice). -/
abbrev geometricSliceFibre {T B : Scheme.{u}} (f : T ⟶ B)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ B) :=
  pullback f b

/-- Base change to the recorded strict localization.
Source: Illusie §1.3 (blueprint: lem-trf-nearby-geometric-slice). -/
abbrev geometricSliceTube {T B : Scheme.{u}} (f : T ⟶ B)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ B) :=
  pullback f (Scheme.strictHenselizationStructuralMap b)

/-- The geometric generic fibre, with the nested fibre product of the statement.
Source: Illusie §1.3 (blueprint: lem-trf-nearby-geometric-slice). -/
abbrev geometricSliceGeneric {T B : Scheme.{u}} (f : T ⟶ B)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b) :=
  pullback (pullback.snd f (Scheme.strictHenselizationStructuralMap b)) t

/-- The special-fibre map induced by the distinguished strict-local closed lift.
Source: Illusie §1.3 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceI {T B : Scheme.{u}} (f : T ⟶ B)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ B) :
    geometricSliceFibre f b ⟶ geometricSliceTube f b :=
  pullback.map f b f (Scheme.strictHenselizationStructuralMap b) (𝟙 T)
    (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation b))) (𝟙 B)
    (Category.comp_id _ |>.trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Scheme.strictHenselizationClosedLift_over b).symm)

/-- The natural map from the geometric generic fibre to the strict-local tube.
Source: Illusie §1.3 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceJ {T B : Scheme.{u}} (f : T ⟶ B)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b) :
    geometricSliceGeneric f b t ⟶ geometricSliceTube f b :=
  pullback.fst _ _

/-- Restriction of an input from T to its geometric generic fibre.
Source: Illusie §1.3 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceR {T B : Scheme.{u}} (f : T ⟶ B)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b) :
    geometricSliceGeneric f b t ⟶ T :=
  geometricSliceJ f b t ≫ pullback.fst f (Scheme.strictHenselizationStructuralMap b)

/-- The actual classical functor i* Rj* r*, on the existing unbounded categories.
Source: Illusie (1.3.4) (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceClassical {T B : Scheme.{u}} (f : T ⟶ B)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b)
    (Λ : Type v) [CommRing Λ] :
    EtaleDerived T Λ ⥤ EtaleDerived (geometricSliceFibre f b) Λ :=
  (etaleModules (geometricSliceR f b t)).pull (Coeff.{u, v} Λ) ⋙
    (etaleModules (geometricSliceJ f b t)).push (Coeff.{u, v} Λ) ⋙
      (etaleModules (geometricSliceI f b)).pull (Coeff.{u, v} Λ)

/-- The point of a triple on this slice: its second leg lies over t, and its
middle lift extends over the special strict localization. This explicitly fixes
which specialization, including which geometric generic field, is used.
Source: Illusie §§1.1, 1.3 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSlicePoint {T B : Scheme.{u}} (f : T ⟶ B)
    {Ω Ξ K : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    [Field K] [IsAlgClosed K]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b)
    (x : Spec (.of K) ⟶ geometricSliceFibre f b) (Z : VanishingSite.{u, v} f) :=
  {p : (Spec (.of K) ⟶ (AsSmall.down.obj Z.left.1).left) ×
      (Spec (.of Ξ) ⟶ (AsSmall.down.obj Z.left.2).left) //
    p.1 ≫ (AsSmall.down.obj Z.left.1).hom = x ≫ pullback.fst f b ∧
    p.2 ≫ (AsSmall.down.obj Z.left.2).hom =
      t ≫ Scheme.strictHenselizationStructuralMap b ∧
    ∃ q : (Scheme.pointSmallEtale b).fiber.obj (AsSmall.down.obj Z.right),
      ∃ l : Scheme.strictHenselizationScheme b ⟶ (AsSmall.down.obj Z.right).left,
      l ≫ (AsSmall.down.obj Z.right).hom = Scheme.strictHenselizationStructuralMap b ∧
      Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation b)) ≫ l =
        q.left ∧
      p.1 ≫ (AsSmall.down.map Z.hom.1).left ≫
          pullback.fst (AsSmall.down.obj Z.right).hom f =
        x ≫ pullback.snd f b ≫ q.left ∧
      p.2 ≫ (AsSmall.down.map Z.hom.2).left = t ≫ l}

/-- Generator normalization of the geometric slice morphism. The equivalences
commute with every triple arrow, so this specifies the point functors, including
all their refinement maps, rather than only the sizes of their fibres.
Source: Illusie (1.1.2), (1.3.4) (blueprint: lem-trf-nearby-geometric-slice). -/
def IsGeometricNearbySlice {T B : Scheme.{u}} (f : T ⟶ B)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b)
    (e : GeometricMorphism
      (Sheaf (etaleTopology.{u, v} (geometricSliceFibre f b)) (Type (max (u + 1) v)))
      (VanishingTopos.{u, v} f)) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ geometricSliceFibre f b),
    ∃ θ : ∀ Z : VanishingSite.{u, v} f,
      (sliceStalk.{u, v} x).obj
        (e.inverse.obj ((OrientedProduct.associated (vanishingTopology f)).obj Z)) ≃
          geometricSlicePoint f b t x Z,
      ∀ (Z W : VanishingSite.{u, v} f) (k : Z ⟶ W)
        (z : (sliceStalk.{u, v} x).obj
          (e.inverse.obj ((OrientedProduct.associated (vanishingTopology f)).obj Z))),
        (θ W ((sliceStalk x).map
          (e.inverse.map ((OrientedProduct.associated (vanishingTopology f)).map k)) z)).val =
          ((θ Z z).val.1 ≫ (AsSmall.down.map k.left.1).left,
            (θ Z z).val.2 ≫ (AsSmall.down.map k.left.2).left)

/-- Global sections on the transported étale site.
Source: Illusie §1.1 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceSections (X : Scheme.{u}) :=
  (sheafSections (etaleTopology.{u, v} X) (Type (max (u + 1) v))).obj
    (op (⊤_ (EtaleSite.{u, v} X)))

/-- The structure morphism to sets, with the actual constant-sheaf inverse image.
Source: Illusie §1.1 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceEpsilon (X : Scheme.{u}) :
    GeometricMorphism
      (Sheaf (etaleTopology.{u, v} X) (Type (max (u + 1) v))) (Type (max (u + 1) v)) where
  inverse := constantSheaf (etaleTopology X) _
  direct := geometricSliceSections X
  adj := constantSheafAdj (etaleTopology X) _ terminalIsTerminal
  leftExact := by unfold constantSheaf; infer_instance

/-- The given geometric point as a morphism from sets, transported through the
recorded étale sheaf equivalence.
Source: Illusie §1.1 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceBasePoint {B : Scheme.{u}} {Ξ : Type u} [Field Ξ] [IsAlgClosed Ξ]
    (t : Spec (.of Ξ) ⟶ B) :
    GeometricMorphism (Type (max (u + 1) v))
      (Sheaf (etaleTopology.{u, v} B) (Type (max (u + 1) v))) where
  inverse := (geometricEtalePoint.{u, v} t).inverse ⋙
    punctualEquivalence.{max (u + 1) v}.functor
  direct := punctualEquivalence.{max (u + 1) v}.inverse ⋙
    (geometricEtalePoint.{u, v} t).direct
  adj := (geometricEtalePoint.{u, v} t).adj.comp
    punctualEquivalence.{max (u + 1) v}.toAdjunction
  leftExact := by
    let := (geometricEtalePoint.{u, v} t).leftExact
    infer_instance

/-- The slice's second leg is the constant geometric GENERIC point, obtained by
composing the structure morphism to sets with that point of the base.
Source: Illusie (1.1.2), (1.3.4) (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceSecond {T B : Scheme.{u}} (f : T ⟶ B)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b) :=
  (geometricSliceEpsilon.{u, v} (geometricSliceFibre f b)).comp
    (geometricSliceBasePoint (t ≫ Scheme.strictHenselizationStructuralMap b))

/-- The universal slice morphism with its two specified legs and its specialization
normalization on oriented points.
Source: Illusie (1.1.2), (1.3.4) (blueprint: lem-trf-nearby-geometric-slice). -/
structure GeometricNearbySliceData {T B : Scheme.{u}} (f : T ⟶ B)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b) where
  morphism : GeometricMorphism
    (Sheaf (etaleTopology.{u, v} (geometricSliceFibre f b)) (Type (max (u + 1) v)))
    (VanishingTopos.{u, v} f)
  first : (morphism.comp (p₁ f)).direct ≅ (etaleMorphism (pullback.fst f b)).direct
  second : (morphism.comp (p₂ f)).direct ≅ (geometricSliceSecond f b t).direct
  specialization : IsGeometricNearbySlice f b t morphism

set_option linter.checkUnivs false in
/-- Slice morphisms for every source over the fixed base and specialization.
Source: Illusie §1.3 (blueprint: lem-trf-nearby-geometric-slice). -/
abbrev GeometricNearbySliceFamily {B : Scheme.{u}} {Ω Ξ : Type u}
    [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b) :=
  ∀ {T : Scheme.{u}} (f : T ⟶ B), GeometricNearbySliceData.{u, v} f b t

/-- The existing constant-module lift of the slice.
Source: Illusie §1.3 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceModules {B : Scheme.{u}} {Ω Ξ : Type u}
    [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b)
    (E : GeometricNearbySliceFamily.{u, v} b t) {T : Scheme.{u}} (f : T ⟶ B) :=
  moduleMorphism (vanishingDatum f) (etaleDatum (geometricSliceFibre f b)) (E f).morphism

/-- Base change of h on the special geometric fibre.
Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceFibreMap {T T' B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ B) :
    geometricSliceFibre (h ≫ f) b ⟶ geometricSliceFibre f b :=
  pullback.map (h ≫ f) b f b h (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- Base change of h on the strict-local tube.
Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceTubeMap {T T' B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ B) :
    geometricSliceTube (h ≫ f) b ⟶ geometricSliceTube f b :=
  pullback.map (h ≫ f) (Scheme.strictHenselizationStructuralMap b) f
    (Scheme.strictHenselizationStructuralMap b) h (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The base-change map commutes with the projection to the strict-local base.
Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice).
Proof: the second-projection identity for pullback.map, followed by the identity law. -/
theorem geometricSliceTubeMap_snd {T T' B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ B) :
    geometricSliceTubeMap f h b ≫ pullback.snd f (Scheme.strictHenselizationStructuralMap b) =
      pullback.snd (h ≫ f) (Scheme.strictHenselizationStructuralMap b) := by
  sorry

/-- Base change of h on the geometric generic fibre.
Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceGenericMap {T T' B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b) :
    geometricSliceGeneric (h ≫ f) b t ⟶ geometricSliceGeneric f b t :=
  pullback.map (pullback.snd (h ≫ f) (Scheme.strictHenselizationStructuralMap b)) t
    (pullback.snd f (Scheme.strictHenselizationStructuralMap b)) t
    (geometricSliceTubeMap f h b) (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans (geometricSliceTubeMap_snd f h b).symm) (by simp)

/-- The three canonical fibre maps give the i, j, and restriction squares.
Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice).
Proof: compose with both pullback projections. The identities for pullback.map and
pullback.condition make the projections equal; pullback.hom_ext gives the i square.
The first projection of the second pullback gives the j square. Composing that
identity with the tube's first projection gives the restriction square. -/
theorem geometricSliceMap_squares {T T' B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b) :
    (geometricSliceI (h ≫ f) b ≫ geometricSliceTubeMap f h b =
      geometricSliceFibreMap f h b ≫ geometricSliceI f b) ∧
    (geometricSliceJ (h ≫ f) b t ≫ geometricSliceTubeMap f h b =
      geometricSliceGenericMap f h b t ≫ geometricSliceJ f b t) ∧
    (geometricSliceGenericMap f h b t ≫ geometricSliceR f b t =
      geometricSliceR (h ≫ f) b t ≫ h) := by
  sorry

/-- The classical ordinary comparison, using the inverse-image square for i,
then the counit mate for j, then restriction of the input along h.
Source: Illusie (1.4.3) (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceOrdinary {T T' B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b)
    (Λ : Type v) [CommRing Λ] (L : EtaleDerived T Λ) :
    ((etaleModules (geometricSliceFibreMap f h b)).pull (Coeff.{u, v} Λ)).obj
        ((geometricSliceClassical f b t Λ).obj L) ⟶
      (geometricSliceClassical (h ≫ f) b t Λ).obj
        (((etaleModules h).pull (Coeff.{u, v} Λ)).obj L) :=
  (slicePullSquare (geometricSliceTubeMap f h b) (geometricSliceFibreMap f h b)
      (geometricSliceI (h ≫ f) b) (geometricSliceI f b)
      (geometricSliceMap_squares f h b t).1 Λ).hom.app _ ≫
    ((etaleModules (geometricSliceI (h ≫ f) b)).pull (Coeff.{u, v} Λ)).map
      (((etaleModules (geometricSliceJ (h ≫ f) b t)).adj (Coeff.{u, v} Λ)).homEquiv _ _
        ((slicePullSquare (geometricSliceJ f b t) (geometricSliceJ (h ≫ f) b t)
          (geometricSliceGenericMap f h b t) (geometricSliceTubeMap f h b)
          (geometricSliceMap_squares f h b t).2.1.symm Λ).hom.app _ ≫
            ((etaleModules (geometricSliceGenericMap f h b t)).pull (Coeff.{u, v} Λ)).map
              (((etaleModules (geometricSliceJ f b t)).adj (Coeff.{u, v} Λ)).counit.app _))) ≫
    ((etaleModules (geometricSliceI (h ≫ f) b)).pull (Coeff.{u, v} Λ)).map
      (((etaleModules (geometricSliceJ (h ≫ f) b t)).push (Coeff.{u, v} Λ)).map
        ((slicePullSquare (geometricSliceR f b t) (geometricSliceR (h ≫ f) b t)
          (geometricSliceGenericMap f h b t) h
          (geometricSliceMap_squares f h b t).2.2 Λ).inv.app L))

/-- The lax tensor map for the classical j-direct image is the transpose of the
tensor of its two counits, using the recorded canonical derived tensor comparison.
Source: Stacks 07A4; Illusie §1.3 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceJLax {T B : Scheme.{u}} (f : T ⟶ B)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b)
    (Λ : Type v) [CommRing Λ] (P Q : EtaleDerived (geometricSliceGeneric f b t) Λ) :
    (derivedTensor (etaleDatum (geometricSliceTube f b)) (Coeff.{u, v} Λ)).obj
      (((etaleModules (geometricSliceJ f b t)).push (Coeff.{u, v} Λ)).obj P,
        ((etaleModules (geometricSliceJ f b t)).push (Coeff.{u, v} Λ)).obj Q) ⟶
      ((etaleModules (geometricSliceJ f b t)).push (Coeff.{u, v} Λ)).obj
        ((derivedTensor (etaleDatum (geometricSliceGeneric f b t)) (Coeff.{u, v} Λ)).obj
          (P, Q)) :=
  ((etaleModules (geometricSliceJ f b t)).adj (Coeff.{u, v} Λ)).homEquiv _ _
    ((pullTensor (etaleModules (geometricSliceJ f b t)) (Coeff.{u, v} Λ)).hom.app _ ≫
      (derivedTensor (etaleDatum (geometricSliceGeneric f b t)) (Coeff.{u, v} Λ)).map
        (Prod.mkHom
          (((etaleModules (geometricSliceJ f b t)).adj (Coeff.{u, v} Λ)).counit.app P)
          (((etaleModules (geometricSliceJ f b t)).adj (Coeff.{u, v} Λ)).counit.app Q)))

/-- The lax tensor map of i* Rj* r*: move through the canonical tensor comparisons
for i and r, and use the tensor-of-counits mate for j in between.
Source: Stacks 07A4; Illusie §1.3 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceTensor {T B : Scheme.{u}} (f : T ⟶ B)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b)
    (Λ : Type v) [CommRing Λ] (L M : EtaleDerived T Λ) :
    (derivedTensor (etaleDatum (geometricSliceFibre f b)) (Coeff.{u, v} Λ)).obj
        ((geometricSliceClassical f b t Λ).obj L, (geometricSliceClassical f b t Λ).obj M) ⟶
      (geometricSliceClassical f b t Λ).obj
        ((derivedTensor (etaleDatum T) (Coeff.{u, v} Λ)).obj (L, M)) :=
  (pullTensor (etaleModules (geometricSliceI f b)) (Coeff.{u, v} Λ)).inv.app
      (((etaleModules (geometricSliceJ f b t)).push (Coeff.{u, v} Λ)).obj
        (((etaleModules (geometricSliceR f b t)).pull (Coeff.{u, v} Λ)).obj L),
       ((etaleModules (geometricSliceJ f b t)).push (Coeff.{u, v} Λ)).obj
        (((etaleModules (geometricSliceR f b t)).pull (Coeff.{u, v} Λ)).obj M)) ≫
    ((etaleModules (geometricSliceI f b)).pull (Coeff.{u, v} Λ)).map
      (geometricSliceJLax f b t Λ _ _) ≫
    ((etaleModules (geometricSliceI f b)).pull (Coeff.{u, v} Λ)).map
      (((etaleModules (geometricSliceJ f b t)).push (Coeff.{u, v} Λ)).map
        ((pullTensor (etaleModules (geometricSliceR f b t)) (Coeff.{u, v} Λ)).inv.app (L, M)))

/-- Direct image preserves global sections, by the unique isomorphism of final
étale objects. Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceDirectSections {X Y : Scheme.{u}} (a : X ⟶ Y) :
    (etaleMorphism.{u, v} a).direct ⋙ geometricSliceSections.{u, v} Y ≅
      geometricSliceSections.{u, v} X :=
  NatIso.ofComponents (fun (H : Sheaf (etaleTopology.{u, v} X)
      (Type (max (u + 1) v))) ↦ H.obj.mapIso
    ((terminalIsTerminal.isTerminalObj (etaleBaseChange.{u, v} a)
      (⊤_ (EtaleSite.{u, v} Y))).uniqueUpToIso
        (terminalIsTerminal (C := EtaleSite.{u, v} X))).symm.op)
    (by intro H K g; exact (g.hom.naturality _).symm)

/-- The actual base-change identity on an étale object, induced by pullback.fst.
Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceIdentityComponent (B : Scheme.{u}) (V : EtaleSite.{u, v} B) :
    (etaleBaseChange (𝟙 B)).obj V ≅ V :=
  AsSmall.up.mapIso (MorphismProperty.Over.isoMk
    (asIso (pullback.fst (AsSmall.down.obj V).hom (𝟙 B)))
    (by
      change pullback.fst (AsSmall.down.obj V).hom (𝟙 B) ≫ (AsSmall.down.obj V).hom =
        pullback.snd (AsSmall.down.obj V).hom (𝟙 B)
      simpa only [Category.comp_id] using
        (pullback.condition (f := (AsSmall.down.obj V).hom) (g := 𝟙 B))))

/-- The identity-base-change components commute with every étale arrow.
Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice).
Proof: compose with pullback.fst. The naturality identity for pullback.map gives
both sides, and the first projection is invertible. -/
theorem geometricSliceIdentity_naturality (B : Scheme.{u})
    (V W : EtaleSite.{u, v} B) (a : V ⟶ W) :
    (etaleBaseChange (𝟙 B)).map a ≫ (geometricSliceIdentityComponent B W).hom =
      (geometricSliceIdentityComponent B V).hom ≫ a := by
  sorry

/-- Canonical identity-base-change isomorphism on the transported étale site.
Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceIdentitySite (B : Scheme.{u}) :
    etaleBaseChange.{u, v} (𝟙 B) ≅ 𝟭 (EtaleSite.{u, v} B) :=
  NatIso.ofComponents (geometricSliceIdentityComponent B)
    (fun {V W} a ↦ geometricSliceIdentity_naturality B V W a)

/-- The identity scheme morphism induces the identity direct image, with the
canonical pullback.fst normalization.
Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceIdentity (B : Scheme.{u}) : (etaleMorphism.{u, v} (𝟙 B)).direct ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousIso (geometricSliceIdentitySite B)
    (Type (max (u + 1) v)) (etaleTopology B) (etaleTopology B)

/-- The first-projection identity for the special fibre map.
Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice).
Proof: the first-projection identity for pullback.map and the identity law. -/
theorem geometricSliceFibreMap_fst {T T' B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ B) :
    geometricSliceFibreMap f h b ≫ pullback.fst f b = pullback.fst (h ≫ f) b ≫ h := by
  sorry

/-- The commutative source square over the identity of B.
Source: Illusie (1.4.1) (blueprint: lem-trf-nearby-geometric-slice).
Proof: the right identity law. -/
theorem geometricSliceSourceSquare {T T' B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T) :
    h ≫ f = (h ≫ f) ≫ 𝟙 B := by
  sorry

/-- First projection of v e', normalized by the two existing universal lifts.
Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceSquareFirst {T T' B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b)
    (E : GeometricNearbySliceFamily.{u, v} b t) :
    (((E (h ≫ f)).morphism.comp
        (squareMorphism f (h ≫ f) h (𝟙 B) (geometricSliceSourceSquare f h))).comp
      (p₁ f)).direct ≅
      ((etaleMorphism (pullback.fst (h ≫ f) b)).comp (etaleMorphism h)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (E (h ≫ f)).morphism.direct
      (squareLift f (h ≫ f) h (𝟙 B) (geometricSliceSourceSquare f h)).first ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (E (h ≫ f)).first (etaleMorphism h).direct

/-- First projection of e h_b, normalized by the actual fibre-product square.
Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceFibreFirst {T T' B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b)
    (E : GeometricNearbySliceFamily.{u, v} b t) :
    (((etaleMorphism (geometricSliceFibreMap f h b)).comp (E f).morphism).comp
      (p₁ f)).direct ≅
      ((etaleMorphism (pullback.fst (h ≫ f) b)).comp (etaleMorphism h)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (etaleMorphism (geometricSliceFibreMap f h b)).direct (E f).first ≪≫
    squareDirect (pullback.fst f b) (pullback.fst (h ≫ f) b)
      (geometricSliceFibreMap f h b) h (geometricSliceFibreMap_fst f h b)

/-- Second projection of v e', normalized at the same constant generic point.
Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceSquareSecond {T T' B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b)
    (E : GeometricNearbySliceFamily.{u, v} b t) :
    (((E (h ≫ f)).morphism.comp
        (squareMorphism f (h ≫ f) h (𝟙 B) (geometricSliceSourceSquare f h))).comp
      (p₂ f)).direct ≅ (geometricSliceSecond (h ≫ f) b t).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (E (h ≫ f)).morphism.direct
      (squareLift f (h ≫ f) h (𝟙 B) (geometricSliceSourceSquare f h)).second ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (E (h ≫ f)).second (etaleMorphism (𝟙 B)).direct ≪≫
    Functor.isoWhiskerLeft (geometricSliceSecond (h ≫ f) b t).direct
      (geometricSliceIdentity B) ≪≫ Functor.rightUnitor _

/-- Second projection of e h_b, using the canonical invariance of global sections
under direct image. Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceFibreSecond {T T' B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b)
    (E : GeometricNearbySliceFamily.{u, v} b t) :
    (((etaleMorphism (geometricSliceFibreMap f h b)).comp (E f).morphism).comp
      (p₂ f)).direct ≅ (geometricSliceSecond (h ≫ f) b t).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (etaleMorphism (geometricSliceFibreMap f h b)).direct (E f).second ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (geometricSliceDirectSections (geometricSliceFibreMap f h b))
      (geometricSliceBasePoint (t ≫ Scheme.strictHenselizationStructuralMap b)).direct

/-- The localized inverse-image square of slice morphisms. The input is the
projection-compatible geometric square, so the constant-module comparison uses
precisely the same generator normalization as ordinary nearby base change.
Source: Illusie §1.4 (blueprint: lem-trf-nearby-geometric-slice). -/
def geometricSliceSquare {T T' B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b)
    (E : GeometricNearbySliceFamily.{u, v} b t)
    (γ : ((E (h ≫ f)).morphism.comp
        (squareMorphism f (h ≫ f) h (𝟙 B) (geometricSliceSourceSquare f h))).direct ≅
      ((etaleMorphism (geometricSliceFibreMap f h b)).comp (E f).morphism).direct)
    (Λ : Type v) [CommRing Λ] :
    (squareModules f (h ≫ f) h (𝟙 B) (geometricSliceSourceSquare f h)).pull (Coeff.{u, v} Λ) ⋙
        (geometricSliceModules b t E (h ≫ f)).pull (Coeff.{u, v} Λ) ≅
      (geometricSliceModules b t E f).pull (Coeff.{u, v} Λ) ⋙
        (etaleModules (geometricSliceFibreMap f h b)).pull (Coeff.{u, v} Λ) :=
  derivedSquare (f := geometricSliceModules b t E f)
    (g := squareModules f (h ≫ f) h (𝟙 B) (geometricSliceSourceSquare f h))
    (h := etaleModules (geometricSliceFibreMap f h b)) (k := geometricSliceModules b t E (h ≫ f))
    (GeometricMorphism.inverseIso γ).symm (Coeff.{u, v} Λ)

/-- A natural comparison of the two actual derived functors, for all sources
needed by arbitrary source pullback. Isomorphism is asserted only on the inputs
specified in the theorem, not on arbitrary unbounded complexes.
Source: Illusie (1.3.4) (blueprint: lem-trf-nearby-geometric-slice). -/
abbrev GeometricSliceComparisonFamily {B : Scheme.{u}} {Ω Ξ : Type u}
    [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ B) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b)
    (E : GeometricNearbySliceFamily.{u, v} b t) (Λ : Type v) [CommRing Λ] :=
  ∀ {T : Scheme.{u}} (f : T ⟶ B),
    nearbyCycles f Λ ⋙ (geometricSliceModules b t E f).pull (Coeff.{u, v} Λ) ⟶
      geometricSliceClassical f b t Λ

/-- Geometric generic slices identify oriented and classical nearby cycles,
including ordinary source-pullback and lax tensor comparisons.

Source: Illusie, Around the Thom--Sebastiani theorem, §§1.3--1.4, especially
(1.3.4), (1.4.2)--(1.4.3); the tensor assertion uses the tensor-of-counits
construction and Stacks 07A4 (blueprint: lem-trf-nearby-geometric-slice).

Proof plan (the six steps of the DAG):
1. Apply lem-trf-oriented-product-universal to the fibre map as first leg,
and the constant geometric GENERIC point as second leg. The specialization
through the strict localization supplies the orientation. Its triple-point
formula is precisely geometricSlicePoint, with its refinement maps.
2. Restrict sections on triples to the geometric generic fibre and sheafify.
Apply this same restriction to direct-image resolutions for every input; this
constructs the natural comparison before taking stalks. The two legs and the
specialization give the recorded slice morphism, not a free geometric morphism.
3. At a geometric point of the special fibre, use
lem-weil-pbc-strict-base-closed-point-localizations to identify strict localizations.
The higher-direct-image presheaf formula
lem-weil-pbc-site-higher-direct-image-sheafified-presheaf, thm-sp-truncation-e2,
and lem-weil-pbc-derived-etale-cohomology-limit compute the classical stalk.
Use lem-weil-pbc-etale-module-cohomology-forget to forget constant scalars.
The oriented stalk is the Milnor tube by lem-trf-oriented-point-cohomology.
4. Separate the generic field enlargement into a purely inseparable algebraic
extension and an extension of algebraically closed fields, using
lem-weil-pbc-separable-first-purely-inseparable. The first gives a universal
homeomorphism by lem-pc-spec-pure-insep-integral-radicial-surjective and
lem-pc-integral-radicial-surjective-universal-homeomorphism; apply
lemma-weil-pbc-universal-homeomorphism-site-equivalence. For the second apply
lem-sc-field-extension-higher-direct-image-exchange with the given invertible
annihilator. Truncation extends the result to bounded inputs. Then
lem-weil-pbc-derived-stalk-conservative proves the slice comparison invertible.
This includes generic geometric fields transcendental over their images.
5. For arbitrary h, the universal property identifies v e' with e h_b by the
unique isomorphism compatible with BOTH projections. Expand the ordinary maps
as unit, inverse-image square, and counit (def-weil-pbc-adjunction-mate).
In the resolution models restriction commutes with pullback and evaluation of
sections, so the displayed ordinary square commutes. No finite-type condition
on h or on h followed by f is used. The same stalk calculation supplies the
comparison isomorphism on h*L.
6. Resolve tensor inputs by K-flat complexes. The lax direct-image map is the
mate of the tensor of counits. Restriction of the tensor of two evaluated
sections is the tensor of their restrictions. The canonical pullTensor
isomorphisms, from lem-weil-pbc-ringed-topoi-derived-tensor-pullback, identify
these targets, giving the displayed equality of derived maps. This is checked
on the resolution maps, not inferred from equality of cohomology stalks.
The tensor input need not itself be bounded. Neither ordinary nor tensor
comparison is asserted invertible.
-/
theorem nearby_geometric_slice
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (Λ : Type v) [CommRing Λ] [Finite Λ]
    (m : ℕ) (hmΛ : ∀ a : Λ, m • a = 0) (hmR : IsUnit (m : R))
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (b : Spec (.of Ω) ⟶ Spec (.of R))
    (hb : b (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint R)
    (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme b)
    (ht : IsGenericPoint (t (IsLocalRing.closedPoint Ξ)) Set.univ) :
    ∃ (E : GeometricNearbySliceFamily.{u, v} b t)
      (α : GeometricSliceComparisonFamily b t E Λ),
      (∃ η : sliceBoundedInclusion T Λ ⋙ nearbyCycles f Λ ⋙
            (geometricSliceModules b t E f).pull (Coeff.{u, v} Λ) ≅
          sliceBoundedInclusion T Λ ⋙ geometricSliceClassical f b t Λ,
        η.hom = Functor.whiskerLeft (sliceBoundedInclusion T Λ) (α f)) ∧
      (∀ (T' : Scheme.{u}) (h : T' ⟶ T),
        ∃ γ : ((E (h ≫ f)).morphism.comp
            (squareMorphism f (h ≫ f) h (𝟙 _) (geometricSliceSourceSquare f h))).direct ≅
          ((etaleMorphism (geometricSliceFibreMap f h b)).comp (E f).morphism).direct,
          (Functor.isoWhiskerRight γ (p₁ f).direct ≪≫ geometricSliceFibreFirst f h b t E =
            geometricSliceSquareFirst f h b t E) ∧
          (Functor.isoWhiskerRight γ (p₂ f).direct ≪≫ geometricSliceFibreSecond f h b t E =
            geometricSliceSquareSecond f h b t E) ∧
          ∀ (L : EtaleDerived T Λ)
            (_hL : IsBounded (etaleDatum.{u, v} T) (Coeff.{u, v} Λ) L),
            IsIso ((α (h ≫ f)).app (((etaleModules h).pull (Coeff.{u, v} Λ)).obj L)) ∧
            (geometricSliceSquare f h b t E γ Λ).hom.app ((nearbyCycles f Λ).obj L) ≫
              ((etaleModules (geometricSliceFibreMap f h b)).pull (Coeff.{u, v} Λ)).map
                ((α f).app L) ≫ geometricSliceOrdinary f h b t Λ L =
              ((geometricSliceModules b t E (h ≫ f)).pull (Coeff.{u, v} Λ)).map
                (baseChange f (h ≫ f) h (𝟙 _) (geometricSliceSourceSquare f h) Λ L) ≫
                  (α (h ≫ f)).app (((etaleModules h).pull (Coeff.{u, v} Λ)).obj L)) ∧
      (∀ (L M : EtaleDerived T Λ)
        (_hL : IsBounded (etaleDatum.{u, v} T) (Coeff.{u, v} Λ) L)
        (_hM : IsBounded (etaleDatum.{u, v} T) (Coeff.{u, v} Λ) M),
        (pullTensor (geometricSliceModules b t E f) (Coeff.{u, v} Λ)).inv.app
            ((nearbyCycles f Λ).obj L, (nearbyCycles f Λ).obj M) ≫
          ((geometricSliceModules b t E f).pull (Coeff.{u, v} Λ)).map (laxTensor f Λ L M) ≫
          (α f).app ((derivedTensor (etaleDatum T) (Coeff.{u, v} Λ)).obj (L, M)) =
        (derivedTensor (etaleDatum (geometricSliceFibre f b)) (Coeff.{u, v} Λ)).map
          (Prod.mkHom ((α f).app L) ((α f).app M)) ≫ geometricSliceTensor f b t Λ L M) := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles
