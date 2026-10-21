/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Sheaf.Paper.GeneralNearbySliceTest
public import Sheaf.Paper.OrientedProperFibreExchange
public import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Paper.OrientedNearbyCycles
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.TraceFormula.OrientedPointCohomology
import Sheaf.Paper.OrientedProductPointsConservative
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization

/-!
# Geometric specialization slices of nearby cycles

Source: ILO, Exposé XI §§1.4, 1.9, 2.2--2.3, 2.7, 4.3
(blueprint: lem-trf-nearby-specialization-slice).

The slice is the universal lift of the specified strict-local specialization.
All coefficient categories and ordinary comparisons are the recorded ones.

## Main definitions

* `sliceLift` and `canonicalSlices`: the projection-normalized universal slices.
* `rho`: the inverse-image square with both point projections normalized.
* `Compatible` and `SuccessiveCompatible`: the ordinary counit-mate equalities.

## Main statements

* `canonicalSlices_points` and `slice_exact`: the point formula and exactness.
* `nearbySpecializationSlice`: the natural slice formula and vanishing detection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.AdicSites

namespace AlgebraicGeometry.OrientedNearbyCycles.SpecializationSlice

/-- The orientation bπ ⇒ fd_a is the actual strict-local restriction c.
Source: ILO XI §§1.4, 2.2 (blueprint: lem-trf-nearby-specialization-slice). -/
def sliceOrientation {X S : Scheme.{u}} (f : X ⟶ S) (s : SliceSpecialization S) :
    (((ProperFibre.fibreGlobal.{u, v} f s.a).comp (geometricEtalePoint s.b)).comp
        (identity _)).direct ⟶
      ((etaleMorphism (pullback.fst f s.a)).comp (etaleMorphism f)).direct :=
  (Functor.rightUnitor _).hom ≫
    Functor.whiskerLeft (ProperFibre.fibreGlobal f s.a).direct
      (ProperFibre.specializationDirect s.a s.b s.c s.over) ≫
    (ProperFibre.fibreFactor f s.a).inv

/-- The canonical slice e, together with its projections and orientation identity.
Source: ILO XI Theorem 1.4, §§2.2--2.3
(blueprint: lem-trf-nearby-specialization-slice). -/
def sliceLift {X S : Scheme.{u}} (f : X ⟶ S) (s : SliceSpecialization S) :=
  lift.{u, v} f
    (Sheaf (etaleTopology (s.fibre f)) (Type (max (u + 1) v))) (sheaf_isTopos _)
    (etaleMorphism (pullback.fst f s.a))
    ((ProperFibre.fibreGlobal f s.a).comp (geometricEtalePoint s.b))
    (sliceOrientation f s)

/-- The family of canonical geometric slices, built from their normalized universal lifts.
Source: ILO XI Theorem 1.4, §§2.2--2.3
(blueprint: lem-trf-nearby-specialization-slice). -/
def canonicalSlices : SpecializationSliceFamily.{u, v} :=
  fun f s ↦ (sliceLift.{u, v} f s).morphism

/-- The canonical slice has exactly the oriented points (x,b,c), naturally on triples.
Source: ILO XI §§1.8--1.12, 2.2--2.3, 4.3
(blueprint: lem-trf-nearby-specialization-slice).
Proof: apply the oriented-product universal lift to the point x of the fibre. Its
first projection is x followed by the fibre projection and its second projection is
b; the orientation is restriction along c by sliceOrientation. On a triple generator,
the neighbourhood-colimit formula identifies a germ with its two compatible étale
lifts. The intermediate lift extends uniquely over the special strict localization
and its restriction by c is the generic lift. These are precisely the equations of
slicePoint, and composition of triple arrows gives the stated naturality. -/
theorem canonicalSlices_points {X S : Scheme.{u}} (f : X ⟶ S)
    (s : SliceSpecialization S) :
    IsSpecializationSlice f s (canonicalSlices.{u, v} f s) := by
  sorry

/-- The left side e^* RΨ_f, on the same unbounded ambient categories.
Source: ILO XI §4.3 (blueprint: lem-trf-nearby-specialization-slice). -/
def restricted {X S : Scheme.{u}} (f : X ⟶ S) (s : SliceSpecialization S)
    (Λ : Type v) [CommRing Λ] : EtaleDerived.{u, v} X Λ ⥤ EtaleDerived.{u, v} (s.fibre f) Λ :=
  nearbyCycles.{u, v} f Λ ⋙ (sliceModules canonicalSlices.{u, v} f s).pull (Coeff.{u, v} Λ)

section Square
variable {X S X' T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
  (h : X' ⟶ X) (k : T ⟶ S) (comm : h ≫ f = f' ≫ k)
  (s : SliceSpecialization S) (t : SliceSpecialization T) (d : SliceChange f f' h k s t)

/-- First projection of v e_T, normalized to the induced fibre map to X.
Source: ILO XI §1.9 (blueprint: lem-trf-nearby-specialization-slice). -/
def squareFirstLeft :
    (((sliceLift.{u, v} f' t).morphism.comp (squareMorphism f f' h k comm)).comp
        (p₁ f)).direct ≅ (etaleMorphism (d.fibreMap ≫ pullback.fst f s.a)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (squareLift f f' h k comm).first ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sliceLift f' t).first _ ≪≫
    etaleComposition _ _ ≪≫
    eqToIso (congrArg (fun a ↦ (etaleMorphism.{u, v} a).direct)
      d.fibreLeft.symm)

/-- First projection of e q_a, with the same normalization.
Source: ILO XI §1.9 (blueprint: lem-trf-nearby-specialization-slice). -/
def squareFirstRight :
    (((etaleMorphism.{u, v} (d.fibreMap)).comp
      (sliceLift f s).morphism).comp (p₁ f)).direct ≅
        (etaleMorphism (d.fibreMap ≫ pullback.fst f s.a)).direct :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (sliceLift f s).first ≪≫
    etaleComposition _ _

/-- Composition with a field map preserves the pointed-lift equation.
Source: ILO XI §1.9 (blueprint: lem-trf-nearby-specialization-slice).
Proof: reassociate e followed by l and the étale structure map, apply l.w, then he. -/
theorem pointExtension_liftOver {Z : Scheme.{u}} {Ω Ξ : Type u}
    [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (x : Spec (.of Ω) ⟶ Z) (y : Spec (.of Ξ) ⟶ Z)
    (e : Spec (.of Ξ) ⟶ Spec (.of Ω)) (he : e ≫ x = y)
    (V : EtaleSite.{u, v} Z)
    (l : (Scheme.pointSmallEtale x).fiber.obj (AsSmall.down.obj V)) :
    (e ≫ l.left) ≫ (AsSmall.down.obj V).hom = y := by
  sorry

/-- Geometric points related by a field extension have the unique direct-image
identification that reindexes every skyscraper product by composition of lifts.
Source: ILO XI §§1.8--1.9 (blueprint: lem-trf-nearby-specialization-slice).
Proof: an étale scheme over an algebraically closed field is a disjoint union of copies
of its spectrum. Thus composition with e gives a bijection on pointed étale lifts.
Reindex each skyscraper product by this bijection. Its product projections give the
formula, naturality, and uniqueness, and inverse reindexing gives invertibility. -/
theorem pointExtension_existsUnique {Z : Scheme.{u}} {Ω Ξ : Type u}
    [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (x : Spec (.of Ω) ⟶ Z) (y : Spec (.of Ξ) ⟶ Z)
    (e : Spec (.of Ξ) ⟶ Spec (.of Ω)) (he : e ≫ x = y) :
    ∃! z : (geometricEtalePoint.{u, v} y).direct ≅ (geometricEtalePoint x).direct,
      ∀ (M : Sheaf punctualSite.{max (u + 1) v}.topology (Type (max (u + 1) v)))
        (V : EtaleSite.{u, v} Z)
        (l : (Scheme.pointSmallEtale x).fiber.obj (AsSmall.down.obj V)),
        ((z.hom.app M).hom.app (Opposite.op V)) ≫
            Pi.π (fun _ : (Scheme.pointSmallEtale x).fiber.obj (AsSmall.down.obj V) ↦
              punctualEquivalence.functor.obj M) l =
          Pi.π (fun _ : (Scheme.pointSmallEtale y).fiber.obj (AsSmall.down.obj V) ↦
              punctualEquivalence.functor.obj M)
            (Over.homMk (e ≫ l.left) (pointExtension_liftOver x y e he V l)) := by
  sorry

/-- The canonical field-extension identification of points.
Source: ILO XI §1.9 (blueprint: lem-trf-nearby-specialization-slice). -/
def pointExtension {Z : Scheme.{u}} {Ω Ξ : Type u}
    [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (x : Spec (.of Ω) ⟶ Z) (y : Spec (.of Ξ) ⟶ Z)
    (e : Spec (.of Ξ) ⟶ Spec (.of Ω)) (he : e ≫ x = y) :=
  (pointExtension_existsUnique.{u, v} x y e he).choose

/-- The global-sections morphisms of the geometric fibres commute with q_a.
The identification is unique: both functors represent Hom from the terminal sheaf.
Source: ILO XI §§1.4, 1.9 (blueprint: lem-trf-nearby-specialization-slice).
Proof: fibreGlobal is global sections followed by the punctual equivalence, since the
base field is algebraically closed. Direct image preserves global sections. Thus the
two functors are canonically isomorphic. Their natural automorphisms correspond, by
Yoneda and the punctual equivalence, to automorphisms of the terminal sheaf; these are
identities, which proves uniqueness without a choice of a field automorphism. -/
theorem globalSquare_existsUnique :
    ∃ e : (ProperFibre.fibreGlobal.{u, v} f' t.a).direct ≅
        (etaleMorphism (d.fibreMap)).direct ⋙
          (ProperFibre.fibreGlobal f s.a).direct,
      ∀ e' : (ProperFibre.fibreGlobal.{u, v} f' t.a).direct ≅
          (etaleMorphism (d.fibreMap)).direct ⋙
            (ProperFibre.fibreGlobal f s.a).direct, e' = e := by
  sorry

/-- The unique global-sections identification.
Source: ILO XI §1.9 (blueprint: lem-trf-nearby-specialization-slice). -/
def globalSquare := (globalSquare_existsUnique.{u, v} f f' h k s t d).choose

/-- The second projection of v e_T, compared with e q_a by the specified field map
on b and the unique global-sections comparison.
Source: ILO XI §1.9 (blueprint: lem-trf-nearby-specialization-slice). -/
def squareSecond :
    (((sliceLift.{u, v} f' t).morphism.comp
        (squareMorphism f f' h k comm)).comp (p₂ f)).direct ≅
      (((etaleMorphism (d.fibreMap)).comp
        (sliceLift f s).morphism).comp (p₂ f)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (squareLift f f' h k comm).second ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sliceLift f' t).second _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ProperFibre.pointComposition k t.b) ≪≫
    Functor.isoWhiskerLeft _ (pointExtension s.b (t.b ≫ k) d.bMap d.bOver.symm) ≪≫
    Functor.isoWhiskerRight (globalSquare f f' h k s t d) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sliceLift f s).second.symm ≪≫
    (Functor.associator _ _ _).symm

/-- The unique projection-compatible square v e_T ≅ e q_a.
Source: ILO XI Theorem 1.4 and §1.9 (blueprint: lem-trf-nearby-specialization-slice).
Proof: the pointed equations of d identify the two pasted orientations after the
specified field-extension and global-section comparisons. Apply the uniqueness
clause of the oriented-product universal property; the two projection equations fix
its unique isomorphism. -/
theorem sliceSquare_existsUnique :
    ∃! e : ((sliceLift.{u, v} f' t).morphism.comp
        (squareMorphism f f' h k comm)).direct ≅
      ((etaleMorphism (d.fibreMap)).comp (sliceLift f s).morphism).direct,
      Functor.isoWhiskerRight e (p₁ f).direct ≪≫
          squareFirstRight f f' h k s t d = squareFirstLeft f f' h k comm s t d ∧
        Functor.isoWhiskerRight e (p₂ f).direct = squareSecond f f' h k comm s t d := by
  sorry

/-- The canonical projection-compatible slice square.
Source: ILO XI §1.9 (blueprint: lem-trf-nearby-specialization-slice). -/
def sliceSquare := (sliceSquare_existsUnique.{u, v} f f' h k comm s t d).choose

/-- The inverse-image square ρ uses the recorded generator-normalized module square.
Source: ILO XI §1.9 (blueprint: lem-trf-nearby-specialization-slice). -/
def rho (Λ : Type v) [CommRing Λ] :
    (squareModules.{u, v} f f' h k comm).pull (Coeff.{u, v} Λ) ⋙
        (sliceModules canonicalSlices f' t).pull (Coeff.{u, v} Λ) ≅
      (sliceModules canonicalSlices f s).pull (Coeff.{u, v} Λ) ⋙
        (etaleModules.{u, v} d.fibreMap).pull (Coeff.{u, v} Λ) :=
  OrientedNearbyCycles.sliceSquare canonicalSlices f f' h k comm s t d
    (sliceSquare f f' h k comm s t d) Λ

end Square

/-- A family of comparison transformations; its components on D⁺ are asserted
invertible below. The ambient maps allow the ordinary counit comparisons to be typed
without choosing a boundedness witness for each exact pullback.
Source: ILO XI §4.3 (blueprint: lem-trf-nearby-specialization-slice). -/
abbrev ComparisonFamily (Λ : Type v) [CommRing Λ] :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (s : SliceSpecialization S),
    restricted.{u, v} f s Λ ⟶ SliceSpecialization.complex.{u, v} s f Λ

/-- Equality of the specified ordinary oriented mate with the sliced ordinary mate,
conjugated by the comparison transformations and the canonical square ρ.
Source: ILO XI §§1.9, 4.3 (blueprint: lem-trf-nearby-specialization-slice). -/
def Compatible (Λ : Type v) [CommRing Λ] (α : ComparisonFamily.{u, v} Λ) : Prop :=
  ∀ {X S X' T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType f'] [QuasiCompact f']
    (h : X' ⟶ X) (k : T ⟶ S) (comm : h ≫ f = f' ≫ k),
    IsPullback h f' f k → ∀ (s : SliceSpecialization S) (t : SliceSpecialization T)
      (d : SliceChange f f' h k s t) (K : EtaleDerived.{u, v} X Λ),
      ProperFibre.IsBoundedBelow (etaleDatum.{u, v} X) (Coeff.{u, v} Λ) K →
      ((sliceModules canonicalSlices.{u, v} f' t).pull (Coeff.{u, v} Λ)).map
          (baseChange f f' h k comm Λ K) ≫
          (α f' t).app (((etaleModules.{u, v} h).pull (Coeff.{u, v} Λ)).obj K) =
        (rho f f' h k comm s t d Λ).hom.app ((nearbyCycles.{u, v} f Λ).obj K) ≫
          ((etaleModules.{u, v} (d.fibreMap)).pull (Coeff.{u, v} Λ)).map
            ((α f s).app K) ≫ ordinarySliceComparison f f' h k s t d Λ K

/-- The two paths through two successive base changes, as an equality of derived
morphisms with every coefficient and square identification displayed. Naturality in
K is already carried by ComparisonFamily and the ordinary mate constructions.
Source: ILO XI §1.9 (blueprint: lem-trf-nearby-specialization-slice). -/
def SuccessiveCompatible (Λ : Type v) [CommRing Λ] (α : ComparisonFamily.{u, v} Λ) : Prop :=
  ∀ {X₀ S₀ X₁ S₁ X₂ S₂ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
    [LocallyOfFiniteType f₀] [QuasiCompact f₀] [LocallyOfFiniteType f₁] [QuasiCompact f₁]
    [LocallyOfFiniteType f₂] [QuasiCompact f₂]
    (h₁ : X₁ ⟶ X₀) (k₁ : S₁ ⟶ S₀) (w₁ : h₁ ≫ f₀ = f₁ ≫ k₁)
    (h₂ : X₂ ⟶ X₁) (k₂ : S₂ ⟶ S₁) (w₂ : h₂ ≫ f₁ = f₂ ≫ k₂),
    IsPullback h₁ f₁ f₀ k₁ → IsPullback h₂ f₂ f₁ k₂ →
    ∀ (s₀ : SliceSpecialization S₀) (s₁ : SliceSpecialization S₁)
      (s₂ : SliceSpecialization S₂)
      (d₁ : SliceChange f₀ f₁ h₁ k₁ s₀ s₁) (d₂ : SliceChange f₁ f₂ h₂ k₂ s₁ s₂)
      (K : EtaleDerived.{u, v} X₀ Λ),
      ProperFibre.IsBoundedBelow (etaleDatum.{u, v} X₀) (Coeff.{u, v} Λ) K →
      ((sliceModules canonicalSlices.{u, v} f₂ s₂).pull (Coeff.{u, v} Λ)).map
          (((squareModules.{u, v} f₁ f₂ h₂ k₂ w₂).pull (Coeff.{u, v} Λ)).map
            (baseChange f₀ f₁ h₁ k₁ w₁ Λ K)) ≫
        ((sliceModules canonicalSlices.{u, v} f₂ s₂).pull (Coeff.{u, v} Λ)).map
          (baseChange f₁ f₂ h₂ k₂ w₂ Λ
            (((etaleModules.{u, v} h₁).pull (Coeff.{u, v} Λ)).obj K)) ≫
        (α f₂ s₂).app
          (((etaleModules.{u, v} h₂).pull (Coeff.{u, v} Λ)).obj
            (((etaleModules.{u, v} h₁).pull (Coeff.{u, v} Λ)).obj K)) =
      (rho f₁ f₂ h₂ k₂ w₂ s₁ s₂ d₂ Λ).hom.app
          (((squareModules.{u, v} f₀ f₁ h₁ k₁ w₁).pull (Coeff.{u, v} Λ)).obj
            ((nearbyCycles.{u, v} f₀ Λ).obj K)) ≫
        ((etaleModules.{u, v} (d₂.fibreMap)).pull (Coeff.{u, v} Λ)).map
          ((rho f₀ f₁ h₁ k₁ w₁ s₀ s₁ d₁ Λ).hom.app ((nearbyCycles.{u, v} f₀ Λ).obj K)) ≫
        ((etaleModules.{u, v} (d₂.fibreMap)).pull (Coeff.{u, v} Λ)).map
          (((etaleModules.{u, v} (d₁.fibreMap)).pull (Coeff.{u, v} Λ)).map
            ((α f₀ s₀).app K)) ≫
        ((etaleModules.{u, v} (d₂.fibreMap)).pull (Coeff.{u, v} Λ)).map
          (ordinarySliceComparison f₀ f₁ h₁ k₁ s₀ s₁ d₁ Λ K) ≫
        ordinarySliceComparison f₁ f₂ h₂ k₂ s₁ s₂ d₂ Λ
          (((etaleModules.{u, v} h₁).pull (Coeff.{u, v} Λ)).obj K)

/-- Exactness of the actual module inverse image of every specialization slice.
Source: ILO XI §§1.4, 2.3; Stacks 03D2
(blueprint: lem-trf-nearby-specialization-slice).
Proof: sliceLift is a geometric morphism, hence its inverse image is left exact and
is a left adjoint. The canonical constant-ring identification transports addition and
scalar multiplication. Thus the constant-module inverse image preserves finite limits
and finite colimits, by lem-pe-constant-left-module-inverse-image. -/
theorem slice_exact {X S : Scheme.{u}} (f : X ⟶ S) (s : SliceSpecialization S)
    (Λ : Type v) [CommRing Λ] :
    PreservesFiniteLimits
      ((sliceModules canonicalSlices.{u, v} f s).modulePull (Coeff.{u, v} Λ)) ∧
      PreservesFiniteColimits
        ((sliceModules canonicalSlices.{u, v} f s).modulePull (Coeff.{u, v} Λ)) := by
  sorry

/-- Geometric specialization slices of oriented nearby cycles, their ordinary-mate
compatibility for arbitrary and successive base changes, and detection of cohomology
vanishing on the unbounded vanishing-topos category.
Source: ILO XI §§1.4, 1.9, 2.2--2.3, 2.7, 4.3
(blueprint: lem-trf-nearby-specialization-slice).

Proof (the eleven steps of the DAG node):
1. The oriented-product universal property gives sliceLift from d_a and bπ with the
   strict-local orientation c. Composition with a geometric point gives (x,b,c).
   Constant-module inverse image is exact (lem-pe-constant-left-module-inverse-image).
2. For every triple C and compatible lifts v at a and w at b, lift v and w to the
   strict localizations. The closed-germ bijection and strict-henselization functoriality
   make their composites agree. The resulting étale E_v over X_(a) has fibre U_(a,v)
   and a specified map E_v × S_(b) → U ×_V W.
3. Restrict a section of F(U ×_V W) along this map, then apply the inverse-image unit
   for i_a. Naturality on all triples gives the global sheaf morphism χ_F; this is a
   sectionwise construction, not an attempt to glue maps in a derived category from
   their stalks. Use direct-image and inverse-image-module formulas in the cited nodes.
4. On an injective representative I of K, compose χ_I with the right-derived unit
   for j_* to obtain α_K. No injectivity or acyclicity of r_b^*I is assumed.
   K-injective homotopy uniqueness makes this independent of representatives and
   natural in K (def-sfb-right-derived-functor, lem-weil-pbc-kinjective-hom-derived).
5. Both stalks are cohomology of X_(x) × S_(b): use oriented-point cohomology,
   strict-henselization-stalk-formula, and ind-étale strict-local invariance. The map
   between strict localizations and j are affine, hence qcqs. Forget coefficients by
   the scalar-comparison nodes. All cohomology is torsion; m need not be invertible.
6. The already constructed map restricts along the same maps of tubes on both sides.
   Thus its stalk map is the identity of that tube cohomology. Derived stalk
   conservativity and conservative scalar forgetting prove it invertible on D⁺.
7. Define E and γ by the actual j counit and inverse-image composition comparisons,
   exactly as ordinarySliceComparison in the recorded interface. No Cartesian claim
   about the j square is used.
8. On every triple and every component, both underived routes restrict a section along
   the same composite E_(vT) × T_(bT) → U ×_V W. Projection equality, inverse-image-unit
   naturality and the formula for the ordinary sheaf mate prove equality globally.
9. Derive that square with injective replacements and the right-derived units. Maps
   into K-injectives are unique up to homotopy. Derived-adjunction normalization retains
   the original counits, giving Compatible for the specified β, γ and ρ.
10. Mate pasting and coherent inverse-image composition give the identical equality
    for two successive changes. Both j and ψ mates paste, their middle unit/counit
    pairs cancel, and the projection-compatible ρ squares compose. This proves the
    displayed SuccessiveCompatible equality, without faithfulness of derived stalks.
11. Exact inverse images commute with H^i. Every specialization-triple point factors
    through a slice, taking a=f(x), allowing extension of the geometric fields.
    Conservativity of the triple points applied to 0 → H^i(A) proves the reverse
    implication for every i ≤ r; the forward implication follows from exactness.

The comparison family is supplied as a theorem witness, together with its naturality,
invertibility and specified-mate equations. No arbitrary comparison map is selected
as a definition. -/
theorem nearbySpecializationSlice (Λ : Type v) [CommRing Λ]
    (m : ℕ) (hm : 1 ≤ m) (hΛ : ∀ a : Λ, (m : Λ) * a = 0) :
    (∃ α : ComparisonFamily.{u, v} Λ,
      (∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
        (s : SliceSpecialization S) (K : EtaleDerived.{u, v} X Λ),
        ProperFibre.IsBoundedBelow (etaleDatum.{u, v} X) (Coeff.{u, v} Λ) K →
          IsIso ((α f s).app K)) ∧
      Compatible.{u, v} Λ α ∧ SuccessiveCompatible.{u, v} Λ α) ∧
    (∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
      (A : VanishingDerived.{u, v} f Λ) (r₀ : ℤ),
      sliceVanishing (vanishingDatum.{u, v} f) (Coeff.{u, v} Λ) r₀ A ↔
        ∀ s : SliceSpecialization S,
          sliceVanishing (etaleDatum.{u, v} (s.fibre f)) (Coeff.{u, v} Λ) r₀
            (((sliceModules canonicalSlices.{u, v} f s).pull (Coeff.{u, v} Λ)).obj A)) := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles.SpecializationSlice
