/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.AlgebraicGeometry.SmoothAnalytificationCotangent
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Field.ULift
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import Sheaf.CategoryTheory.RingedAcyclicResolutionDerivedMaps
import Sheaf.AlgebraicGeometry.AnalyticPullbackExact
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.Topology.ClosedImmersionPushforwardCohomology
import Sheaf.AlgebraicGeometry.AnalyticClosedDirectImage
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import Sheaf.Geometry.Complex.AnalyticProjectiveStructureCohomology
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Sheaf.AlgebraicGeometry.FixedHyperplaneRestrictionCohomology
import Mathlib.Algebra.Homology.ModelCategory.Injective
import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Canonical derived GAGA for finite locally free coefficients

Source: Serre, Géométrie algébrique et géométrie analytique, nos. 11--13,
printed pp.18--22 (blueprint: lem-sfb-gaga-derived-coherent-sections).

The scalar sheaves use the existing scalar restriction and Mathlib's forgetful functor.
Their nonnegative injective-resolution sections represent derived global sections in
D+(Vect_C). The comparison is localized from every augmentation-compatible lift of the
specified tensor-section map, so its canonicity is part of the statement.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.SmoothAnalytic

/-- The existing analytification, viewed as a sheaf of complex vector spaces by restriction
along the canonical complex scalar map. Source: Serre, GAGA, nos. 9 and 11
(blueprint: lem-sfb-gaga-derived-coherent-sections). -/
noncomputable abbrev analyticVectorSheaf {X : Scheme.{u}} {f : X ⟶ Spec (.of (ULift.{u} ℂ))}
    (D : Data f) (F : X.Modules) :
    Sheaf (Opens.grothendieckTopology D.space) (ModuleCat.{u} (ULift.{u} ℂ)) :=
  ((SheafOfModules.forgetToSheafModuleCat (moduleRings D.space) (op ⊤)
      isTerminalTop.op) ⋙
    sheafCompose _ (ModuleCat.restrictScalars
      ((D.pi.hom.c.app (op ⊤)).hom.comp (Scheme.Modules.scalarMap (k := ULift.{u} ℂ) f ⊤)))).obj
        (analytify D F)

/-- Global sections of vector-space sheaves: Mathlib's sheaf evaluation on the whole space.
Source: Serre, GAGA, no. 11 (blueprint: lem-sfb-gaga-derived-coherent-sections). -/
abbrev gagaSections (T : TopCat.{u}) :
    Sheaf (Opens.grothendieckTopology T) (ModuleCat.{u} (ULift.{u} ℂ)) ⥤
      ModuleCat.{u} (ULift.{u} ℂ) :=
  (sheafSections _ _).obj (op ⊤)

/-- A nonnegative resolution model for R Gamma of a vector-space sheaf placed in degree zero.
Source: Serre, GAGA, no. 11, derived reformulation
(blueprint: lem-sfb-gaga-derived-coherent-sections). -/
noncomputable def gagaResolutionSections {T : TopCat.{u}}
    {V : Sheaf (Opens.grothendieckTopology T) (ModuleCat.{u} (ULift.{u} ℂ))}
    (I : InjectiveResolution V) : CochainComplex.Plus (ModuleCat.{u} (ULift.{u} ℂ)) :=
  ⟨((gagaSections T).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex,
    0, inferInstance⟩

/-- Apply global sections to a resolution lift. Sections of direct image are literally
sections on the source space. Source: Serre, GAGA, no. 11, derived reformulation
(blueprint: lem-sfb-gaga-derived-coherent-sections). -/
noncomputable def gagaResolutionSectionsMap {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ULift.{u} ℂ))) (D : Data f) (F : X.Modules)
    (I : InjectiveResolution (Scheme.Modules.scalarSheaf (k := ULift.{u} ℂ) f F))
    (J : InjectiveResolution (analyticVectorSheaf D F))
    (u : I.cochainComplex ⟶
      ((TopCat.Sheaf.pushforward (ModuleCat.{u} (ULift.{u} ℂ))
        D.pi.hom.base).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex) :
    gagaResolutionSections (T := X.toTopCat) I ⟶
      gagaResolutionSections (T := D.space.toPresheafedSpace.carrier) J :=
  ObjectProperty.homMk (((gagaSections X.toTopCat).mapHomologicalComplex (.up ℤ)).map u)

/-- A lift represents the coefficient map precisely when its degree-zero augmentation square
commutes. The source F[0] is zero in other degrees, so this is the full augmentation square.
Source: Serre, GAGA, no. 11, canonical comparison; derived resolution interpretation
(blueprint: lem-sfb-gaga-derived-coherent-sections). -/
def IsGagaResolutionLift {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ULift.{u} ℂ))) (D : Data f) (F : X.Modules)
    (a : Scheme.Modules.scalarSheaf (k := ULift.{u} ℂ) f F ⟶
      (TopCat.Sheaf.pushforward (ModuleCat.{u} (ULift.{u} ℂ)) D.pi.hom.base).obj
        (analyticVectorSheaf D F))
    (I : InjectiveResolution (Scheme.Modules.scalarSheaf (k := ULift.{u} ℂ) f F))
    (J : InjectiveResolution (analyticVectorSheaf D F))
    (u : I.cochainComplex ⟶
      ((TopCat.Sheaf.pushforward (ModuleCat.{u} (ULift.{u} ℂ))
        D.pi.hom.base).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex) : Prop :=
  I.ι.f 0 ≫ (I.cochainComplexXIso 0 0 rfl).inv ≫ u.f 0 =
    a ≫ (TopCat.Sheaf.pushforward (ModuleCat.{u} (ULift.{u} ℂ)) D.pi.hom.base).map
      (J.ι.f 0 ≫ (J.cochainComplexXIso 0 0 rfl).inv)

/-- Derived GAGA for the canonical tensor-section comparison, in complex vector spaces.
The two derived objects are represented by global sections of arbitrary injective
resolutions in complex-vector-space sheaves. The augmentation condition fixes the
canonical derived arrow: all compatible lifts have the same homotopy class.

Source: Serre, GAGA, no. 11 and no. 12, Theorem 1, printed pp.18--22;
agent-written derived reformulation and finite-resolution proof variant
(blueprint: lem-sfb-gaga-derived-coherent-sections).

Proof plan, following the ten steps of the node:
1. Choose a projective embedding into P^n. Projective-field coordinates give properness,
   Noetherianity and coherence. Finite locally free F is coherent; its closed direct
   image is coherent. The standard affine charts make P^n smooth. Use
   lem-sfb-projective-field-coordinate-euler-polynomial, pqf-lem-coherent-ft-locnoeth,
   lem-pc-closed-immersion-coherent-cohomology, sbc-lem-affine-space-smooth and
   lem-weil-pbc-smooth-local-on-source. Apply the analytification-cotangent theorem.
2. Restrict both coefficient sheaves to complex vector spaces, with enough injectives.
   The tensor-section maps give a. Exact inverse image and injective lifting extend
   its augmentation to every pair of resolutions. Ringed derived evaluation and
   lem-sfb-ringed-acyclic-resolution-derived-maps identify the localized section map
   with the derived-pushforward and derived-sections arrow. Its degree-zero value is
   s maps to 1 tensor s. Scalar actions agree by naturality in complex multiplication.
3. The topos pullback delta theorem and lem-sfb-analytic-pullback-exact identify these
   comparisons on short exact sequences and their connecting maps. Global sections
   are additive and left exact, so the derived long exact sequences apply.
4. Closed direct image preserves cohomology on both spaces. The coefficient-compatible
   lem-sfb-analytic-closed-direct-image identifies the comparisons for F and i_*F.
5. The five-term exact-sequence argument transfers invertibility from any two members
   of a short exact sequence to its third member, in every degree.
6. Algebraic twist cohomology and lem-sfb-analytic-projective-structure-cohomology give
   the comparison for O on P^n: identity on constants and maps of zero groups otherwise.
   For n=0 the single standard-chart frame treats every twist.
7. The fixed coordinate hyperplane sequence, given by
   lem-sfb-fixed-hyperplane-restriction-cohomology, propagates the comparison between
   twists d and d-1. Induct on n and then in both directions on d, starting at d=0.
8. Additivity and the finite biproduct identities prove comparison for finite sums of
   twists, including the empty sum.
9. Apply lem-sfb-projective-coherent-finite-twist-resolution to i_*F. Descend along the
   kernel short exact sequences, using analytic exactness without assumptions on the
   kernels, and transfer back to F by step 4.
10. Negative cohomology vanishes for these nonnegative resolution section complexes.
    The bounded-below cohomology criterion gives invertibility of the actual localized
    section map. Injective comparison uniqueness makes every normalized lift represent
    that arrow. Empty X, zero F and components of varying dimension are included. -/
theorem gaga_derived_coherent_sections {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ULift.{u} ℂ))) [Smooth f] [IsProjective f]
    (D : Data f) (F : X.Modules) [F.IsFiniteLocallyFree]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} (ULift.{u} ℂ))] :
    ∃ a : Scheme.Modules.scalarSheaf (k := ULift.{u} ℂ) f F ⟶
        (TopCat.Sheaf.pushforward (ModuleCat.{u} (ULift.{u} ℂ)) D.pi.hom.base).obj
          (analyticVectorSheaf D F),
      (∀ (U : X.Opens) (s : F.val.obj (op U)),
        a.hom.app (op U) s = tensorSection D F U 1 s) ∧
      ∀ (I : InjectiveResolution (Scheme.Modules.scalarSheaf (k := ULift.{u} ℂ) f F))
        (J : InjectiveResolution (analyticVectorSheaf D F)),
        (∃ u : I.cochainComplex ⟶
            ((TopCat.Sheaf.pushforward (ModuleCat.{u} (ULift.{u} ℂ))
              D.pi.hom.base).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex,
          IsGagaResolutionLift f D F a I J u) ∧
        ∀ u : I.cochainComplex ⟶
            ((TopCat.Sheaf.pushforward (ModuleCat.{u} (ULift.{u} ℂ))
              D.pi.hom.base).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex,
          IsGagaResolutionLift f D F a I J u →
            IsIso (DerivedCategory.Plus.Q.map (gagaResolutionSectionsMap f D F I J u)) := by
  sorry

end AlgebraicGeometry.SmoothAnalytic
