/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.AffineTraceTower
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data
public import Sheaf.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange

import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Compactification.ProjectiveSpace
import Sheaf.AlgebraicGeometry.OpenClosedRecollement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.Paper.RingedTopoiDerivedTensorPullback
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection

/-!
# The actual affine-space counit trace

Source: blueprint sec-smooth-purity/sk-prop-an, Steps 5(b) and 6, detailed lemma
lem-amb-affine-space-top-trace (blueprint: lem-amb-affine-space-top-trace).

The coordinate model is `affineTraceTower S d`. Its unbounded left functor and right
functor are ordered composites of the affine-line functors; the zero-dimensional
adjunction is literally the identity. In the right functor, each coordinate contributes
one ordinary finite Tate line and a shift by two. This is the coordinate-tower expression
for p* K(d)[2d], with the canonical tensor, shift and inverse-image identifications.
The bounded-below comparison below uses the existing coherent compact-support composition
isomorphisms. Neither the counit nor its base-change map is chosen independently.

## Main definitions and statement

- `affineTraceAdjunction`: the specified ordered open/projective composite.
- `affineTraceCompactSupportComparison`: the canonical comparison on D+.
- `affineTraceCounit`: its actual counit at the constant coefficient complex.
- `affineTraceExchange`: the coordinatewise pasted compact-support exchange.
- `exists_affineSpaceTopTrace`: invertibility and arbitrary Noetherian base change.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- One affine-line left functor, on its specified standard compactification.
Source: blueprint sk-prop-an, Step 5(b) (blueprint: lem-amb-affine-space-top-trace). -/
@[implicit_reducible]
def affineTraceLineLeft (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S) ⥤ DerivedCategoryModule A S :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (affineTraceLineCompactification S)

/-- The right functor obtained by restricting the normalized projective-line right
functor to the standard affine chart. Source: blueprint sk-prop-an, Step 5(b)
(blueprint: lem-amb-affine-space-top-trace). -/
@[implicit_reducible]
def affineTraceLineRight (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) :
    DerivedCategoryModule A S ⥤ DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S) :=
  ordinaryFiniteP1Right A N hA S ⋙ ordinaryFinitePullback A (ProjectiveLine.affineChart S)

/-- Compose the actual open adjunction with the actual normalized projective adjunction.
Source: blueprint sk-prop-an, Step 5(b) (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceLineAdjunction (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (D : OrdinaryFiniteP1Datum A N hA t S hS) :
    affineTraceLineLeft A S ⊣ affineTraceLineRight A N hA S :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
    (ProjectiveLine.affineChart S)).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (ProjectiveLine.affineChart S)).symm).comp D.adjunction

/-- The ordered unbounded left functor of the coordinate tower.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceLeft (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategoryModule A (affineTraceTower S d) ⥤ DerivedCategoryModule A S
  | 0 => 𝟭 _
  | d + 1 => affineTraceLineLeft A (affineTraceTower S d) ⋙ affineTraceLeft A S d

/-- The ordered right functor: p* K(d)[2d] written as the iterated shifted-line twists.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceRight (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategoryModule A S ⥤ DerivedCategoryModule A (affineTraceTower S d)
  | 0 => 𝟭 _
  | d + 1 => affineTraceRight A N hA S d ⋙
      affineTraceLineRight A N hA (affineTraceTower S d)

/-- The literal composite adjunction, with the literal identity adjunction in dimension zero.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceAdjunction (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    (d : ℕ) → affineTraceLeft A S d ⊣ affineTraceRight A N hA S d
  | 0 => Adjunction.id
  | d + 1 =>
    (affineTraceLineAdjunction A N hA t (affineTraceTower S d)
      (affineTraceInvertible N S hS d)
      (@D (affineTraceTower S d) (affineTraceNoetherian S d)
        (affineTraceInvertible N S hS d))).comp
      (affineTraceAdjunction A N hA t D S hS d)

/-- The actual trace, the counit at the constant coefficient complex. Its source is
F_d applied to the coordinate-tower model of A(d)[2d].
Source: blueprint sk-prop-an, Steps 5(b), 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceCounit (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :=
  (affineTraceAdjunction A N hA t D S hS d).counit.app (ordinaryFiniteUnit A S)

/-- The bounded-below version of the same ordered left functor.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceLeftPlus (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategory.Plus
        (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
  | 0 => 𝟭 _
  | d + 1 => rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification (affineTraceTower S d)) ⋙ affineTraceLeftPlus A S d

/-- The canonical coherent comparison of the ordered tower with Rp_d! on D+.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceCompactSupportComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] : (d : ℕ) →
    affineTraceLeftPlus A S d ≅
      rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) (affineTraceProjection S d)
  | 0 => (rightDerivedLowerShriekPlusId A S).symm
  | d + 1 =>
    letI := affineTraceNoetherian S d
    let e₁ := rightDerivedLowerShriekOfCompactificationPlusIso A
      (f := AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (affineTraceLineCompactification (affineTraceTower S d))
      (HasCompactification.compactification
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d))
    let e₂ := affineTraceCompactSupportComparison A S d
    let e₃ := rightDerivedLowerShriekPlusCompIso A
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (affineTraceProjection S d)
    Functor.isoWhiskerRight e₁ (affineTraceLeftPlus A S d) ≪≫
      Functor.isoWhiskerLeft
        (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A)
          (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)) e₂ ≪≫ e₃

/-- The restriction of the unbounded tower to D+ is its bounded-below tower.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTracePlusCompatibility (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    (d : ℕ) → affineTraceLeftPlus A S d ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ affineTraceLeft A S d
  | 0 => Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm
  | d + 1 =>
    let L := rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification (affineTraceTower S d))
    let F := affineTraceLeftPlus A S d
    let l := affineTraceLineLeft A (affineTraceTower S d)
    let f := affineTraceLeft A S d
    let e := rightDerivedLowerShriekOfCompactificationPlusCompatibility (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification (affineTraceTower S d))
    let r := affineTracePlusCompatibility A S d
    Functor.associator L F DerivedCategory.Plus.ι ≪≫
      Functor.isoWhiskerLeft L r ≪≫
      (Functor.associator L DerivedCategory.Plus.ι f).symm ≪≫
      Functor.isoWhiskerRight e f ≪≫ Functor.associator DerivedCategory.Plus.ι l f

/-- Canonical proper exchange followed by open exchange and the coherent comparison
back to the standard compactification on the changed base.
Source: blueprint sk-prop-an, Step 5(b) (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceLineExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (f : S' ⟶ S)
    (M : DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S)) :
    (ordinaryFinitePullback A f).obj ((affineTraceLineLeft A S).obj M) ⟶
      (affineTraceLineLeft A S').obj
        ((ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f)).obj M) :=
  let e₁ := rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
    (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f)
    (affineTraceLineCompactification S)
  let e₂ := rightDerivedLowerShriekOfCompactificationIso A
    ((affineTraceLineCompactification S).ofIsPullback
      (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f))
    (affineTraceLineCompactification S')
  e₁.app M ≫ e₂.hom.app _

/-- The canonical exchange of the ordered coordinate tower, obtained by pasting the
proper/open exchanges of its coordinate steps. Source: blueprint sk-prop-an, Step 6
(blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (f : S' ⟶ S) : (d : ℕ) →
    (M : DerivedCategoryModule A (affineTraceTower S d)) →
    (ordinaryFinitePullback A f).obj ((affineTraceLeft A S d).obj M) ⟶
      (affineTraceLeft A S' d).obj
        ((ordinaryFinitePullback A (affineTraceMap f d)).obj M)
  | 0, M => 𝟙 ((ordinaryFinitePullback A f).obj M)
  | d + 1, M =>
    affineTraceExchange A f d ((affineTraceLineLeft A (affineTraceTower S d)).obj M) ≫
      (affineTraceLeft A S' d).map (affineTraceLineExchange A (affineTraceMap f d) M)

/-- The inverse-image comparison around the standard affine-chart square.
Source: blueprint sk-prop-an, Step 5(b) (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceOpenPullbackSquare (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (f : S' ⟶ S) :
    ordinaryFinitePullback A (ProjectiveLine.affineChart S) ⋙
        ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f) ≅
      ordinaryFinitePullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) f) ⋙
        ordinaryFinitePullback A (ProjectiveLine.affineChart S') :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace.map PUnit.{u + 1} f) (ProjectiveLine.affineChart S)).symm ≪≫
  eqToIso (congrArg (ordinaryFinitePullback A) (affineTraceChart_isPullback f).w) ≪≫
  leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (ProjectiveLine.affineChart S')
    (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)

/-- Canonical pullback of the one-coordinate right functor, with the normalized
roots-of-unity Tate comparison. Source: blueprint sk-prop-an, Step 5(b)
(blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceLineRightBaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f)).obj
        ((affineTraceLineRight A N hA S).obj K) ≅
      (affineTraceLineRight A N hA S').obj ((ordinaryFinitePullback A f).obj K) :=
  (affineTraceOpenPullbackSquare A f).app ((ordinaryFiniteP1Right A N hA S).obj K) ≪≫
    (ordinaryFinitePullback A (ProjectiveLine.affineChart S')).mapIso
      (ordinaryFiniteP1RightBaseChange A N hA t f hP K)

/-- One pasting step for the canonical right-functor base-change comparison.
The last argument is the preceding coordinate comparison; no map is chosen here.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceRightBaseChangeStep (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : DerivedCategoryModule A S)
    (e : (ordinaryFinitePullback A (affineTraceMap f d)).obj
        ((affineTraceRight A N hA S d).obj K) ≅
      (affineTraceRight A N hA S' d).obj ((ordinaryFinitePullback A f).obj K)) :
    (ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} (affineTraceMap f d))).obj
        ((affineTraceLineRight A N hA (affineTraceTower S d)).obj
          ((affineTraceRight A N hA S d).obj K)) ≅
      (affineTraceLineRight A N hA (affineTraceTower S' d)).obj
        ((affineTraceRight A N hA S' d).obj ((ordinaryFinitePullback A f).obj K)) :=
  affineTraceLineRightBaseChange A N hA t (affineTraceMap f d)
    (affineTraceProjectiveInvertible N (affineTraceTower S d)
      (affineTraceInvertible N S hS d)) ((affineTraceRight A N hA S d).obj K) ≪≫
    (affineTraceLineRight A N hA (affineTraceTower S' d)).mapIso e

/-- The canonical right-functor base-change comparison, pasted coordinatewise.
Source: blueprint sk-prop-an, Step 6 (blueprint: lem-amb-affine-space-top-trace). -/
def affineTraceRightBaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A (affineTraceMap f d)).obj
        ((affineTraceRight A N hA S d).obj K) ≅
      (affineTraceRight A N hA S' d).obj ((ordinaryFinitePullback A f).obj K) :=
  Nat.rec (motive := fun e ↦
    (ordinaryFinitePullback A (affineTraceMap f e)).obj
        ((affineTraceRight A N hA S e).obj K) ≅
      (affineTraceRight A N hA S' e).obj ((ordinaryFinitePullback A f).obj K))
    (Iso.refl ((ordinaryFinitePullback A f).obj K))
    (fun e r ↦ affineTraceRightBaseChangeStep A N hA t f hS e K r) d

/-- The affine-space trace is the actual composite counit, is invertible, and obeys
arbitrary Noetherian base change. The exchange is the pasted compact-support exchange;
the right-object comparison is the normalized Tate pullback comparison above.
Source: blueprint sk-prop-an, Steps 5(b), 6, detailed affine-space top trace lemma
(blueprint: lem-amb-affine-space-top-trace).

Proof, following the node's nine steps:
1. Use the two polynomial charts to compactify each line projection by P¹, and every
   coordinate composite by Pᵈ. These maps are separated and finite type; the standard
   opens are quasi-compact, their sources Noetherian, and N stays invertible.
2. Apply the open-closed triangle to A_P(1)[2] and push it along q. Its third vertex is
   A_S(1)[2], since the infinity section is finite, q i is the identity, and finite direct
   image is exact. Use the canonical direct-image composition comparison.
3. In the normalized decomposition b_q, restriction to infinity is (1,0). Its first
   component is the adjunction unit. Its second is zero because the Kummer boundary
   of O(1) restricts to the boundary of the trivial bundle. The normalized trace is (0,1).
4. The long exact cohomology sequence identifies the open vertex with the second
   summand. Thus the actual restricted trace induces an isomorphism in every degree;
   the unbounded cohomology criterion makes it invertible.
5. The composite-adjunction counit is q_* of the open counit followed by the projective
   counit. At A_S this is exactly the restricted trace of step 4.
6. For M=A_S(e)[2e], the open tensor comparison is invertible on geometric stalks, where
   it is identity inside the open and 0→0 outside. Flatness of the Tate line and exactness
   of open extension descend it termwise. The open counit square follows by transposing
   both maps to the identity. Proper projection naturality then identifies the composite
   counit with 1_M tensor the trace. All interchanged shifts are even, so no sign occurs.
7. Induct along the literal coordinate adjunctions, starting with the identity at d=0.
   The inner counit is invertible by step 6, and the previous counit by induction.
   The intermediate objects are shifted Tate lines, hence bounded below. Use the coherent
   comparison and its restriction compatibility to identify this with Rp_d! A(d)[2d].
8. For a changed base, the inverse open exchange is the mate of the open unit; the two
   open counit maps therefore transpose to the same identity. Paste this equality with
   the normalized projective-line counit square. Tate comparisons are the canonical
   roots-of-unity comparisons, not an arbitrary orientation.
9. Induct through the tower. Naturality and horizontal/vertical pasting identify its
   exchange with the compactification-independent compact-support exchange. Apply the
   inner counit equality, then the preceding trace equality. This gives exactly the
   displayed equality of actual morphisms, including identity and dimension-zero cases.
-/
theorem exists_affineSpaceTopTrace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∃ (t : OrdinaryFiniteTwistTransport A N hA)
      (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
        OrdinaryFiniteP1Datum A N hA t T hT),
      OrdinaryFiniteP1BaseChange A N hA t D ∧
      ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ),
        Nonempty (affineTraceRight A N hA S d ≅
          ordinaryFinitePullback A (affineTraceProjection S d) ⋙
            derivedTensorRight (ModuleCat.{u + 1} A) (affineTraceTower S d)
              ((_root_.DerivedCategory.singleFunctor _ 0).obj
                (Scheme.finiteEtaleTateSheaf A N (affineTraceTower S d) hA (d : ℤ))) ⋙
            shiftFunctor _ (2 * (d : ℤ))) ∧
        _root_.DerivedCategory.TStructure.t.plus
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ∧
        IsIso (affineTraceCounit A N hA t D S hS d) ∧
        ∀ (S' : Scheme.{u}) [IsNoetherian S'] (g : S' ⟶ S),
          affineTraceExchange A g d
              ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
            (affineTraceLeft A S' d).map
              ((affineTraceRightBaseChange A N hA t g hS d
                (ordinaryFiniteUnit A S)).hom ≫
                (affineTraceRight A N hA S' d).map (ordinaryFiniteUnitPullback A g).hom) ≫
            affineTraceCounit A N hA t D S' (affineTracePullbackInvertible N g hS) d =
          (ordinaryFinitePullback A g).map (affineTraceCounit A N hA t D S hS d) ≫
            (ordinaryFiniteUnitPullback A g).hom := by
  sorry

end AlgebraicGeometry.Etale
