/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.CategoryTheory.StrictProjectionLimitData
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import WeilConjectures.CategoryTheory.Abelian.SplitSESBoundaryComparison
import Sheaf.CategoryTheory.FiniteFreeScalarCoordinates
import Sheaf.CategoryTheory.DiagramSiteRealization
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Paper.RestrictionDerivedProducts
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars

/-!
# Finite-free scalar extension and strict derived towers

Source: Stacks Project, algebraization.tex, Tag 0A0E (application); sites-cohomology.tex,
Tag 0941 (resolved Roos triangle); derived.tex, Tags 070I, 08BJ, 0BK6.
(blueprint: lem-weil-pbc-finite-free-strict-tower-transport).

The helpers specify canonical maps and their cochain factorizations. Positive
levels are indexed by `n : ℕ` meaning level `n + 1`. All complexes are unbounded.
The existing `StrictProjectionLimitData` packages the recorded total right derived limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v r w uA vA uB vB
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules

namespace CategoryTheory

/-- The ordinary inverse-limit functor on cochain complexes of strict towers.
Source: Stacks 0941 (blueprint: lem-weil-pbc-finite-free-strict-tower-transport). -/
abbrev strictTowerLimitComplex (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] :=
  (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The canonical inclusion of the ordinary strict limit into the product of evaluations.
Source: Stacks 0941 (blueprint: lem-weil-pbc-finite-free-strict-tower-transport). -/
def strictTowerLimitInclusion {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (strictTowerLimitComplex A).obj I ⟶ ∏ᶜ (fun n : ℕ ↦ I.asFunctor.obj (op n)) :=
  Pi.lift (fun n : ℕ ↦
    (NatTrans.mapHomologicalComplex (lim.π (op n)) (ComplexShape.up ℤ)).app I)

/-- Product comparison from a cochain tower to its derived evaluations, including the
specified evaluation factorization of the strict-limit interface.
Source: Stacks 0941 (blueprint: lem-weil-pbc-finite-free-strict-tower-transport). -/
def strictTowerResolvedProduct {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    (L : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q)
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    DerivedCategory.Q.obj (∏ᶜ (fun n : ℕ ↦ I.asFunctor.obj (op n))) ⟶
      ∏ᶜ (fun n : ℕ ↦ (L.ev.obj (DerivedCategory.Q.obj I)).obj (op n)) :=
  piComparison DerivedCategory.Q (fun n : ℕ ↦ I.asFunctor.obj (op n)) ≫
    Limits.Pi.map (fun n : ℕ ↦ (L.evaluation.inv.app I).app (op n))

/-- Normalization of the whole Roos triangle on injective-term K-injective towers.
The last equation fixes the connecting arrow as the actual short-exact-sequence boundary.
It does not choose a completion of an abstract triangle.
Source: Stacks 0941 (blueprint: lem-weil-pbc-finite-free-strict-tower-transport). -/
def strictTowerRoosNormalized
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    (L : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q) : Prop :=
  (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
    L.eta.app X ≫ L.p (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (strictTowerLimitInclusion X) ≫ strictTowerResolvedProduct L X) ∧
  ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective →
    (∀ k : ℤ, Injective (I.X k)) →
    ∀ (h : strictTowerLimitInclusion I ≫
        towerTransitionEndomorphism
          (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op) = 0)
      (hs : (ShortComplex.mk (strictTowerLimitInclusion I)
        (towerTransitionEndomorphism
          (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op)) h).ShortExact),
      strictTowerResolvedProduct L I ≫ L.delta (DerivedCategory.Q.obj I) =
        DerivedCategory.triangleOfSESδ hs ≫ (L.eta.app I)⟦(1 : ℤ)⟧'

/-- Finite-free transport data with the normalized ordinary and derived comparisons,
all three Roos squares and the strict augmentation formula. `augmentation` quantifies
all maps to the ordinary limit, equivalently all compatible strict augmented towers.
Source: Stacks 0A0E, 0941 (blueprint: lem-weil-pbc-finite-free-strict-tower-transport). -/
structure FiniteFreeStrictTowerTransport
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    [HasCountableProducts (DerivedCategory.{w} B)]
    (F : A ⥤ B) [F.Additive]
    (G : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B) [G.CommShift ℤ]
    (T : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ B))
    (factors : DerivedCategory.Q ⋙ G ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (towerFactors : DerivedCategory.Q ⋙ T ≅
      (projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) where
  /-- The source total derived inverse limit with its functorial Roos triangles. -/
  source : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q
  /-- The target total derived inverse limit with its functorial Roos triangles. -/
  target : StrictProjectionLimitData B DerivedCategory.Q DerivedCategory.Q
  /-- The source total derived inverse limit is exact with its cochain shift. -/
  source_exact : ∃ (_ : source.L.CommShift ℤ), source.L.IsTriangulated
  /-- The target total derived inverse limit is exact with its cochain shift. -/
  target_exact : ∃ (_ : target.L.CommShift ℤ), target.L.IsTriangulated
  /-- Pin the source connecting arrow to the resolved short exact sequence. -/
  source_normalized : strictTowerRoosNormalized source
  /-- Pin the target connecting arrow to the resolved short exact sequence. -/
  target_normalized : strictTowerRoosNormalized target
  /-- The ordinary limit/tensor comparison. -/
  ordinary : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ F ≅
    projectionPost (I := ℕᵒᵖ) F ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B)
  /-- Its definition by ordinary limit projections. -/
  ordinary_normalized : ∀ X : ℕᵒᵖ ⥤ A, ordinary.hom.app X = limit.post X F
  /-- Canonical projection comparison for every countable family in D(A). -/
  products : ∀ M : ℕ → DerivedCategory.{w} A, IsIso (piComparison G M)
  /-- Exact termwise tensor commutes with derived evaluation. -/
  evaluation : T ⋙ target.ev ≅
    source.ev ⋙ projectionPost (I := ℕᵒᵖ) G
  /-- This is the evaluation comparison induced on actual cochain representatives. -/
  evaluation_normalized : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ),
    (target.ev.map (towerFactors.hom.app X)).app n ≫
        (target.evaluation.hom.app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X)).app n ≫
        factors.inv.app (X.asFunctor.obj n) =
      (evaluation.hom.app (DerivedCategory.Q.obj X)).app n ≫
        G.map ((source.evaluation.hom.app X).app n)
  /-- The natural derived-limit comparison lambda. -/
  comparison : source.L ⋙ G ≅
    T ⋙ target.L
  /-- The defining total-derived comparison equation, for every complex. -/
  comparison_normalized : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    G.map (source.eta.app X) ≫
        comparison.hom.app (DerivedCategory.Q.obj X) =
      factors.hom.app ((strictTowerLimitComplex A).obj X) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app X) ≫
        target.eta.app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X) ≫
        target.L.map (towerFactors.inv.app X)
  /-- The first square of the Roos triangles, with the canonical product comparison. -/
  roos_first : ∀ X : DerivedCategory.{w} (ℕᵒᵖ ⥤ A),
    G.map (source.p X) ≫
        piComparison G (fun n : ℕ ↦ (source.ev.obj X).obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ (evaluation.inv.app X).app (op n)) =
      comparison.hom.app X ≫
        target.p (T.obj X)
  /-- The middle square: the projection comparison intertwines one minus shift. -/
  roos_middle : ∀ X : DerivedCategory.{w} (ℕᵒᵖ ⥤ A),
    G.map (towerTransitionEndomorphism
        (fun n : ℕ ↦ (source.ev.obj X).map (homOfLE (Nat.le_succ n)).op)) ≫
        piComparison G (fun n : ℕ ↦ (source.ev.obj X).obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ (evaluation.inv.app X).app (op n)) =
      piComparison G (fun n : ℕ ↦ (source.ev.obj X).obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ (evaluation.inv.app X).app (op n)) ≫
        towerTransitionEndomorphism (fun n : ℕ ↦
          (target.ev.obj (T.obj X)).map
            (homOfLE (Nat.le_succ n)).op)
  /-- The last square, including the cochain-normalized shift comparison. -/
  roos_last : ∀ X : DerivedCategory.{w} (ℕᵒᵖ ⥤ A),
    G.map (source.delta X) ≫
        (G.commShiftIso (1 : ℤ)).hom.app (source.L.obj X) ≫
        (comparison.hom.app X)⟦(1 : ℤ)⟧' =
      piComparison G (fun n : ℕ ↦ (source.ev.obj X).obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ (evaluation.inv.app X).app (op n)) ≫
        target.delta (T.obj X)
  /-- A strict augmentation is its ordinary-limit lift z. The equation is lambda C(z)=z'. -/
  augmentation : ∀ (M : CochainComplex A ℤ) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
      (z : M ⟶ (strictTowerLimitComplex A).obj X),
    G.map (DerivedCategory.Q.map z ≫ source.eta.app X) ≫
        comparison.hom.app (DerivedCategory.Q.obj X) =
      factors.hom.app M ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map z ≫
          (NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app X) ≫
        target.eta.app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X) ≫
        target.L.map (towerFactors.inv.app X)
  /-- Naturality for a map (h,v) of entire augmented towers, including the source complex. -/
  augmented_naturality : ∀ (M N : CochainComplex A ℤ)
      (X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
      (z : M ⟶ (strictTowerLimitComplex A).obj X)
      (t : N ⟶ (strictTowerLimitComplex A).obj Y)
      (h : M ⟶ N) (v : X ⟶ Y),
    z ≫ (strictTowerLimitComplex A).map v = h ≫ t →
      G.map (DerivedCategory.Q.map z ≫ source.eta.app X) ≫
          comparison.hom.app (DerivedCategory.Q.obj X) ≫
          target.L.map (T.map
            (DerivedCategory.Q.map v)) =
        G.map (DerivedCategory.Q.map h) ≫
          G.map (DerivedCategory.Q.map t ≫ source.eta.app Y) ≫
          comparison.hom.app (DerivedCategory.Q.obj Y)

end CategoryTheory

namespace SheafOfModules

/-- Finite-free scalar extension preserves arbitrary unbounded derived countable products
and the complete functorial Roos triangles of strict towers, including strict augmentations.
The hypothesis is only existence of a finite basis, not the choice of one. The counit equation
identifies the exact cochain model with the recorded derived tensor functor.

Source: Stacks 0A0E, 0941, 070I, 08BJ, 0BK6
(blueprint: lem-weil-pbc-finite-free-strict-tower-transport).

Proof (the eleven DAG steps):
1. Restriction is exact, conservative and limit preserving
(lem-weil-pbc-restriction-derived-products). The internal/sectionwise adjunction bridge
(lem-sfb-internal-section-scalar-adjunction, det-def-sfb-ring-object-sheaf,
sk-def-sfb-change-of-scalars) transports finite scalar coordinates
(lem-sfb-finite-free-scalar-coordinates) to UF(M)=M^d. Hence F is exact, also on towers
(lem-weil-tower-category-levelwise-abelian). Exact-functor-derived-factorization identifies
its localization with the given derived-change-of-rings universal pair.
2. Define product and ordinary-limit comparisons by projections. Under U and the coordinates
they interchange a finite tuple with a compatible family. They are invertible and basis free.
3. Resolve modules and towers functorially by injective-term K-injectives
(prop-pur-kinjective-resolutions-exist, lem-weil-pbc-diagram-site-realization). Restriction
preserves K-injectives by the exact left adjoint
(lem-weil-pbc-right-adjoint-preserves-kinjective); UFI=I^d is K-injective, including d=0
(lem-pc-ringed-space-product-kinjective). No claim that FI is K-injective over S is needed.
4. Resolve each FI_n to J_n. After U these are quasi-isomorphisms between K-injectives,
hence homotopy equivalences (lem-weil-pbc-kinjective-hom-derived). Their products remain
homotopy equivalences, proving invertibility of the canonical derived-product comparison.
5. For X to I and FI to J use F(lim I) to lim FI to lim J. This is the comparison induced
by the ordinary limit/tensor map and the right-derived unit, not a cone filler.
6. U applied to I^d to UJ is a homotopy equivalence. Additive inverse limit preserves it.
Conservativity detects the desired quasi-isomorphism. The K-injective Hom bijection makes
it independent of resolutions, and localization gives the natural isomorphism.
7. Injectivity of a tower splits each transition by extension across finite prefix towers.
For given (x_n), set y_0=0 and y_(n+1)=sigma_n(y_n-x_n); this splits 1-s degreewise.
8. The kernel is the ordinary limit. On injective-term resolutions the two products are
derived products (lem-weil-tower-evaluation-kinjective, lem-pc-ringed-space-product-kinjective).
The resulting short exact sequence is the functorial Roos triangle of
lem-weil-pbc-ringed-strict-tower-homotopy-limit, using lem-weil-pbc-complex-ses-triangle.
9. The limit comparison and product comparison give a morphism of these short exact
sequences. Its middle square commutes by projections and transition compatibility.
The degreewise split boundary formula (lem-sc-p1-split-ses-boundary-comparison) and the
cochain shift comparison of exact-functor-derived-factorization identify the boundary;
naturality of the SES triangle supplies the last Roos square.
10. Constant towers are exact left adjoint to inverse limit. The K-injective Hom bijection
identifies the derived adjunct of a strict augmentation with lim(qz). Naturality of the
ordinary comparison gives lambda C(z)=z' with the specified whole-tower data.
11. Functorial resolutions and the same projection equations give naturality in (h,v).
Only the proof chose coordinates: the specified comparisons are basis independent.
None of the steps assumes exactness of countable sheaf products or bounds on complexes. -/
theorem finiteFreeStrictTowerTransport
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {O S : Sheaf J CommRingCat.{r}} (a : O ⟶ S)
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, w, w} a)
    (hfree : ∃ d : ℕ, Nonempty
      (free (R := derivedChangeRingIndependentCoefficients J O) (ULift.{r} (Fin d)) ≅
        (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (unit (derivedChangeRingIndependentCoefficients J S)))) :
    ∃ (_ : PreservesFiniteLimits D.E) (_ : PreservesFiniteColimits D.E)
      (_ : PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) D.E))
      (_ : PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) D.E))
      (_ : HasCountableProducts (DerivedCategory.{w} (ringedSiteModules.{r}
        (derivedChangeRingIndependentCoefficients J O))))
      (_ : HasCountableProducts (DerivedCategory.{w} (ringedSiteModules.{r}
        (derivedChangeRingIndependentCoefficients J S))))
      (κ : D.T ≅ D.E.mapDerivedCategory),
      (∀ M, D.ε.app M = κ.hom.app (DerivedCategory.Q.obj M) ≫
        D.E.mapDerivedCategoryFactors.hom.app M) ∧
      (∀ M : ℕ → DerivedCategory.{w} (ringedSiteModules.{r}
        (derivedChangeRingIndependentCoefficients J O)), IsIso (piComparison D.T M)) ∧
      Nonempty (FiniteFreeStrictTowerTransport D.E D.E.mapDerivedCategory
        (projectionPost (I := ℕᵒᵖ) D.E).mapDerivedCategory
        D.E.mapDerivedCategoryFactors
        (projectionPost (I := ℕᵒᵖ) D.E).mapDerivedCategoryFactors) := by
  sorry

end SheafOfModules
