/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.ScalarProjectionTransformation
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.ModuleDerivedFunctorCompositorShifts
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.ModCondensedCachedInstances
import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
import WeilConjectures.AlgebraicGeometry.SectionDerivedTensorNormalization
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.AlgebraicGeometry.KFlatDerivedAdjunctionTransportShifts
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.AlgebraicGeometry.RingedProjectionFirstShift
import WeilConjectures.AlgebraicGeometry.ProjectionMateExact
import WeilConjectures.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
public import WeilConjectures.AlgebraicGeometry.RationalBivariateShiftSecond
public import WeilConjectures.AlgebraicGeometry.RationalBivariateShiftFirst
import WeilConjectures.AlgebraicGeometry.RationalBivariateBraiding

/-! # The canonical projection transformation in both variables

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.proof.md,
paragraph (3); Stacks Project, Tags 07A4, 0B56, 0A8D and 014A
(blueprint: lem-sfb-rational-bivariate-devissage).

The two helper definitions only curry the existing adjunction-defined projection.
The theorem fixes their components to the recorded projection map, identifies the
scalar-first braiding conjugate, and uses the existing signed tensor and derived
pushpull shifts throughout.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem triangle_morphism_of_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]
    (B : F ⟶ G) [NatTrans.CommShift B ℤ] (T : Triangle C) :
    ∃ b : F.mapTriangle.obj T ⟶ G.mapTriangle.obj T,
      b.hom₁ = B.app T.obj₁ ∧ b.hom₂ = B.app T.obj₂ ∧ b.hom₃ = B.app T.obj₃ := by
  refine ⟨{ hom₁ := B.app T.obj₁, hom₂ := B.app T.obj₂, hom₃ := B.app T.obj₃
            comm₁ := B.naturality T.mor₁
            comm₂ := B.naturality T.mor₂
            comm₃ := ?_ }, rfl, rfl, rfl⟩
  change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
    (shiftFunctor D (1 : ℤ)).map (B.app T.obj₁) =
      B.app T.obj₃ ≫ G.map T.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁
  rw [Category.assoc, NatTrans.shift_app_comm B (1 : ℤ),
    ← Category.assoc, B.naturality T.mor₃, Category.assoc]

set_option maxHeartbeats 5000000 in
-- The derived-functor transport and triangle proof requires the larger budget.
set_option linter.style.haveILetI false in
/-- The actual counit projection agrees with the scalar-first projection after Koszul
braiding and is an exact transformation separately in each variable, with both fixed
signed integer-shift structures. Its isomorphism loci are triangulated and invariant
under isomorphism.

Source: latest blueprint, rational proper-base-change proof, paragraph (3);
Stacks Project, Tags 07A4, 0B56, 0A8D and 014A
(blueprint: lem-sfb-rational-bivariate-devissage).

Proof, following the six DAG steps:
1. Apply lem-pe-internal-section-tensor-comparison to the fixed section equivalences.
They are exact and preserve the signed total tensors, symmetry, acyclicity and K-flatness.
Use lem-pd-section-derived-pushpull-normalization and
lem-pd-section-derived-tensor-normalization to identify the specified derived functors,
resolution comparisons, units, counits and tensor comparison with the ringed ones.
The pro-etale sites satisfy the required coefficient-universe size convention.
2. These equivalences preserve reindexing, the differential sign (-1)^n, the unsigned
first tensor shift and the second shift (-1)^(np). The derived pushpull comparison uses
the same resolution maps. lem-sfb-kflat-derived-adjunction-transport-shifts identifies
the adjunction-compatible shift with the fixed K-injective shift. The transpose of pi
is therefore exactly (epsilon tensor identity) delta, with delta the comparison of
new-proetale-derived-module-pullback-monoidal, rather than an arbitrary tensorator.
3. By lem-sfb-ringed-derived-monoidal-comparisons, delta preserves symmetry. Transpose
the scalar-first map conjugated by the two braidings. Braiding naturality at epsilon
and symmetry identify its transpose with (epsilon tensor identity) delta. Injectivity
of the adjunction Hom bijection gives the displayed equality with pi.
4. For fixed K apply lem-weil-pbc-ringed-projection-mate-exact; for fixed M apply
lem-sfb-ringed-projection-first-shift. Steps 1--2 transport exactness and their shift
squares to the actual internal functors. Iterate the coherent [1] comparison for
positive integers, use its identity at zero, and cancel its inverse for negative ones.
This gives the two explicit equations for every integer n with the fixed signed shifts.
5. Naturality gives the first two triangle squares. For the connecting arrow w, use
pi(L)[1] s_F F(w) = s_H pi(L[1]) F(w) = s_H H(w) pi(L3).
These are exactly the third arrows of the two distinguished image triangles, giving
the asserted triangle morphisms, including the connecting square.
6. Additive exact functors send zero to zero. Naturality conjugates the map along
isomorphisms; the shift square conjugates it along shifts in both directions. For
a distinguished triangle use lem-sf-triangle-morphism-iso: two invertible components
force the third. Thus each locus is closed under zero, isomorphisms, shifts and cones.
No properness, boundedness, flatness of coefficients, or generator invertibility is used. -/
theorem rational_bivariate_devissage
    {k : Type u} [Field k] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {S T : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (p : S ⟶ T) :
    (∀ (K : DerivedCategory (ModuleObjectRingedComparison.Internal Λ S.left))
      (M : DerivedCategory (ModuleObjectRingedComparison.Internal Λ T.left)),
      (rationalProjectionSecond Λ p.left K).app M = moduleObjectProjectionMap Λ p.left K M ∧
      (rationalProjectionFirst Λ p.left M).app K = moduleObjectProjectionMap Λ p.left K M ∧
      moduleObjectProjectionMap Λ p.left K M =
        (@BraidedCategory.braiding _ _ _
          (ModuleObjectRingedComparison.internalBraiding Λ T.left)
          ((moduleObjectDerivedPushforward Λ p.left).obj K) M).hom ≫
          (scalarFirstProjection Λ p.left K).app M ≫
          (moduleObjectDerivedPushforward Λ p.left).map
            (@BraidedCategory.braiding _ _ _
              (ModuleObjectRingedComparison.internalBraiding Λ S.left)
              ((moduleObjectDerivedPullback Λ p.left).obj M) K).hom) ∧
    (∀ K : DerivedCategory (ModuleObjectRingedComparison.Internal Λ S.left),
      (tensorLeft ((moduleObjectDerivedPushforward Λ p.left).obj K)).IsTriangulated ∧
      (moduleObjectDerivedPullback Λ p.left ⋙ tensorLeft K ⋙
        moduleObjectDerivedPushforward Λ p.left).IsTriangulated ∧
      NatTrans.CommShift (rationalProjectionSecond Λ p.left K) ℤ ∧
      (∀ (n : ℤ) (M : DerivedCategory (ModuleObjectRingedComparison.Internal Λ T.left)),
        (rationalProjectionSecond Λ p.left K).app (M⟦n⟧) ≫
            ((moduleObjectDerivedPullback Λ p.left ⋙ tensorLeft K ⋙
              moduleObjectDerivedPushforward Λ p.left).commShiftIso n).hom.app M =
          ((tensorLeft ((moduleObjectDerivedPushforward Λ p.left).obj K)).commShiftIso n).hom.app
              M ≫
            (shiftFunctor _ n).map ((rationalProjectionSecond Λ p.left K).app M)) ∧
      (∀ A : Triangle (DerivedCategory (ModuleObjectRingedComparison.Internal Λ T.left)),
        A ∈ distTriang _ →
        ∃ a : (tensorLeft ((moduleObjectDerivedPushforward Λ p.left).obj K)).mapTriangle.obj A ⟶
            (moduleObjectDerivedPullback Λ p.left ⋙ tensorLeft K ⋙
              moduleObjectDerivedPushforward Λ p.left).mapTriangle.obj A,
          a.hom₁ = (rationalProjectionSecond Λ p.left K).app A.obj₁ ∧
          a.hom₂ = (rationalProjectionSecond Λ p.left K).app A.obj₂ ∧
          a.hom₃ = (rationalProjectionSecond Λ p.left K).app A.obj₃) ∧
      (rationalProjectionSecond Λ p.left K).isoLocus.IsTriangulated ∧
      (rationalProjectionSecond Λ p.left K).isoLocus.IsClosedUnderIsomorphisms) ∧
    (∀ M : DerivedCategory (ModuleObjectRingedComparison.Internal Λ T.left),
      (moduleObjectDerivedPushforward Λ p.left ⋙ tensorRight M).IsTriangulated ∧
      (tensorRight ((moduleObjectDerivedPullback Λ p.left).obj M) ⋙
        moduleObjectDerivedPushforward Λ p.left).IsTriangulated ∧
      NatTrans.CommShift (rationalProjectionFirst Λ p.left M) ℤ ∧
      (∀ (n : ℤ) (K : DerivedCategory (ModuleObjectRingedComparison.Internal Λ S.left)),
        (rationalProjectionFirst Λ p.left M).app (K⟦n⟧) ≫
            ((tensorRight ((moduleObjectDerivedPullback Λ p.left).obj M) ⋙
              moduleObjectDerivedPushforward Λ p.left).commShiftIso n).hom.app K =
          ((moduleObjectDerivedPushforward Λ p.left ⋙ tensorRight M).commShiftIso n).hom.app K ≫
            (shiftFunctor _ n).map ((rationalProjectionFirst Λ p.left M).app K)) ∧
      (∀ A : Triangle (DerivedCategory (ModuleObjectRingedComparison.Internal Λ S.left)),
        A ∈ distTriang _ →
        ∃ a : (moduleObjectDerivedPushforward Λ p.left ⋙ tensorRight M).mapTriangle.obj A ⟶
            (tensorRight ((moduleObjectDerivedPullback Λ p.left).obj M) ⋙
              moduleObjectDerivedPushforward Λ p.left).mapTriangle.obj A,
          a.hom₁ = (rationalProjectionFirst Λ p.left M).app A.obj₁ ∧
          a.hom₂ = (rationalProjectionFirst Λ p.left M).app A.obj₂ ∧
          a.hom₃ = (rationalProjectionFirst Λ p.left M).app A.obj₃) ∧
      (rationalProjectionFirst Λ p.left M).isoLocus.IsTriangulated ∧
      (rationalProjectionFirst Λ p.left M).isoLocus.IsClosedUnderIsomorphisms) := by
  classical
  obtain ⟨hpb, hpf, _, _⟩ :=
    module_derived_functors_exact_and_comparison_shifts Λ p.left
  haveI := hpb
  haveI := hpf
  constructor
  · intro K M
    refine ⟨?_, ?_, ?_⟩
    · rfl
    · rfl
    · exact rational_bivariate_braiding Λ p.left K M
  · constructor
    · intro K
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · infer_instance
      · infer_instance
      · exact (rational_bivariate_second_shift Λ p.left K).1
      · intro n M
        exact (rational_bivariate_second_shift Λ p.left K).2 n M
      · intro A hA
        let τ := rationalProjectionSecond Λ p.left K
        set_option maxRecDepth 10000 in
        have hτ := rational_bivariate_second_shift Λ p.left K
        haveI : NatTrans.CommShift τ ℤ := hτ.1
        set_option maxRecDepth 10000 in
          exact triangle_morphism_of_shift _ _ τ A
      · let τ := rationalProjectionSecond Λ p.left K
        set_option maxRecDepth 10000 in
        have hτ := rational_bivariate_second_shift Λ p.left K
        haveI : NatTrans.CommShift τ ℤ := hτ.1
        exact ⟨inferInstance, inferInstance⟩
    · intro M
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · infer_instance
      · infer_instance
      · exact (rational_bivariate_first_shift Λ p.left M).1
      · intro n K
        exact (rational_bivariate_first_shift Λ p.left M).2 n K
      · intro A hA
        let τ := rationalProjectionFirst Λ p.left M
        set_option maxRecDepth 10000 in
        have hτ := rational_bivariate_first_shift Λ p.left M
        haveI : NatTrans.CommShift τ ℤ := hτ.1
        set_option maxRecDepth 10000 in
          exact triangle_morphism_of_shift _ _ τ A
      · let τ := rationalProjectionFirst Λ p.left M
        set_option maxRecDepth 10000 in
        have hτ := rational_bivariate_first_shift Λ p.left M
        haveI : NatTrans.CommShift τ ℤ := hτ.1
        exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.ProEtale.CondensedRing
