/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Shifts and quantitative Tor bounds on the pro-etale site

Source: Stacks Project, Cohomology on Sites, Tags 06YU and 08FZ;
Homology, Tags 011G and 011H (blueprint: lem-weil-proetale-tor-interval-shift).
The coefficient-sized small model is equivalent to the original small pro-etale site.
All tensor tests use the published K-flat derived tensor and ordinary module sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace AlgebraicGeometry.Scheme

/-- Restrict the published derived tensor to module sheaves in degree zero in its
second argument. This is composition of existing functors, with no new resolutions.
Source: Stacks Tag 06YU (blueprint: lem-weil-proetale-tor-interval-shift). -/
def coefficientProEtaleTorTensorTest (Y : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    (ConstantCompletion.D (ConstantCompletion.constant
      (coefficientProEtaleModelTopology.{u, v} Y) A) ×
    ConstantCompletion.Mod (ConstantCompletion.constant
      (coefficientProEtaleModelTopology.{u, v} Y) A)) ⥤
    ConstantCompletion.D (ConstantCompletion.constant
      (coefficientProEtaleModelTopology.{u, v} Y) A) :=
  let R := ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} Y) A
  letI : HasSheafify (coefficientProEtaleModelTopology.{u, v} Y)
      AddCommGrpCat.{max v (u + 1)} := coefficientModelAdditiveSheafify Y
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  (𝟭 (ConstantCompletion.D R)).prod
    ((HomologicalComplex.single (ConstantCompletion.Mod R) (.up ℤ) 0) ⋙
      ConstantCompletion.Q R) ⋙
    SheafOfModules.siteDerivedTensorIndependentCoefficients.{max v (u + 1),
      max v (u + 1), max v (u + 1), max v (u + 1) + 1}
      (coefficientProEtaleModelTopology.{u, v} Y) R

/-- Natural tensor and cohomology shift comparisons, the exact interval translation,
isomorphism invariance, and the zero test for arbitrary commutative coefficients.
The natural isomorphisms are on the product of the derived category and the entire
module-sheaf category, so they include naturality in both K and N.

Source: Stacks Tags 06YU and 08FZ, and Homology Tags 011G and 011H
(blueprint: lem-weil-proetale-tor-interval-shift).

Proof (the node's five steps):
1. Apply lem-weil-pbc-kflat-fixed-tensor-triangulated to R = A_Y on the coefficient-sized
   small model. Its CommShift₂Int structure gives the first-variable shift isomorphisms
   and their naturality in the second variable. Form the natural isomorphism on
   D(R) × D(R), using the fixed-variable shift naturality square and commShift_flip_map
   (the tensor is that of lem-weil-pbc-site-derived-tensor-descent). Restrict the second
   variable along N ↦ Q(N[0]). This is natural in both K and N.
2. Whisker the tensor shift isomorphism by H^i (def-weil-derived-cohomology-sheaves),
   reassociate, and whisker the natural cohomology shift isomorphism
   H^i(T[m]) ≅ H^(i+m)(T) of lem-sp-derived-cohomology-shift; m+i = i+m.
3. By lem-pe-coefficient-tor-flat-model represent an object of amplitude [a,b] by a
   flat complex P zero below a and above b. Then P[m] has flat terms and is zero below
   a-m and above b-m, and the localization shift isomorphism identifies Q(P[m]) with
   K[m]; the criterion gives the forward implication. For the converse apply the same
   construction with -m and the isomorphism K[m][-m] ≅ K.
4. Unfold def-weil-proetale-tor-amplitude. For e : K ≅ L, a K-flat representative
   QP ≅ L gives QP ≅ K by composing with e⁻¹, and conversely with e. The tensor-test
   vanishing assertion is the same in both cases.
5. By lem-pe-coefficient-tor-flat-model choose a flat-term K-flat representative P of
   N[0], and translate its monoidal flatness into site flatness through the canonical
   tensor comparison (lem-weil-pbc-independent-sheaf-tensor-colimits). The fixed tensor
   - ⊗ QP is triangulated, so it preserves zero objects. Transport this along the
   isomorphism induced by QP ≅ N[0], which gives 0 ⊗ N ≅ 0. The zero complex is flat and
   concentrated in [0,0], and Q preserves zero, so the flat-model criterion gives
   amplitude [0,0] for 0.
-/
theorem coefficientProEtaleTor_interval_shift (Y : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    (∀ m : ℤ, Nonempty
      (((shiftFunctor (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) m).prod
          (𝟭 (ConstantCompletion.Mod (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)))) ⋙
          coefficientProEtaleTorTensorTest Y A ≅
        coefficientProEtaleTorTensorTest Y A ⋙
          shiftFunctor (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) m)) ∧
    (∀ i m : ℤ, Nonempty
      (((shiftFunctor (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) m).prod
          (𝟭 (ConstantCompletion.Mod (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)))) ⋙
          coefficientProEtaleTorTensorTest Y A ⋙
          coefficientModelCohomology (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A) i ≅
        coefficientProEtaleTorTensorTest Y A ⋙
          coefficientModelCohomology (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A) (i + m))) ∧
    (∀ (K : ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) (a b m : ℤ), a ≤ b →
      (HasCoefficientProEtaleTorAmplitude Y A K a b ↔
        HasCoefficientProEtaleTorAmplitude Y A (K⟦m⟧) (a - m) (b - m))) ∧
    (∀ (K L : ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) (_e : K ≅ L)
      (a b : ℤ), a ≤ b →
      (HasCoefficientProEtaleTorAmplitude Y A K a b ↔
        HasCoefficientProEtaleTorAmplitude Y A L a b)) ∧
    (∀ N : ConstantCompletion.Mod (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A),
      Nonempty (@Functor.obj _
        (CategoryTheory.prod'.{max v (u + 1) + 1, max v (u + 1)}
          (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A))
          (ConstantCompletion.Mod (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)))
        (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) inferInstance
        (coefficientProEtaleTorTensorTest.{u, v} Y A)
        ((0 : (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A))), N) ≅
        (0 : (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A))))) ∧
    HasCoefficientProEtaleTorAmplitude Y A 0 0 0 := by
  sorry

end AlgebraicGeometry.Scheme
