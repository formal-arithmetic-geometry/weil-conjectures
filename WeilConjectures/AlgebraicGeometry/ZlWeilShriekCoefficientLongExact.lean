/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.SfConstructibleHeart
public import WeilConjectures.AlgebraicGeometry.ConstructibleTruncations
public import WeilConjectures.AlgebraicGeometry.WeilMixedUpperBounds
public import WeilConjectures.AlgebraicGeometry.CommonStageWeilShriek
public import WeilConjectures.AlgebraicGeometry.FieldWeilShriekShiftData
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
import WeilConjectures.AlgebraicGeometry.ConstructiblePullbackTExact
import WeilConjectures.CategoryTheory.Triangulated.TStructure.HeartAbelianKernelSplitting
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.AlgebraicGeometry.FieldShriekLowerBound
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
import WeilConjectures.AlgebraicGeometry.WeilShriekShiftCompatibility
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # The Weil-equivariant coefficient sequence for compact support

Source: main-20261015 blueprint, lem-zl-morphism-open-closed-reduction.proof.md,
Part 3 (blueprint: lem-zl-weil-shriek-coefficient-long-exact).

The higher images use the actual common-stage functor and its induced Weil structure.
The boundary formula uses an underlying heart triangle and the uniquely normalized
truncation comparisons. No triangulation on fixed pairs is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hXsep : IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [hYsep : IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) [hfsep : IsSeparated f₀.left]
  [hfft : LocallyOfFiniteType f₀.left] [hfqc : QuasiCompact f₀.left]
  (c : Compactification f₀.left)

/-- R^r f_! on the constructible Weil heart is H^r of compact support of its
underlying degree-zero complex, retaining the prescribed Weil structures.
Source: blueprint Part 3 (blueprint: lem-zl-weil-shriek-coefficient-long-exact). -/
def zlCoefficientHigherShriek (r : ℤ) :
    sfCommonStageWeilSheaf D l hl X₀ Ω ⥤ sfCommonStageWeilSheaf D l hl Y₀ Ω :=
  ((sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω).inverseImage
      (sfCommonStageWeilForget D l hl X₀ Ω)).ι ⋙
    zlComplexShriek D l hl Ω f₀ c ⋙ sfWeilCohomology D l hl Ω Y₀ r

/-- The boundary is the cohomology of the image of the canonical heart triangle.
The two auxiliary isomorphisms are uniquely fixed by the truncation counit and unit.
Their shifted composite, followed by the prescribed shift-addition comparison,
identifies H^r(A[1]) with H^(r+1)(A); thus the equality fixes the boundary's sign.
Source: blueprint Part 3, BBD 1.3.3
(blueprint: lem-zl-weil-shriek-coefficient-long-exact). -/
def zlCoefficientBoundaryFormula
    (S : ShortComplex (sfCommonStageWeilSheaf D l hl X₀ Ω)) (r : ℤ)
    (δ : (zlCoefficientHigherShriek D l hl Ω f₀ c r).obj S.X₃ ⟶
      (zlCoefficientHigherShriek D l hl Ω f₀ c (r + 1)).obj S.X₁) : Prop :=
  ∃ (t : S.X₃.obj.carrier ⟶ S.X₁.obj.carrier⟦(1 : ℤ)⟧),
    Triangle.mk S.f.hom.hom.f S.g.hom.hom.f t ∈ distTriang _ ∧
    ∃ (a :
      ((sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl).truncLE r).obj
        (((zlCommonStageShriek D l hl Ω f₀ c).obj S.X₁.obj.carrier)⟦(1 : ℤ)⟧) ≅
      (((sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl).truncLE
        (r + 1)).obj ((zlCommonStageShriek D l hl Ω f₀ c).obj S.X₁.obj.carrier))⟦(1 : ℤ)⟧)
    (b :
      ((sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl).truncGE r).obj
        ((((sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl).truncLE
          (r + 1)).obj ((zlCommonStageShriek D l hl Ω f₀ c).obj S.X₁.obj.carrier))⟦(1 : ℤ)⟧) ≅
      (((sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl).truncGE
        (r + 1)).obj
          (((sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl).truncLE
            (r + 1)).obj ((zlCommonStageShriek D l hl Ω f₀ c).obj
              S.X₁.obj.carrier)))⟦(1 : ℤ)⟧),
      a.hom ≫ (((sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl).truncLEι
         (r + 1)).app
          ((zlCommonStageShriek D l hl Ω f₀ c).obj S.X₁.obj.carrier))⟦(1 : ℤ)⟧' =
        ((sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl).truncLEι
           r).app
            (((zlCommonStageShriek D l hl Ω f₀ c).obj S.X₁.obj.carrier)⟦(1 : ℤ)⟧) ∧
      ((sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl).truncGEπ
         r).app
          ((((sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl).truncLE
            (r + 1)).obj ((zlCommonStageShriek D l hl Ω f₀ c).obj
              S.X₁.obj.carrier))⟦(1 : ℤ)⟧) ≫ b.hom =
        (((sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl).truncGEπ
           (r + 1)).app
            (((sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl).truncLE
              (r + 1)).obj ((zlCommonStageShriek D l hl Ω f₀ c).obj
                S.X₁.obj.carrier)))⟦(1 : ℤ)⟧' ∧
      δ.hom.hom.f =
        (constructibleTruncationCohomology
          (sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl) r).map
          ((zlCommonStageShriek D l hl Ω f₀ c).map t ≫
            ((zlCommonStageShriek D l hl Ω f₀ c).commShiftIso (1 : ℤ)).hom.app
              S.X₁.obj.carrier) ≫
        (((sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl).truncGE
           r).map a.hom)⟦r⟧' ≫ b.hom⟦r⟧' ≫
        (shiftFunctorAdd' _ (1 : ℤ) r (r + 1) (Int.add_comm 1 r)).inv.app
          (((sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl).truncGE
            (r + 1)).obj
              (((sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl).truncLE
                 (r + 1)).obj
                  ((zlCommonStageShriek D l hl Ω f₀ c).obj S.X₁.obj.carrier)))

include hXsep hYsep hfsep hfft hfqc in
/-- Every short exact Weil sequence has the canonical natural long exact sequence
of compact-support higher images, exact at each of its three types of terms.

Source: main-20261015 blueprint, lem-zl-morphism-open-closed-reduction.proof.md,
Part 3 (blueprint: lem-zl-weil-shriek-coefficient-long-exact).

Proof plan, following the seven DAG steps:
1. Separated finite type is preserved by geometric base change. ConstructibleTruncations,
   PbcDescentFunctors and ConstructiblePullbackTExact supply the standard bounded
   t-structures and the exact, t-exact Frobenius pullbacks.
2. The heart is abelian. Kernels and cokernels of intertwining arrows acquire the
   induced invertible Frobenius structures, since exact pullback preserves homology.
   Their universal factorizations intertwine. Forgetting therefore reflects exactness.
3. Apply lem-weil-heart-short-exact-triangles to the underlying heart sequence.
   TR3 and epimorphy of its second arrow give naturality of the unique last arrow.
   Applied to Frobenius, this makes the last arrow equivariant without a triangulation
   on fixed pairs.
4. FieldShriekLowerBound gives exact compact support. The Weil-operation exchange and
   WeilShriekShiftCompatibility make the image triangle's last arrow equivariant.
5. Apply the homological heart functor and its shifts to this underlying triangle.
   This gives the long exact sequence; naturality of Frobenius/cohomology comparison
   makes the same-degree maps Weil arrows.
6. Use lem-zl-texact-cohomology-boundary-comparison and naturality of the underlying
   triangle's cohomology boundary: delta Theta = Theta G(delta). Thus each boundary
   is a Weil arrow. Uniqueness of truncation comparisons gives the displayed formula.
7. Reflection of exactness gives all three exactness positions in the Weil heart.
   Triangle naturality gives the boundary square for any morphism of short exact
   sequences. The boundary formula identifies the underlying canonical maps. -/
theorem zlWeilShriek_coefficient_long_exact :
    ∃ δ : ∀ (S : ShortComplex (sfCommonStageWeilSheaf D l hl X₀ Ω)), S.ShortExact →
        ∀ r : ℤ, (zlCoefficientHigherShriek D l hl Ω f₀ c r).obj S.X₃ ⟶
          (zlCoefficientHigherShriek D l hl Ω f₀ c (r + 1)).obj S.X₁,
      (∀ (S : ShortComplex (sfCommonStageWeilSheaf D l hl X₀ Ω))
        (hS : S.ShortExact) (r : ℤ),
        (∃ h, (ShortComplex.mk
          ((zlCoefficientHigherShriek D l hl Ω f₀ c r).map S.f)
          ((zlCoefficientHigherShriek D l hl Ω f₀ c r).map S.g) h).Exact) ∧
        (∃ h, (ShortComplex.mk
          ((zlCoefficientHigherShriek D l hl Ω f₀ c r).map S.g) (δ S hS r) h).Exact) ∧
        (∃ h, (ShortComplex.mk (δ S hS r)
          ((zlCoefficientHigherShriek D l hl Ω f₀ c (r + 1)).map S.f) h).Exact) ∧
        zlCoefficientBoundaryFormula D l hl Ω f₀ c S r (δ S hS r)) ∧
      ∀ (S T : ShortComplex (sfCommonStageWeilSheaf D l hl X₀ Ω))
        (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (r : ℤ),
        (zlCoefficientHigherShriek D l hl Ω f₀ c r).map φ.τ₃ ≫ δ T hT r =
          δ S hS r ≫ (zlCoefficientHigherShriek D l hl Ω f₀ c (r + 1)).map φ.τ₁ := by
  sorry

end WeilConjectures
