/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FrameworkPbcComparisonSystem
import WeilConjectures.AlgebraicGeometry.SimultaneousIntegralPullbackComparisons
import WeilConjectures.AlgebraicGeometry.FrameworkPbcIntegralComparisonLaws
import WeilConjectures.AlgebraicGeometry.FrameworkPbcRawComparisonLaws

/-! # Framework and PBC pullback scalar coherence

Source: purity-transport coefficient-change proof
(blueprint: lem-pur-framework-pbc-pullback-scalar-bridge).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrameworkPbc

/-- The raw unit and composition equations, with both compositors normalized by
localizing the specified integral ones. This does not replace either compositor
by one transported along pi.
Source: Stacks 099N, 0D6D and blueprint raw-rationalization clause
(blueprint: lem-pur-framework-pbc-pullback-scalar-bridge). -/
structure RawCoherence (l : ℕ) [Fact l.Prime] (s : System.{u} l) where
  unit : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))],
    ∃ su : rationalDerivedPullback l A (𝟙 W) ≅ 𝟭 _,
    ∃ pu : pbcConditionalRational (pbcIntegralDatum l A)
        (pbcActualCompletedPull (𝟙 W) (pbcIntegralDatum l A))
        (s.raw_pullback A (𝟙 W)).preserves (pbcUniformizer l A) ≅ 𝟭 _,
      (∀ K : sfIntegralConstructibleCategory l A W,
        HEq (su.hom.app ((sfRationalConstructibleLocalization l A W).obj K))
          ((sfRationalConstructibleLocalization l A W).map
            (ObjectProperty.homMk
              (X := (constructibleIntegralPullback l A (𝟙 W)).obj K) (Y := K)
              (integralComparisonUnit l A s.realization W K).hom))) ∧
      (∀ K : PbcBoundedConstructibleComplete W (pbcIntegralDatum l A),
        HEq (pu.hom.app ((pbcRationalization W (pbcIntegralDatum l A)
            (pbcUniformizer l A)).obj K))
          ((pbcRationalization W (pbcIntegralDatum l A) (pbcUniformizer l A)).map
            (ObjectProperty.homMk
              (X := (pbcConditionalIntegral (pbcIntegralDatum l A)
                (pbcActualCompletedPull (𝟙 W) (pbcIntegralDatum l A))
                (s.raw_pullback A (𝟙 W)).preserves).obj K) (Y := K)
              ((pbcActualCompletedPullIdIso
              (pbcIntegralDatum l A) W).hom.app ⟨K.obj, K.property.1⟩)))) ∧
      ∀ K : sfRationalConstructibleCategory l A W,
        (s.raw_pullback A (𝟙 W)).rational.hom.app K ≫
          pu.hom.app ((s.coefficient A W).rational.functor.obj K) =
        (s.coefficient A W).rational.functor.map (su.hom.app K)
  composition : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (X Y Z : Scheme.{u})
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]
    (h : X ⟶ Y) (g : Y ⟶ Z),
    ∃ sc : rationalDerivedPullback l A (h ≫ g) ≅
        rationalDerivedPullback l A g ⋙ rationalDerivedPullback l A h,
    ∃ pc : pbcConditionalRational (pbcIntegralDatum l A)
        (pbcActualCompletedPull (h ≫ g) (pbcIntegralDatum l A))
        (s.raw_pullback A (h ≫ g)).preserves (pbcUniformizer l A) ≅
      pbcConditionalRational (pbcIntegralDatum l A)
        (pbcActualCompletedPull g (pbcIntegralDatum l A))
        (s.raw_pullback A g).preserves (pbcUniformizer l A) ⋙
      pbcConditionalRational (pbcIntegralDatum l A)
        (pbcActualCompletedPull h (pbcIntegralDatum l A))
        (s.raw_pullback A h).preserves (pbcUniformizer l A),
      (∀ K : sfIntegralConstructibleCategory l A Z,
        HEq (sc.hom.app ((sfRationalConstructibleLocalization l A Z).obj K))
          ((sfRationalConstructibleLocalization l A X).map
            (ObjectProperty.homMk
              (X := (constructibleIntegralPullback l A (h ≫ g)).obj K)
              (Y := (constructibleIntegralPullback l A h).obj
                ((constructibleIntegralPullback l A g).obj K))
              (integralComparisonComposition l A s.realization h g K).hom))) ∧
      (∀ K : PbcBoundedConstructibleComplete Z (pbcIntegralDatum l A),
        HEq (pc.hom.app ((pbcRationalization Z (pbcIntegralDatum l A)
            (pbcUniformizer l A)).obj K))
          ((pbcRationalization X (pbcIntegralDatum l A) (pbcUniformizer l A)).map
            (ObjectProperty.homMk
              (X := (pbcConditionalIntegral (pbcIntegralDatum l A)
                (pbcActualCompletedPull (h ≫ g) (pbcIntegralDatum l A))
                (s.raw_pullback A (h ≫ g)).preserves).obj K)
              (Y := (pbcConditionalIntegral (pbcIntegralDatum l A)
                (pbcActualCompletedPull h (pbcIntegralDatum l A))
                (s.raw_pullback A h).preserves).obj
                  ((pbcConditionalIntegral (pbcIntegralDatum l A)
                    (pbcActualCompletedPull g (pbcIntegralDatum l A))
                    (s.raw_pullback A g).preserves).obj K))
              ((pbcActualCompletedPullCompIso h g
              (pbcIntegralDatum l A)).inv.app ⟨K.obj, K.property.1⟩)))) ∧
      ∀ K : sfRationalConstructibleCategory l A Z,
        (s.raw_pullback A (h ≫ g)).rational.hom.app K ≫
          pc.hom.app ((s.coefficient A Z).rational.functor.obj K) =
        (s.coefficient A X).rational.functor.map (sc.hom.app K) ≫
          (s.raw_pullback A h).rational.hom.app ((rationalDerivedPullback l A g).obj K) ≫
          (pbcConditionalRational (pbcIntegralDatum l A)
            (pbcActualCompletedPull h (pbcIntegralDatum l A))
            (s.raw_pullback A h).preserves (pbcUniformizer l A)).map
              ((s.raw_pullback A g).rational.hom.app K)

/-- Framework/PBC comparison for arbitrary morphisms, with scalar and tensor coherence.
Source: purity-transport coefficient-change proof; Stacks 099N, 0941, 07A4, 0D6D
(blueprint: lem-pur-framework-pbc-pullback-scalar-bridge).

Proof: First identify the completed coefficient sheaves, preserving every finite
projection and structural map. Coefficient relabeling carries ordinary tensors,
adjunction units and counits to the identical balanced tensors. For a flat-term
K-flat representative use the whole strict tower of reduced pullbacks, with its
actual transition maps. Exact countable products identify its Roos realization
with the PBC total derived limit. The two coordinates fix the augmentation and
all projections, yielding pi naturally and independently of representatives.
Substitution retains the iterated counits. At finite levels the composition
routes are the same adjunction-normalized map; completion-unit uniqueness
identifies the PBC compositor, while the framework compositor is its prescribed
system realization. The identity tower similarly gives the specified unit.
Finite freeness commutes with completion; its unique unit-preserving comparison
is kappa. Hence the inverse completed scalar/pullback map is precisely completion
of inverse ordinary balancing after kappa. The canonical chi identifies the
strict scalar extension with ordinary scalar extension; invert chi and apply
coefficient relabeling to obtain j. Both scalar routes send every strict-system
generator to the same balanced tensor, so whole-tower realization gives the
scalar square. For tensor retain both quotient Roos coordinates and the signed
total comparison: the two routes send s tensor (x tensor y) to
(s tensor x) tensor (1 tensor y), with inverse multiplying the scalars. This is
the canonical ordinary PBC tensor map; unit-preserving completion gives the
stated tensor conjugation. Signed cone shifts commute with these generator maps;
identity and successive scalar extensions give the multiplication unitors and
associators. Finally localize the restricted functors and every comparison with
one; bilinearity extends all equations to denominators and preserves inverses.
No quotient-ring flatness or geometric exchange invertibility is used.

Lean reduction: obtain the single simultaneous realization from the existing
realization theorem. The integral comparison step provides the four integral
families and their eight laws for that realization. The raw localization step
takes those fixed families and the four relevant laws and supplies the coefficient
equivalences, raw families, raw squares, and normalized raw unit and composition.
Assemble System and RawCoherence explicitly from these witnesses. The two steps
remain separate named theorems; neither asserts the full bridge. -/
theorem frameworkPbcPullbackScalarBridge (l : ℕ) [Fact l.Prime] :
    ∃ s : System.{u} l, Nonempty (RawCoherence l s) := by
  obtain ⟨realization, realization_coherent⟩ :=
    integralPullbackComparisonRealization_simultaneous.{u} l
  obtain ⟨pullback, scalar, tensor, scalarTensor, hunit, hcomposition, hscalar_square,
      htensor_square, hscalar_unit, hscalar_tower, hpullback_shifts, hscalar_shifts⟩ :=
    frameworkPbcIntegralComparisonLaws l realization
      (fun A B _ _ _ _ _ _ i ↦ realization_coherent A B i)
  obtain ⟨coefficient, raw_pullback, raw_scalar, raw_tensor, hraw_scalar_square,
      hraw_tensor_square, hraw_unit, hraw_composition⟩ :=
    frameworkPbcRawComparisonLaws l realization pullback tensor scalarTensor
      hunit hcomposition hscalar_square htensor_square
  refine ⟨{
    realization := realization
    realization_coherent := fun A B _ _ _ _ _ _ i ↦ realization_coherent A B i
    pullback := pullback
    coefficient := coefficient
    scalar := scalar
    tensor := tensor
    scalarTensor := scalarTensor
    unit := hunit
    composition := hcomposition
    scalar_square := hscalar_square
    tensor_square := htensor_square
    scalar_unit := hscalar_unit
    scalar_tower := hscalar_tower
    pullback_shifts := hpullback_shifts
    scalar_shifts := hscalar_shifts
    raw_pullback := raw_pullback
    raw_scalar := raw_scalar
    raw_tensor := raw_tensor
    raw_scalar_square := hraw_scalar_square
    raw_tensor_square := hraw_tensor_square
  }, ⟨{ unit := hraw_unit, composition := hraw_composition }⟩⟩

end WeilConjectures.FrameworkPbc
