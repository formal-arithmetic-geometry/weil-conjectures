/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q9
-/
module

public import Sheaf.Paper.FiniteQuotientCoefficientLayerData
public import Sheaf.Paper.FiniteQuotientLayerTensorComplex
public import Sheaf.Paper.FinitePerfectQuotientModelData
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral

import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-! # Derived slice comparison for the finite quotient layer

Source: Stacks Project, sites-cohomology.tex, Tags 094I and 06YU.
(blueprint: lem-weil-pbc-finite-quotient-layer-tensor-derived-slice-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/--
The actual finite quotient layer and its derived constant tensor model become
isomorphic after restriction to the etale chart.  This is the derived-object
comparison before applying exact slice homology.  It is the unresolved derived
tensor and balancing step of the finite-layer argument.

Source: Stacks Project, sites-cohomology.tex, Tags 094I and 06YU.
Proof: identify the kernel of the successive quotient with the ideal-power
layer, use the compatible coefficient maps to balance the derived tensor, and
transport the supplied residue-chart isomorphism through the derived tensor
descent equivalence.  Restriction to the chart is exact and retains the
successor coefficient action.
(blueprint: lem-weil-pbc-finite-quotient-layer-tensor-derived-slice-comparison).
-/
theorem finiteQuotient_layer_tensor_derived_slice_comparison
    (X : Scheme.{t})
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n))
    (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (b : ℤ) (n : ℕ) (Z : X.Etale)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (0 + 1))) ℤ)
    (hPb : P.IsStrictlyLE b)
    (hP : ∀ i : ℤ, Module.Projective (A ⧸ d.ideal ^ (0 + 1)) (P.X i))
    (e : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d 0)
          ((toProEt X).obj Z) ((completedAdicQuotientReduction X d 0).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d 0)
          ((toProEt X).obj Z) ((completedAdicDerivedChange X (φ 0)).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))))) :
    Nonempty
      ((ringedDerivedRestrictionGeneral (completedAdicFiniteRing X d (n + 1))
          ((toProEt X).obj Z)).obj (finiteQuotientLayerObject X d M n) ≅
        (ringedDerivedRestrictionGeneral (completedAdicFiniteRing X d (n + 1))
          ((toProEt X).obj Z)).obj
          ((completedAdicDerivedChange X (φ (n + 1))).obj
            (DerivedCategory.Q.obj
              (finiteModelConstantComplex X _
                (finiteQuotientLayerTensorComplex d.ideal n P))))) := by
  sorry

end AlgebraicGeometry.Scheme
