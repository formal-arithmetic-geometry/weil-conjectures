/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTransposeData

/-! # Unit and signed-symmetry coherence of the exact site tensor comparison

Source: Stacks 07A4 and finite-ring site transport, proof step 5
(blueprint: lem-pur-finite-ring-tensor-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale

/-- The specified comparison respects scalar evaluation and the signed braiding.
Source: Stacks 07A4; proof steps 5 and 11 of the finite-ring site transport
(blueprint: lem-pur-finite-ring-tensor-coherence).

Proof: use K-flat representatives with flat terms for both inputs. The tensor
comparison is induced by the ordinary inverse-image pure-tensor map. Its unit
comparison is induced by the inverse image of the constant scalar unit. On every
bidegree summand, multiplying a scalar before or after comparison gives the same
section; exchanging factors gives the same sign (-1)^(ab) on both sites.
The summands generate the direct-sum total tensor complex, so these are equal
chain maps. The canonical exact/left-derived comparison identifies their images
with the named comparisons below. Localization proves both equations. This argument
uses no bound or constructibility and includes the zero ring and empty scheme. -/
theorem finiteRingTensorCoherence (B : Type) [CommRing B] [Finite B] (T : Scheme.{u}) :
    (∀ (Z K : DerivedCategory (Sheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} B)))) (e : Z ⟶ 𝟙_ _),
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T).mapDerivedCategory.map
          ((e ⊗ₘ 𝟙 K) ≫ (λ_ K).hom) =
        (finiteRingSiteTensor (ModuleCat.{u + 1} (ULift.{u + 1} B)) T Z K).hom ≫
          (((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T).mapDerivedCategory.map e ≫
              (finiteRingSiteUnit (ModuleCat.{u + 1} (ULift.{u + 1} B)) T).hom) ⊗ₘ
            𝟙 ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
              T).mapDerivedCategory.obj K)) ≫ (λ_ _).hom) ∧
    (∀ M N : DerivedCategory (Sheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} B))),
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T).mapDerivedCategory.map
          (@BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) M N).hom ≫
        (finiteRingSiteTensor (ModuleCat.{u + 1} (ULift.{u + 1} B)) T N M).hom =
      (finiteRingSiteTensor (ModuleCat.{u + 1} (ULift.{u + 1} B)) T M N).hom ≫
        (@BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _)
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T).mapDerivedCategory.obj M)
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
            T).mapDerivedCategory.obj N)).hom) := by sorry

end AlgebraicGeometry.ProEtale
