/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularCoordinatePurityMaps

/-! # Tensor evaluation for the purity map of a smooth section

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/
sk-thm-regular.proof.md, Step 4(iii), passing twists through exceptional inverse
image and evaluating the inverse base twist
(blueprint: lem-pur-regular-section-tate-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The tensor/counit purity pairing commutes with inverse-Tate evaluation.

Proof: unfold the tensor/counit definition of purity at the base Tate line. Its
naturality and the exceptional co-projection identify this pairing with the
pairing at the coefficient unit tensored with the base Tate line. Conjugate the
compact-support composition and identity constraints to pass this tensor factor
through the exceptional section unitor. Reassociate the three factors, combine
the Tate lines of indices m+c and -m, and evaluate the m,-m pair. Co-projection
additivity and evaluation coherence give the displayed equality. The even
cohomological shifts of the Tate lines contribute sign +1. This argument uses
only p and its section, and no absolute orientations or ground field. The unit
laws cover m=0 and c=0, and the argument applies to an empty scheme as well.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/
sk-thm-regular.proof.md, Step 4(iii), tensor/counit and inverse-Tate cancellation
(blueprint: lem-pur-regular-section-tate-evaluation). -/
theorem regular_section_tate_evaluation
    (A : Type (u + 1)) [CommRing A] [Finite A] [NeZero (ringChar A)]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X B : Scheme.{u}} [IsNoetherian X] [IsNoetherian B]
    (p : X ⟶ B) (z : B ⟶ X)
    [HasCompactification p] [HasCompactification z] [HasCompactification (z ≫ p)]
    [QuasiCompact p] [IsSeparated p] [IsClosedImmersion z]
    [QuasiCompact (z ≫ p)]
    (c : ℕ) [SmoothOfRelativeDimension c p]
    [HasInvertibleExponent A X] [HasInvertibleExponent A B]
    (hB : IsUnit (N : Γ(B, ⊤))) (m : ℕ) (hz : z ≫ p = 𝟙 B) :
    let G := rightDerivedUpperShriek A z
    let T := derivedTensor (ModuleCat.{u + 1} A) B
    let v := regularPurityAtTateIso A N hN hA p c hB m
    let U := regularExceptionalSectionUnitor A p z hz
    let D := (regularCoprojectionIso A z ((m + c : ℕ) : ℤ)).inv ≫
      G.map v.hom ≫ U.hom.app (shiftedTateObject A B (m : ℤ))
    let r := (regularCoprojectionIso A z (c : ℤ)).inv ≫
      G.map (regularSmoothUnitPurityIso A N hN hA p c hB).hom ≫
        U.hom.app (constantComplex A B)
    (T.map D).app (shiftedTateObject A B (-(m : ℤ))) ≫
        (regularInverseTateEvaluation A B (m : ℤ)).inv =
      (regularCancelBaseTateIso A B (G.obj (constantComplex A X)) m c).hom ≫ r := by
  sorry

end AlgebraicGeometry.Etale
