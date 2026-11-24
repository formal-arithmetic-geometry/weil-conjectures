/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarBasic

/-! # K-flatness on the ringed sequence site of singleton extension

## References

* Stacks Project, Tags 06YN, 0D6D, 0G7E
* Zheng, Construction 4.1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

variable (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- Ordinary singleton extension preserves flat-term K-flat complexes on the whole
ringed sequence site. -/
theorem singletonSequenceOrdinary_kFlat (n : ℕ)
    (P : CochainComplex (systemLevel B n) ℤ) (hP : systemLevelKFlat B n P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := systemSequenceRing B)
      (((singletonSequenceOrdinary S T B n).mapHomologicalComplex (.up ℤ)).obj P) ∧
    (∀ i : ℤ, IsFlatOnSite (R := systemSequenceRing B)
      ((singletonSequenceOrdinary S T B n).obj (P.X i))) := by sorry

end SheafOfModules
