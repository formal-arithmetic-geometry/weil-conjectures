/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarBasic

/-! # Normalized representative of singleton coefficient change

## References

* Stacks Project, Tags 09T5, 0D6D, 0FND
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
  {B D : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : B ⟶ D)
  (A : SystemScalarModel (singletonSequenceRingMap a))

/-- The specified derived conjugate is represented by the ordinary singleton
coefficient comparison, with the actual universal comparison maps. -/
theorem singletonScalarDerivedIso_rep (n : ℕ)
    (P : CochainComplex (systemLevel B n) ℤ) :
      (singletonScalarDerivedIso S T a A n).hom.app (DerivedCategory.Q.obj P) ≫
          singletonScalarTargetComparison S T a n P =
        singletonScalarSourceComparison S T a A n P ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (singletonScalarOrdinaryIso S T a A n)
            (.up ℤ)).hom.app P) := by sorry

end SheafOfModules
