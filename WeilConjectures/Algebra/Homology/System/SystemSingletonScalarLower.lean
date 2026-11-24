/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarBasic

/-! # Compatibility of singleton coefficient change with lower-singleton maps

## References

* Stacks Project, Tags 06YT, 0D6D
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

/-- The normalized singleton coefficient comparisons commute with the canonical
lower-singleton maps and the specified scalar associators. -/
theorem singletonScalarDerivedIso_lower (n m : ℕ) (h : n ≤ m)
    (P : DerivedCategory (systemLevel B m)) :
      A.model.T.map (singletonLowerMap S T B h P) ≫
          (singletonScalarDerivedIso S T a A m).hom.app P =
        (singletonScalarDerivedIso S T a A n).hom.app ((systemDerivedTensor S B h).obj P) ≫
          (singletonSequenceDerived S T D n).map ((singletonScalarSquare S a n m h).hom.app P) ≫
          singletonLowerMap S T D h ((S (a.app (op m))).model.T.obj P) := by sorry

end SheafOfModules
