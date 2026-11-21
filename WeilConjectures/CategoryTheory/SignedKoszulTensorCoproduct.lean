/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel
import WeilConjectures.CategoryTheory.SignedKoszulTensorAssembly

/-!
# The coproduct property of negative Koszul pure tensors

## References

* Stacks Project, algebraization.tex, Tag 0A0E.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u z
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- For a positive number of negative Koszul factors, the specified pure-tensor
inclusions form a coproduct in each degree. This concerns only the underlying
graded object, not its differential.

Stacks Project, algebraization.tex, Tag 0A0E. -/
theorem isColimit_ringedNegativeKoszulSummands_succ
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) :
    Nonempty (IsColimit (Cofan.mk
      (((ringedNegativeKoszulTensor O ρ a m).obj K).X q)
      (ringedNegativeKoszulSummand O ρ a m K q))) := by
  classical
  exact isColimit_ringedNegativeKoszulTensor_of_basis O ρ r a m K q (fun n ↦
    isColimit_ringedNegativeKoszulBasis_succ O r
      (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m n)

end CategoryTheory
