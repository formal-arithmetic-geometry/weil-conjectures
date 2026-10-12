module
public import Sheaf.CategoryTheory.ExactCouple
@[expose] public section
universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple
/-- (blueprint: lem-sp-derived-couple-kernel-identities)
Kernel and image identities for the derived differential, as in the element chase
of Stacks Tag 011R. -/
theorem derived_couple_kernel_identities {C : Type u} [Category.{v} C] [Abelian C]
    {s : ℕ} (X : BigradedExactCouple C s) :
    ∀ p q : ℤ,
      let a : X.D (p + 3) (q - 2) ⟶ X.D (p + 2) (q - 1) :=
        X.alpha (p + 3) (q - 2) ≫ eqToHom (by congr 1 <;> omega)
      kernelSubobject (X.d p q) =
          (Subobject.pullback (X.f p q)).obj (kernelSubobject (X.g (p + 2) (q - 1))) ∧
      kernelSubobject (X.d p q) =
          (Subobject.pullback (X.f p q)).obj (imageSubobject a) ∧
      kernelSubobject (X.g (p + 2) (q - 1)) = imageSubobject a ∧
      imageSubobject (X.d p q) =
          imageSubobject ((imageSubobject (X.f p q)).arrow ≫ X.g (p + 2) (q - 1)) ∧
      imageSubobject (X.d p q) =
          imageSubobject ((kernelSubobject (X.alpha (p + 2) (q - 1))).arrow ≫
            X.g (p + 2) (q - 1)) ∧
      imageSubobject (X.f p q) = kernelSubobject (X.alpha (p + 2) (q - 1)) ∧
      imageSubobject (kernel.ι (X.d p q) ≫ X.f p q) ≤ imageSubobject a := by
  sorry
end CategoryTheory.BigradedExactCouple
