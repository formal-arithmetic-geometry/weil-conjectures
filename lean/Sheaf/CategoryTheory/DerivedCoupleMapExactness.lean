/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.CategoryTheory.DerivedCoupleMapConstruction

/-!
# Exactness of the induced maps on images and cycle quotients

Source: Stacks Project, Lemma 12.21.2 (Tag 011R), Remark 12.21.5 (Tag 0AMJ).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {s : ℕ}

/-- The induced maps are exact, provided they satisfy the defining descent equations.
Source: Stacks Project, Lemma 12.21.2, Tag 011R, and Remark 12.21.5, Tag 0AMJ
(blueprint: lem-sp-derived-map-exactness).

Proof. Use generalized elements with epimorphic refinements, which detect images
and kernels in an abelian category. At the image of `a`, an element annihilated
by the restricted `a` lifts through `f`, by `ha`. The lift is a cycle, because
its `f`-image lies in the incoming image of `a`, annihilated by `g`. Its cycle
class maps to the original element by `f_comm`; the converse follows from `haf`.
At the cycle quotient, lift an element through the epi cycle projection. If its
`forward`-image is zero, `f_comm` and mono image cancellation imply that its
cycle lift is killed by `f`. Lift it through `g` using `hf`, then apply the
incoming image epimorphism of `a`. The equation `g_comm` identifies the resulting
`backward`-image with the original class. Conversely, that image is killed by
`forward`, by `hg` and the equations.
At the next image of `a`, lift an element killed by `backward` through the epi
image factorization of the incoming `a`. Its `g`-image is a boundary, by `g_comm`
and the kernel description of the cycle quotient. Lift that boundary through
its defining incoming differential; subtract the resulting `f`-image from the
chosen lift. This does not change its image under `a`, by `haf`, and kills its
`g`-image by the boundary equality `hβeq`. By `hgg` the corrected lift comes
from the preceding `a`. The equation `alpha_comm` gives an `alpha`-preimage
of the element. Conversely an `alpha`-image is killed by `backward` by `hga`.
These image and kernel inclusions descend along epimorphisms: every subobject
of an abelian category is the kernel of its cokernel. They prove all three
subobject equalities, with the indices transported as in the stated equations. -/
theorem derivedCoupleMapData_exact (D E : ℤ → ℤ → C)
    (a : ∀ p q, D p q ⟶ D (p - 1) (q + 1))
    (f : ∀ p q, E p q ⟶ D (p + 2) (q - 1))
    (g : ∀ p q, D p q ⟶ E (p + s) (q - s))
    (β : ∀ p q, E (p - s - 2) (q + s + 1) ⟶ E p q)
    (hβ : ∀ p q, β p q ≫ f p q ≫ g (p + 2) (q - 1) = 0)
    (hg : ∀ p q, g p q ≫ f (p + s) (q - s) = 0)
    (haf : ∀ p q, f p q ≫ a (p + 2) (q - 1) = 0)
    (hga : ∀ p q, a p q ≫ g (p - 1) (q + 1) = 0)
    (ha : ∀ p q, imageSubobject (f p q) = kernelSubobject (a (p + 2) (q - 1)))
    (hf : ∀ p q, imageSubobject (g p q) = kernelSubobject (f (p + s) (q - s)))
    (hgg : ∀ p q, imageSubobject (a p q) = kernelSubobject (g (p - 1) (q + 1)))
    (hβeq : ∀ p q, β p q =
      (f (p - s - 2) (q + s + 1) ≫ g ((p - s - 2) + 2) ((q + s + 1) - 1)) ≫
        eqToHom (by congr 1 <;> omega))
    (M : DerivedCoupleMapData D E a f g β hβ hg) :
    (∀ p q, imageSubobject (M.forward p q) =
      kernelSubobject (M.alpha (p + 2) (q - 1))) ∧
    (∀ p q, imageSubobject (M.backward p q) =
      kernelSubobject (M.forward (p + (s + 1)) (q - (s + 1)))) ∧
    (∀ p q, imageSubobject (M.alpha p q) =
      kernelSubobject (M.backward (p - 1) (q + 1))) := by
  sorry

end CategoryTheory
