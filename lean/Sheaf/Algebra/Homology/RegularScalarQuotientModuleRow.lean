/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Algebra.Homology.RegularScalarQuotientNotation

/-! # The exact row of power quotient modules

Source: blueprint sk-lem-sp-tower, first proof paragraph; Stacks Project, Tags 03EI and 03CY.
(blueprint: lem-sp-regular-scalar-quotient-module-row).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.RegularScalarQuotient

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J CommRingCat.{r}]
  (R : Sheaf J CommRingCat.{r}) (t : (unit R).sections)

/-- The four-term row of quotient module sheaves, without complexes or tensor products.

Proof: put d=n-m. On each section ring A define a:A/(t^(m+1)) → A/(t^(n+1))
by [x] ↦ [t^d*x], and define red by reduction. The inclusion of principal
ideals defines red as a ring homomorphism. Changing x by t^(m+1)y changes a(x)
by t^(n+1)y, so a is well-defined and linear over A/(t^(n+1)). Cancel t^d
to prove a injective. Cancel t^(m+1) to show the kernel of multiplication by
t^(m+1) is the image of a. The kernel of red is the image of that multiplication,
and red is surjective on representatives. The image of a is the complementary
power ideal t^d B_n. These constructions commute with restrictions. Apply exact
module sheafification over the quotient ring presheaf, using Tag 03CY, and
identify its regular module with the regular module of the ring sheafification
via the comparison on underlying sets. This gives all asserted maps and exactness
over B_n. At n=m both maps are identities and the scalar power is zero. The
same formulas include a unit scalar and the zero ring.
Source: Stacks Project, Tags 03EI and 03CY.
(blueprint: lem-sp-regular-scalar-quotient-module-row). -/
theorem regularScalarQuotient_moduleRow
    (hregular : ∀ U : Cᵒᵖ, Function.Injective
      (fun x : R.obj.obj U ↦ (@id (R.obj.obj U) (t.val U)) * x)) (n m : ℕ) (hm : m ≤ n) :
    ∃ red : B R t n ⟶ B R t m,
      projection R t n ≫ red = projection R t m ∧
      ∃ (a : (res red).obj (unit (B R t m)) ⟶ unit (B R t n)),
        (∀ (U : Cᵒᵖ) (x : R.obj.obj U),
          a.val.app U ((projection R t m).hom.app U x) =
            (projection R t n).hom.app U ((@id (R.obj.obj U) (t.val U)) ^ (n - m) * x)) ∧
        Mono a ∧ Epi (ringMap red) ∧
        (∃ ha : a ≫ mul (B R t n) (scalarImage R t (projection R t n))
            (unit (B R t n)) (m + 1) = 0,
          (ShortComplex.mk a (mul (B R t n) (scalarImage R t (projection R t n))
            (unit (B R t n)) (m + 1)) ha).Exact) ∧
        (∃ hb : mul (B R t n) (scalarImage R t (projection R t n))
            (unit (B R t n)) (m + 1) ≫ ringMap red = 0,
          (ShortComplex.mk (mul (B R t n) (scalarImage R t (projection R t n))
            (unit (B R t n)) (m + 1)) (ringMap red) hb).Exact) ∧
        imageSubobject a = imageSubobject
          (mul (B R t n) (scalarImage R t (projection R t n))
            (unit (B R t n)) (n - m)) ∧
        (∀ h : n = m,
          red = eqToHom (congrArg (B R t) h) ∧
          (∀ (U : Cᵒᵖ) (x : (B R t m).obj.obj U),
            a.val.app U x = (eqToHom (congrArg (B R t) h.symm)).hom.app U x) ∧
          mul (B R t n) (scalarImage R t (projection R t n))
            (unit (B R t n)) (m + 1) = 0) := by
  sorry

end CategoryTheory.RegularScalarQuotient
