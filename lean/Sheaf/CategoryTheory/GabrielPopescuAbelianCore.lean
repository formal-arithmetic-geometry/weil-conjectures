/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! The abelian Gabriel--Popescu component of the derived presentation. -/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits

namespace CategoryTheory

/-- The Gabriel--Popescu abelian presentation, with the large-coproduct hypothesis
needed to extend the small presentation to the displayed module universe.
Source: Stacks Project, Tags 0F5V and 0F5X, with Tag 05NU for the Baer criterion.

(blueprint: new-stage3-gabriel-popescu-abelian-core)

Proof in words: choose a separator G of A and replace its endomorphism ring by
the opposite of the w-small endomorphism ring obtained from local smallness.
For a module M, use the canonical free presentation by coproducts of G and take
the corresponding cokernel in A; this gives F, while Hom(G,-) gives U.  For
w-sized modules the usual Gabriel--Popescu construction proves the adjunction,
the exactness of F, and invertibility of the counit.  The hypothesis that
DerivedCategory A has coproducts indexed by Type (max w vA vH) gives the same
coproducts in A: form the coproduct of the objects concentrated in degree zero,
use vanishing of maps into positive truncations to put it in degree zero, and
identify its zeroth cohomology by the truncation adjunction.  Thus the free
presentation works at the larger size and its counit agrees with the small one.
For an injective I, U(I) is injective on w-small modules; the Baer criterion for
the w-sized ring extends this to all displayed modules.  Adjunction and enough
injectives show that F preserves monomorphisms.  Since a left adjoint is right
exact, F is additive and exact, and the resulting counit is invertible.
-/
theorem gabriel_popescu_abelian_core
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)] :
    ∃ (S : Type w) (rS : Ring S),
      letI := rS
      ∃ hD : HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S),
      letI := hD
      ∃ (F : ModuleCat.{max w vH} S ⥤ A) (U : A ⥤ ModuleCat.{max w vH} S)
        (adj₀ : F ⊣ U) (addF : F.Additive)
        (limF : PreservesFiniteLimits F) (colimF : PreservesFiniteColimits F),
      let _ := addF
      let _ := limF
      let _ := colimF
      IsIso adj₀.counit := by
  sorry

end CategoryTheory
