/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Linearity of localized extension by zero on derived module sheaves

Source: Stacks Project, Modules on Sites, Tags 03CY, 03DI and 03DJ
(blueprint: lem-cbc-localized-extension-zero-linear-derived).
-/

@[expose] public section
set_option autoImplicit false
universe u a w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u + 1})
  (A : Type a) [CommRing A]
  (U : C)
  (rho : ∀ V : Cᵒᵖ, A →+* O.obj.obj V)
  [HasDerivedCategory.{w} (ringedSiteModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))]
  [HasDerivedCategory.{w} (ringedSiteModules.{u + 1}
    (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O).over U))]
/--
Module extension by zero is additive and linear, and its termwise unbounded derived functor
is linear, commutes with integer shifts, and is triangulated. The `A`-linear structures on
the two module-sheaf categories are the bound ones, pinned by the two sectionwise clauses;
those on the two derived categories are Mathlib's `DerivedCategory.instLinear`, induced from
them by degreewise scalars on cochain maps and localization
(lem-weil-linear-abelian-derived-category). Source: Stacks Project, Modules on Sites,
Tags 03CY, 03DI and 03DJ (blueprint: lem-cbc-localized-extension-zero-linear-derived).
Proof:
1. Define `(a • t)_V(x) = rho V a • t_V(x)` and `(t + t')_V = t_V + t'_V` on module-sheaf
   morphisms; `hnat` makes restriction carry `rho V a` to `rho W a`, and commutativity of
   `O(V)` makes `a • t` linear. Composition is bilinear sectionwise. The same on `C / U`,
   where `O_U(V → U) = O(V)` (def-pur-localized-ringed-site). Both categories are abelian.
2. On the direct-sum extension presheaf (def-weil-extension-by-zero-presheaf),
   `P_{t + t'} = P_t + P_{t'}` and `P_{a • t} = a • P_t` summandwise, for any number of maps
   `V → U`, including none.
3. Functoriality of module sheafification gives `j_! t ∘ η_F = η_G ∘ P_t`; uniqueness of the
   factorization through `η_F` (Stacks 03CY) transfers both identities to `j_!`, so
   `localizedModuleExtension` is additive and `A`-linear.
4. `localizedModuleExtension` is exact (lem-pur-site-restriction-module-adjunction-exact), so
   `mapDerivedCategory` is its termwise unbounded derived functor; Mathlib's instances give
   its shift compatibility and triangulatedness (lem-sf-exact-functor-derived-triangulated).
5. With the induced derived structures (lem-weil-linear-abelian-derived-category), Mathlib's
   `Functor.instLinearDerivedCategoryMapDerivedCategory` applied to Steps 3 and 4 gives
   `A`-linearity of the derived functor on every derived morphism
   (lem-cbc-exact-linear-derived-functor).
-/
theorem localizedExtensionZeroLinearDerived (hnat : ∀ {V W : Cᵒᵖ} (f : V ⟶ W) (a : A),
    O.obj.map f (rho V a) = rho W a) :
    ∃ (_ : Linear A (ringedSiteModules.{u + 1} ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))),
      ∃ (_ : Linear A (ringedSiteModules.{u + 1} (((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O).over U))),
        (∀ (M N : ringedSiteModules.{u + 1} ((sheafCompose J
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
          (f : M ⟶ N) (a : A) (V : Cᵒᵖ) (x : M.val.obj V),
          (a • f).val.app V x = rho V a • f.val.app V x) ∧
        (∀ (M N : ringedSiteModules.{u + 1} (((sheafCompose J
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O).over U))
          (f : M ⟶ N) (a : A) (V : (Over U)ᵒᵖ) (x : M.val.obj V),
          (a • f).val.app V x =
            rho (Opposite.op V.unop.left) a • f.val.app V x) ∧
        (SheafOfModules.localizedModuleExtension O U).Additive ∧
        Functor.Linear A (SheafOfModules.localizedModuleExtension O U) ∧
        (SheafOfModules.localizedModuleExtension O U).mapDerivedCategory.Additive ∧
        Functor.Linear A (SheafOfModules.localizedModuleExtension O U).mapDerivedCategory ∧
        Nonempty
          ((SheafOfModules.localizedModuleExtension O U).mapDerivedCategory.CommShift ℤ) ∧
        (SheafOfModules.localizedModuleExtension O U).mapDerivedCategory.IsTriangulated := by
  sorry
end CategoryTheory
