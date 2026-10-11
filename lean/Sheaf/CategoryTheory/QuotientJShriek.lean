/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# The canonical extension-by-zero generator epimorphism

Source: Stacks Project, Modules on Sites, Lemma 18.28.8, Tag 03EW, clause (3)
(blueprint: lem-pc-sites-modules-quotient-j-shriek).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- On a small ringed site, the coproduct of `j_{U!} R_U`, indexed by all pairs
`(U,s)` with `s ∈ M(U)`, exists and its canonical section-evaluation map is epic.
Here the free Yoneda presheaf is `V ↦ ⨁ (V ⟶ U), R(V)`, and its sheafification
is `j_{U!} R_U`. The component map is the sheafification of the free Yoneda
map corresponding to `s`, followed by the sheafification counit.

Source: Stacks Project, Lemma 18.28.8 (03EW), clause (3)
(blueprint: lem-pc-sites-modules-quotient-j-shriek).

Proof: (1) By the free-presheaf adjunction and sheafification adjunction,
`Hom(j_{U!} R_U,M) = M(U)`: the free generator at the identity maps to `s`,
and its restriction along `V ⟶ U` maps to the restriction of `s`. This is
step 1 of the node, using def-weil-extension-by-zero-presheaf and
def-weil-presheaf-modules-sheafification.
(2) The pairs form a set; sheafifying the sectionwise direct sum gives their
coproduct, by lem-weil-pbc-module-sheaves-colimits-forgetful, clause (2).
Its universal property gives the map with the specified components.
(3) Each section `t ∈ M(V)` is the image of the identity generator in the
`(V,t)` summand. The map is thus sectionwise surjective, its sectionwise
cokernel is zero, and its sheafified cokernel is zero by
lem-weil-pbc-module-sheaves-colimits-forgetful, clause (1). In the abelian
category of def-weil-sheaf-of-modules-category it is an epimorphism. -/
theorem exists_epi_coproduct_jShriek
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{u})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (M : SheafOfModules.{u} R) :
    ∃ (c : Cofan (fun m : M.val.Elements =>
        (PresheafOfModules.sheafification (𝟙 R.obj)).obj m.freeYoneda))
      (_hc : IsColimit c) (q : c.pt ⟶ M),
      Epi q ∧ ∀ m : M.val.Elements,
        c.inj m ≫ q =
          (PresheafOfModules.sheafification (𝟙 R.obj)).map m.fromFreeYoneda ≫
            (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app M := by
  sorry

end SheafOfModules
