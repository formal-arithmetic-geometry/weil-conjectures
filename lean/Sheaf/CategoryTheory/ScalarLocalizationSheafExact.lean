/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Exact scalar localization of module sheaves

Source: Stacks Project, Modules on Sites, Tag 03ET, with Tags 03ER, 03ES,
03DA and 03DB, and Algebra, Tag 00HT.
(blueprint: lem-weil-pbc-scalar-localization-sheaf-exact)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Actual scalar localization is additive and exact, as is any naturally isomorphic
functor. The object and arrow equalities specify the existing sheafified change of rings;
the existential packages those objects and maps as a functor, without choosing an unrelated
left adjoint.
Source: Stacks Project, Modules on Sites, Tag 03ET and Tags 03DA, 03DB, 03ER, 03ES;
Algebra, Tag 00HT (blueprint: lem-weil-pbc-scalar-localization-sheaf-exact).

Proof:
1. The presheaf `P(V) = R(V)[1/s(V)]` has flat section modules by
   `lem-weil-pbc-localization-flat`, including when a power of the section is zero.
2. Presheaf kernels and finite products are sectionwise. Flat tensoring preserves
   kernels by `lem-weil-pbc-flat-tensor-exact`, and finite products by the coordinate
   inclusion/projection tensor formulas, including the empty product. These formulas
   commute with restrictions, so the presheaf tensor preserves finite limits.
3. Apply `lem-pc-sites-modules-sheafification-flat`: sheafifying P gives the flat
   localization module. Tensor symmetry and `lem-pc-sheaf-modules-tensor-closed`
   give an additive exact endofunctor `T(M) = R_s ⊗_R M` on R-module sheaves.
4. Retaining multiplication on the first factor gives the specified change-of-rings
   objects and maps E. The sectionwise identity on tensors, followed by sheafification,
   identifies restriction of scalars of E with T. The balancing relation identifies
   their R-actions, and the formula `b ⊗ m ↦ b ⊗ f(m)` proves naturality.
5. By `lem-weil-pbc-module-sheaves-colimits-forgetful`, forgetting to abelian sheaves
   is faithful and exact and detects exactness. Thus exactness of T proves exactness
   of E in R_s-modules; faithfulness also proves additivity. No surjectivity on sections
   of a sheaf epimorphism is assumed.
6. In the abelian module categories, exactness preserves kernels and cokernels, while
   additivity preserves finite biproducts. The finite-diagram kernel/cokernel formulas
   imply finite-limit and finite-colimit preservation. A natural isomorphism F ≅ E
   conjugates the arrow maps and identifies images of short exact sequences; hence F
   has the same additivity and exactness properties. -/
theorem scalarLocalization_sheaf_exact
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (s : (R.obj ⋙ forget CommRingCat.{u}).sections) :
    ∃ (E : ringedSiteModules.{u, u, vC, uC}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
        ringedSiteModules.{u, u, vC, uC} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ringedLocalizationRingOfUniverses.{u, uC, vC} (J := J) R s)))
      (hE : ∀ M : ringedSiteModules.{u, u, vC, uC}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        E.obj M = SheafOfModules.changeOfRingsOfUniverses.{vC, uC, u, u}
        (ringedLocalizationRingUnitOfUniverses.{u, uC, vC} (J := J) R s) M),
      (∀ {M N : ringedSiteModules.{u, u, vC, uC}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (f : M ⟶ N),
        E.map f = eqToHom (hE M) ≫
          SheafOfModules.changeOfRingsHomOfUniverses.{vC, uC, u, u}
            (ringedLocalizationRingUnitOfUniverses.{u, uC, vC} (J := J) R s) M f ≫
              eqToHom (hE N).symm) ∧
      E.Additive ∧ PreservesFiniteLimits E ∧ PreservesFiniteColimits E ∧
      (∀ F : ringedSiteModules.{u, u, vC, uC}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
          ringedSiteModules.{u, u, vC, uC}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (ringedLocalizationRingOfUniverses.{u, uC, vC} (J := J) R s)),
        Nonempty (F ≅ E) →
          F.Additive ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F) := by
  sorry

end CategoryTheory
