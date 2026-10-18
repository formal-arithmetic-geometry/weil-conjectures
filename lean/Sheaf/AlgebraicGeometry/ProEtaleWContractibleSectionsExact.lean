/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Sheaf.AlgebraicGeometry.ProEtale.Projective

/-!
# Exact sections over a w-contractible affine pro-etale object

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-wc-sections/det-pe-wc-sections-exact.md
(blueprint: det-pe-wc-sections-exact).
-/

@[expose] public section

set_option autoImplicit false

universe t u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Sections over `Spec D` are exact, for both abelian sheaves and module sheaves.
The two pairs of finite-limit and finite-colimit preservation assertions express
exactness of the corresponding additive evaluation functors. The section universe
contains the small site; the coefficient-ring universe is independent.

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-wc-sections/det-pe-wc-sections-exact.md
(blueprint: det-pe-wc-sections-exact).

Proof:
1. By lem-weil-pbc-sheafification-exact, kernels of abelian sheaves are sectionwise.
   By lem-weil-pbc-module-sheaves-limits-sectionwise, so are module kernels.
   Evaluation is additive, with linear components in the module case, and is left exact.
2. By lem-weil-pbc-module-sheaves-colimits-forgetful, forgetting the module action
   preserves cokernels, so a module epimorphism is an abelian-sheaf epimorphism.
   Abelian sheafification exists on the small site. The abelian case needs no forgetting.
3. By lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective, such epimorphisms
   locally lift every section. Forgetting operations gives local surjectivity of
   the underlying set sheaves. By lem-weil-pbc-site-sheaf-sets-epi-locally-surjective
   their morphism is an epimorphism of sheaves of sets.
4. Clause 2 of det-pe-wcb-projective applies to `Spec D` because `D` is w-contractible.
   It makes the map on sections surjective, also as a group or module homomorphism.
5. Apply steps 1 and 4 to any short exact sequence. Evaluation preserves the kernel
   and the surjection, hence the full short exact sequence. Equivalently, both additive
   functors preserve finite limits and finite colimits. -/
theorem wContractible_sections_exact
    (X : Scheme.{t}) (D : Type t) [CommRing D] [IsWContractibleRing D]
    (f : Spec (CommRingCat.of D) ⟶ X) [WeaklyEtale f]
    (R : Sheaf (topology X) RingCat.{u}) :
    PreservesFiniteLimits
      ((sheafSections (topology X) AddCommGrpCat.{max v (t + 1)}).obj
        (op (ProEt.mk f))) ∧
    PreservesFiniteColimits
      ((sheafSections (topology X) AddCommGrpCat.{max v (t + 1)}).obj
        (op (ProEt.mk f))) ∧
    PreservesFiniteLimits
      (SheafOfModules.evaluation.{max v (t + 1)} R (op (ProEt.mk f))) ∧
    PreservesFiniteColimits
      (SheafOfModules.evaluation.{max v (t + 1)} R (op (ProEt.mk f))) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
