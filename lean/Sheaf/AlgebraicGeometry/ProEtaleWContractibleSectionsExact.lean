/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q86 and H6
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective

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
   the underlying set sheaves.
4. The proved source theorem `isWeaklyContractible_of_iso` applies to `Spec D` in
   any section universe. It makes each locally surjective set-sheaf map surjective
   on sections, also as a group or module homomorphism. This is the projectivity
   argument of det-pe-wcb-projective, with no restriction on the section universe.
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
  have : EssentiallySmall.{max v (t + 1)} X.ProEt := essentiallySmallSelf _
  have : HasSheafify
      ((equivSmallModel.{max v (t + 1)} X.ProEt).inverse.inducedTopology (topology X))
      AddCommGrpCat.{max v (t + 1)} :=
    instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
      ((equivSmallModel.{max v (t + 1)} X.ProEt).inverse.inducedTopology (topology X))
      AddCommGrpCat.{max v (t + 1)}
  have : HasSheafify (topology X) AddCommGrpCat.{max v (t + 1)} :=
    hasSheafifyEssentiallySmallSite.{t, max v (t + 1), t + 1,
      (max v (t + 1)) + 1, max v (t + 1)} (topology X) _
  have : (topology X).WEqualsLocallyBijective AddCommGrpCat.{max v (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, max v (t + 1),
      t + 1, (max v (t + 1)) + 1, max v (t + 1), max v (t + 1), max v (t + 1)}
      (topology X)
  let W := ProEt.mk f
  let evAb := (sheafSections (topology X) AddCommGrpCat.{max v (t + 1)}).obj (op W)
  let evMod := SheafOfModules.evaluation.{max v (t + 1)} R (op W)
  have hW : (topology X).IsWeaklyContractible.{max v (t + 1)} W :=
    isWeaklyContractible_of_iso (R := CommRingCat.of D) (Iso.refl _)
  have : evAb.Additive := ⟨by intros; rfl⟩
  have : evMod.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits evAb := by
    change PreservesFiniteLimits
      (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op W))
    infer_instance
  have : evAb.PreservesEpimorphisms := by
    constructor
    intro M N g hg
    have : Sheaf.IsLocallySurjective g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max v (t + 1)} g).mpr hg
    let g' := (sheafCompose (topology X)
      (CategoryTheory.forget AddCommGrpCat.{max v (t + 1)})).map g
    exact (AddCommGrpCat.epi_iff_surjective (evAb.map g)).mpr (hW g' inferInstance)
  have : evAb.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels evAb
  have : PreservesFiniteColimits evAb :=
    Functor.preservesFiniteColimits_of_preservesHomology evAb
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{max v (t + 1)} R) :=
    (moduleSheaves_colimits_forgetful R).2.2.1
  have : evMod.PreservesEpimorphisms := by
    constructor
    intro M N g hg
    let gAb := (SheafOfModules.toSheaf R).map g
    have : Epi gAb := inferInstance
    exact (ModuleCat.epi_iff_surjective (evMod.map g)).mpr
      ((AddCommGrpCat.epi_iff_surjective (evAb.map gAb)).mp inferInstance)
  have : evMod.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels evMod
  exact ⟨inferInstance, inferInstance, inferInstance,
    Functor.preservesFiniteColimits_of_preservesHomology evMod⟩

end AlgebraicGeometry.Scheme.ProEt
