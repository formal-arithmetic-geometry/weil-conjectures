/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
import Sheaf.CategoryTheory.ContinuousCocontinuousRingedRestriction
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat
import Sheaf.CategoryTheory.QuotientJShriek

/-!
# Free sheaf generators for restriction on ringed sites

Source: Stacks Project, Modules on Sites, Tags 0797 and 03EW(3)
(blueprint: lem-trf-ringed-site-restriction-generator-data).

The constructions below name the sheafified free representables, their evaluation maps,
the canonical presentation, and the class of their small sums appearing in this lemma.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace SheafOfModules

section Generators

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- The sheaf `E_U = (R[h_U])♯`. Mathlib's free presheaf has section module
`R(V)[Hom(V,U)]`, with restrictions sending `e_a` to `e_(b ≫ a)` along `b`.
Source: Stacks Project, Tag 0797, evaluation computation, and Tag 03CY
(blueprint: lem-trf-ringed-site-restriction-generator-data). -/
noncomputable def freeYonedaSheaf (U : C) : ringedSiteModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (yoneda.obj U))

/-- Evaluation at the image of the identity basis vector under the sheafification unit.
Source: Stacks Project, Tag 0797, evaluation computation
(blueprint: lem-trf-ringed-site-restriction-generator-data). -/
noncomputable def freeYonedaSheafEvaluation (U : C) (M : ringedSiteModules.{u} R)
    (f : freeYonedaSheaf R U ⟶ M) : M.val.obj (op U) :=
  f.val.app (op U)
    ((toSheafify J ((PresheafOfModules.free R.obj).obj (yoneda.obj U)).presheaf).app
      (op U) (ModuleCat.freeMk (𝟙 U)))

/-- The morphism associated to a section, obtained from the free Yoneda bijection
and module sheafification. Its data are the existing adjunction inverse, with no choice.
Source: Stacks Project, Tags 0797 and 03CY
(blueprint: lem-trf-ringed-site-restriction-generator-data). -/
noncomputable def freeYonedaSheafSection (U : C) (M : ringedSiteModules.{u} R)
    (s : M.val.obj (op U)) : freeYonedaSheaf R U ⟶ M :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
    (PresheafOfModules.freeYonedaEquiv.symm s)

/-- The canonical map from the sum indexed by all object-section pairs, whose components
are the morphisms associated to those sections.
Source: Stacks Project, Tag 03EW(3) and its proof
(blueprint: lem-trf-ringed-site-restriction-generator-data). -/
noncomputable def freeYonedaSheafPresentation (M : ringedSiteModules.{u} R) :
    (∐ fun m : M.val.Elements ↦ freeYonedaSheaf R m.1.unop) ⟶ M :=
  Sigma.desc (fun m : M.val.Elements ↦ freeYonedaSheafSection R m.1.unop M m.2)

/-- The class of objects isomorphic to small sums of the specified free sheaf generators.
Source: Stacks Project, Tag 0797, reduction to partial adjoints
(blueprint: lem-trf-ringed-site-restriction-generator-data). -/
def IsFreeYonedaSheafSum (M : ringedSiteModules.{u} R) : Prop :=
  ∃ (I : Type u) (U : I → C), Nonempty (M ≅ ∐ fun i : I ↦ freeYonedaSheaf R (U i))

/-- The generator clauses for one of the two ringed sites in the lemma: bijective natural
identity-generator evaluation, the canonical epimorphic presentation with its component
normalization.
Smallness is enforced by `C : Type u`, the section universe `u`, and `I : Type u`.
Source: Stacks Project, Tags 0797 and 03EW(3)
(blueprint: lem-trf-ringed-site-restriction-generator-data). -/
def freeYonedaSheafGeneratorProperties : Prop :=
  (∀ (U : C) (M : ringedSiteModules.{u} R),
    Function.Bijective (freeYonedaSheafEvaluation R U M)) ∧
  (∀ (U : C) (M N : ringedSiteModules.{u} R)
    (f : freeYonedaSheaf R U ⟶ M) (h : M ⟶ N),
    freeYonedaSheafEvaluation R U N (f ≫ h) =
      h.val.app (op U) (freeYonedaSheafEvaluation R U M f)) ∧
  (∀ M : ringedSiteModules.{u} R,
    Epi (freeYonedaSheafPresentation R M) ∧
      ∀ m : M.val.Elements,
        freeYonedaSheafEvaluation R m.1.unop M
          (Sigma.ι (fun n : M.val.Elements ↦ freeYonedaSheaf R n.1.unop) m ≫
            freeYonedaSheafPresentation R M) = m.2)

/-- The zero, finite-sum and epimorphic-generation clauses for the class of small sums.
Source: Stacks Project, Tags 0797 and 03EW(3)
(blueprint: lem-trf-ringed-site-restriction-generator-data). -/
def freeYonedaSheafSumProperties : Prop :=
  IsFreeYonedaSheafSum R (0 : ringedSiteModules.{u} R) ∧
  (∀ (I : Type u) (_ : Finite I) (M : I → ringedSiteModules.{u} R),
    (∀ i : I, IsFreeYonedaSheafSum R (M i)) → IsFreeYonedaSheafSum R (∐ M)) ∧
  (∀ M : ringedSiteModules.{u} R,
    ∃ P : ringedSiteModules.{u} R, IsFreeYonedaSheafSum R P ∧
      ∃ q : P ⟶ M, Epi q)

end Generators

/-- Restriction of module sheaves along a continuous site functor, using the identity
structural map on the restricted ring; its sections, action and maps are precomposition.
Source: Stacks Project, Tag 0797 and Sites, Tag 00WW
(blueprint: lem-trf-ringed-site-restriction-generator-data). -/
noncomputable def siteModuleRestriction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [Functor.IsContinuous F J K] (R : Sheaf K RingCat.{u}) :
    ringedSiteModules.{u} R ⥤
      ringedSiteModules.{u} ((F.sheafPushforwardContinuous RingCat J K).obj R) :=
  pushforward (F := F) (𝟙 ((F.sheafPushforwardContinuous RingCat J K).obj R))

/-- Continuous cocontinuous restriction is additive and exact; the sheafified free
representables on both sites have the stated generator properties. Small sums on the
source and of their images on the target give the two natural evaluation bijections.

Source: Stacks Project, Tags 0797 and 03EW(3)
(blueprint: lem-trf-ringed-site-restriction-generator-data).

Proof:
1. Continuity makes ring and module precomposition sheaves by
   `lem-weil-pbc-site-continuous-pushforward-sheaf`. The sectionwise action defines
   restriction as in `def-weil-sheaf-of-modules-category`. Addition and kernels are
   sectionwise, so restriction is additive and preserves kernels.
2. `lem-weil-pbc-continuous-cocontinuous-ringed-restriction` makes this very restriction
   a left adjoint. Cokernels exist by `lem-weil-pbc-module-sheaves-colimits-forgetful`.
   Adjunction identifies maps out of the restricted cokernel with maps annihilating
   the restricted morphism, so restriction preserves cokernels, hence is exact.
3. For a section `s`, send `sum r_a e_a` to `sum r_a M(a)(s)`. Semilinearity proves
   compatibility with restriction. Naturality forces this formula from the value of
   `e_id`, giving `lem-weil-pbc-free-yoneda-presheaf-module`. Unique extension by
   `def-weil-presheaf-modules-sheafification` gives the sheaf evaluation bijection.
   Postcomposition by `h` sends its value to `h_U(s)`, proving naturality.
4. `def-weil-extension-by-zero-presheaf` and the specified construction in
   `lem-pc-sites-modules-j-shriek-flat` identify these generators with `j_! R_U`.
   Apply `lem-pc-sites-modules-quotient-j-shriek`. Its component bijections differ
   from evaluation, if at all, by bijective reindexing of each set of sections.
   Thus the canonically normalized presentation is also epic, on both sites.
5. `lem-weil-pbc-module-sheaves-colimits-forgetful` supplies the sums. Objects,
   arrows and sections have universe `u`, so the object-section pairs and every
   sum index are small (`def-weil-size-convention`). The empty sum is zero;
   flattening a finite sum of small sums gives another small sum. The presentation
   in step 4 proves epimorphic generation, including closure under isomorphism.
6. A map out of a sum is its family of components. Apply step 3 on the source,
   identify `(TN)(U_i)` with `N(F(U_i))`, and apply step 3 backwards on the target.
   Coproduct universality assembles the second bijection. Postcomposition acts
   on each section by `h_(F(U_i))`, proving both naturality formulas. Empty families
   give the unique maps from zero and the singleton empty product. -/
theorem ringedSiteRestrictionGeneratorData
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [Functor.IsContinuous F J K] [Functor.IsCocontinuous F J K]
    (R : Sheaf K RingCat.{u})
    (_hcomm : ∀ (V : Dᵒᵖ) (a b : R.obj.obj V), a * b = b * a) :
    (siteModuleRestriction J K F R).Additive ∧
    PreservesFiniteLimits (siteModuleRestriction J K F R) ∧
    PreservesFiniteColimits (siteModuleRestriction J K F R) ∧
    freeYonedaSheafGeneratorProperties R ∧
    freeYonedaSheafGeneratorProperties
      ((F.sheafPushforwardContinuous RingCat J K).obj R) ∧
    freeYonedaSheafSumProperties
      ((F.sheafPushforwardContinuous RingCat J K).obj R) ∧
    ∀ (I : Type u) (U : I → C),
      ∃ e₁ : ∀ N : ringedSiteModules.{u} R,
        ((∐ fun i : I ↦ freeYonedaSheaf
          ((F.sheafPushforwardContinuous RingCat J K).obj R) (U i)) ⟶
            (siteModuleRestriction J K F R).obj N) ≃
          (∀ i : I, N.val.obj (op (F.obj (U i)))),
      ∃ e₂ : ∀ N : ringedSiteModules.{u} R,
        (∀ i : I, N.val.obj (op (F.obj (U i)))) ≃
          ((∐ fun i : I ↦ freeYonedaSheaf R (F.obj (U i))) ⟶ N),
        (∀ (N : ringedSiteModules.{u} R)
          (f : (∐ fun i : I ↦ freeYonedaSheaf
            ((F.sheafPushforwardContinuous RingCat J K).obj R) (U i)) ⟶
              (siteModuleRestriction J K F R).obj N) (i : I),
          e₁ N f i = freeYonedaSheafEvaluation
            ((F.sheafPushforwardContinuous RingCat J K).obj R) (U i)
            ((siteModuleRestriction J K F R).obj N)
            (Sigma.ι (fun j : I ↦ freeYonedaSheaf
              ((F.sheafPushforwardContinuous RingCat J K).obj R) (U j)) i ≫ f)) ∧
        (∀ (N : ringedSiteModules.{u} R)
          (g : (∐ fun i : I ↦ freeYonedaSheaf R (F.obj (U i))) ⟶ N) (i : I),
          (e₂ N).symm g i = freeYonedaSheafEvaluation R (F.obj (U i)) N
            (Sigma.ι (fun j : I ↦ freeYonedaSheaf R (F.obj (U j))) i ≫ g)) ∧
        (∀ (N N' : ringedSiteModules.{u} R) (h : N ⟶ N')
          (f : (∐ fun i : I ↦ freeYonedaSheaf
            ((F.sheafPushforwardContinuous RingCat J K).obj R) (U i)) ⟶
              (siteModuleRestriction J K F R).obj N),
          e₁ N' (f ≫ (siteModuleRestriction J K F R).map h) =
            fun i : I ↦ h.val.app (op (F.obj (U i))) (e₁ N f i)) ∧
        (∀ (N N' : ringedSiteModules.{u} R) (h : N ⟶ N')
          (s : ∀ i : I, N.val.obj (op (F.obj (U i)))),
          e₂ N' (fun i : I ↦ h.val.app (op (F.obj (U i))) (s i)) = e₂ N s ≫ h) := by
  sorry

end SheafOfModules
