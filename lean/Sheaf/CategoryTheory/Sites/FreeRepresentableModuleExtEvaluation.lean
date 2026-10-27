/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison

/-!
# Ext from a free representable module and object cohomology

Source: Stacks Project, Cohomology on Sites, Tags 07AC and 03FD; Modules on Sites,
Tags 03CY and 03DI (blueprint: lem-trf-free-representable-module-ext-evaluation).

The free presheaf and its sheafification are the existing Mathlib constructions.
The last cohomology functor is right-derived evaluation in abelian sheaves, as in
part (2) of the site/cohomology convention. Commutativity is expressed on the
values of the ring sheaf, keeping Mathlib's existing category of module sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Free representable module Ext is derived evaluation, naturally and with the
specified identity-generator and injective-resolution normalizations.

Source: Stacks Project, Cohomology on Sites, Tags 07AC and 03FD; Modules on Sites,
Tags 03CY, 03DI and 03EJ
(blueprint: lem-trf-free-representable-module-ext-evaluation).

Proof:
1. Apply lem-weil-pbc-ring-sheaves-grothendieck in the common universe, followed by
   lem-sp-grothendieck-enough-injectives. Hence every module sheaf has an injective
   resolution. By lem-weil-pbc-ext-via-injective-resolution, Ext is a subquotient of
   the small Hom groups of that resolution, so HasExt holds in the same universe.
2. Compose the sheafification adjunction of def-weil-presheaf-modules-sheafification
   with lem-weil-pbc-free-yoneda-presheaf-module. The composite evaluates alpha eta
   at the identity basis vector. Its inverse sends r e_a to r times the restriction
   of the section along a. Evaluation and precomposition are additive; naturality
   is the equality b_U(alpha eta(e_id)) = (b alpha eta)(e_id). These maps therefore
   assemble into the additive natural isomorphism theta below.
3. Apply lem-sc-ext-right-derived-cocycle-comparison to theta and invert its
   comparison. Naturality of theta at every differential identifies the Hom and
   evaluated resolution complexes. A represented Ext cocycle s is sent to the
   class of theta(s), exactly the cycle equation below. The comparison is natural
   and independent of the resolution. In degree zero naturality at the augmentation
   identifies the induced map with theta on the kernel, giving the displayed formula.
4. Apply lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison, using its
   general Grothendieck-topology interface. It gives y, normalized at degree zero
   and on every augmentation-compatible lift to an abelian injective resolution.
   This is the canonical comparison with abelian object cohomology. Compose with x
   for the asserted Ext/cohomology identification. Forgotten module injectives need
   only be evaluation-acyclic; neither their abelian injectivity nor coefficient
   flatness over the integers is used. -/
theorem free_representable_module_ext_evaluation
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{u})
    (_hcomm : ∀ (V : Cᵒᵖ) (a b : R.obj.obj V), a * b = b * a) (U : C) :
    ∃ (_hI : EnoughInjectives (ringedSiteModules.{u} R))
      (_hExt : HasExt.{u} (ringedSiteModules.{u} R)),
      ∃ θ : (preadditiveCoyoneda.obj (op ((PresheafOfModules.sheafification (𝟙 R.obj)).obj
        ((PresheafOfModules.free R.obj).obj (yoneda.obj U))))) ≅ (SheafOfModules.toSheaf R ⋙
        (sheafToPresheaf J AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))),
        (∀ (N : ringedSiteModules.{u} R) (α : ((PresheafOfModules.sheafification (𝟙 R.obj)).obj
          ((PresheafOfModules.free R.obj).obj (yoneda.obj U))) ⟶ N),
          θ.hom.app N α =
            (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) α).app (op U)
              (ModuleCat.freeMk (𝟙 U))) ∧
        (∀ (N : ringedSiteModules.{u} R) (s : N.val.obj (op U))
          (V : C) (a : V ⟶ U) (r : R.obj.obj (op V)),
          (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
            (θ.inv.app N s)).app (op V) (r • ModuleCat.freeMk a) =
              r • N.val.map a.op s) ∧
        ∃ x : ∀ q : ℕ, (Abelian.extFunctor q).obj (op ((PresheafOfModules.sheafification (𝟙
          R.obj)).obj ((PresheafOfModules.free R.obj).obj (yoneda.obj U)))) ≅
          (SheafOfModules.toSheaf R ⋙ (sheafToPresheaf J AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ
          AddCommGrpCat.{u}).obj (op U))).rightDerived q,
          ∃ y : ∀ q : ℕ, (SheafOfModules.toSheaf R ⋙ (sheafToPresheaf J AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).rightDerived q ≅
            SheafOfModules.toSheaf R ⋙ (sheafToPresheaf J AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ
            AddCommGrpCat.{u}).obj (op U)).rightDerived q,
            (∀ (M : ringedSiteModules.{u} R) (I : InjectiveResolution M) (q : ℕ)
              (s : ((PresheafOfModules.sheafification (𝟙 R.obj)).obj ((PresheafOfModules.free
                R.obj).obj (yoneda.obj U))) ⟶ I.cocomplex.X q)
              (hs : s ≫ I.cocomplex.d q (q + 1) = 0)
              (c : (((SheafOfModules.toSheaf R ⋙ (sheafToPresheaf J AddCommGrpCat.{u} ⋙
                (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).mapHomologicalComplex (.up ℕ)).obj
                I.cocomplex).cycles q)
              (_hc : (((SheafOfModules.toSheaf R ⋙ (sheafToPresheaf J AddCommGrpCat.{u} ⋙
                (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).mapHomologicalComplex (.up ℕ)).obj
                I.cocomplex).iCycles q c = θ.hom.app (I.cocomplex.X q) s),
              (I.isoRightDerivedObj (SheafOfModules.toSheaf R ⋙ (sheafToPresheaf J
                AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))) q).hom
                ((x q).hom.app M (I.extMk s (q + 1) rfl hs)) =
                  (((SheafOfModules.toSheaf R ⋙ (sheafToPresheaf J AddCommGrpCat.{u} ⋙ (evaluation
                    Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).mapHomologicalComplex (.up ℕ)).obj
                    I.cocomplex).homologyπ q c) ∧
            (∀ (M : ringedSiteModules.{u} R) (α : ((PresheafOfModules.sheafification (𝟙
              R.obj)).obj ((PresheafOfModules.free R.obj).obj (yoneda.obj U))) ⟶ M),
              (x 0).hom.app M (Abelian.Ext.mk₀ α) =
                (SheafOfModules.toSheaf R ⋙ (sheafToPresheaf J AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ
                  AddCommGrpCat.{u}).obj (op U))).toRightDerivedZero.app M (θ.hom.app M α)) ∧
            ((SheafOfModules.toSheaf R ⋙ (sheafToPresheaf J AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ
              AddCommGrpCat.{u}).obj (op U))).toRightDerivedZero ≫ (y 0).hom =
              Functor.whiskerLeft (SheafOfModules.toSheaf R) (sheafToPresheaf J AddCommGrpCat.{u}
                ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).toRightDerivedZero) ∧
            ∀ (M : ringedSiteModules.{u} R) (I : InjectiveResolution M)
              (K : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
              (φ : ((SheafOfModules.toSheaf R).mapHomologicalComplex (.up ℕ)).obj
                I.cocomplex ⟶ K.cocomplex)
              (_hφ : (SheafOfModules.toSheaf R).map (I.ι.f 0) ≫ φ.f 0 = K.ι.f 0) (q : ℕ),
              (y q).hom.app M ≫ (K.isoRightDerivedObj (sheafToPresheaf J AddCommGrpCat.{u} ⋙
                (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).hom =
                (I.isoRightDerivedObj (SheafOfModules.toSheaf R ⋙ (sheafToPresheaf J
                  AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))) q).hom ≫
                  HomologicalComplex.homologyMap ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
                    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex (.up ℕ)
                    |>.map φ) q := by
  sorry

end CategoryTheory
