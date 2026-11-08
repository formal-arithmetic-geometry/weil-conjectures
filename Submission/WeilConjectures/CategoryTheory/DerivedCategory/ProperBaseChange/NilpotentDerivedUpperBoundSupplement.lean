/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.Ring.RingHomExtensionDefsSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Submission.WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import Submission.WeilConjectures.Algebra.Homology.TensorRestrictExtendScalarsModule
import Mathlib.Algebra.Module.Torsion.Basic
import Submission.WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Nilpotent derived reduction detects an upper cohomological bound

Source: Stacks Project, More on Algebra, Tag 0H75,
lemma-check-tor-dimension-modulo-nilpotent, upper-bound-only adaptation used by Tag 09AR
(blueprint: lem-weil-pbc-nilpotent-derived-upper-bound).

Ordinary modules are encoded on the existing one-object site with bottom topology.
The additive scalar-extension functor and its left derived functor are specified by
exactly the object formula, morphism formula and universal property supplied by
`SheafOfModules.derivedChangeOfRings`; no choice of a particular model is required.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- The one-object site is explicitly equivalent to ordinary modules.
private abbrev point : (Discrete PUnit.{u + 1})ᵒᵖ := Opposite.op ⟨PUnit.unit⟩

private noncomputable abbrev pointEval (A : Type u) [CommRing A] :
    RingSiteModules A ⥤ ModuleCat.{u} A :=
  SheafOfModules.evaluation
    ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf A)) point

private noncomputable def pointConstant (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ RingSiteModules A where
  obj M := ⟨{ obj := fun _ ↦ M
              map := fun _ ↦ ModuleCat.ofHom (LinearMap.id) }, Presheaf.isSheaf_bot _⟩
  map f := ⟨{ app := fun _ ↦ f }⟩

private noncomputable def pointUnitIso {A : Type u} [CommRing A]
    (M : RingSiteModules A) : M ≅ (pointConstant A).obj ((pointEval A).obj M) := by
  let e : M.val ≅ ((pointConstant A).obj ((pointEval A).obj M)).val :=
    PresheafOfModules.isoMk (fun U ↦ by
      obtain rfl : U = point := Subsingleton.elim _ _
      exact Iso.refl _) (by
        intro U V g
        obtain rfl : U = point := Subsingleton.elim _ _
        obtain rfl : V = point := Subsingleton.elim _ _
        obtain rfl : g = 𝟙 point := Subsingleton.elim _ _
        ext x
        simp [pointConstant, pointEval]
        rfl)
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso e

private noncomputable def pointEquivalence (A : Type u) [CommRing A] :
    RingSiteModules A ≌ ModuleCat.{u} A where
  functor := pointEval A
  inverse := pointConstant A
  unitIso := NatIso.ofComponents pointUnitIso (by
    intro M N f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    obtain rfl : U = point := Subsingleton.elim _ _
    rfl)
  counitIso := Iso.refl _

private noncomputable local instance pointEval_isEquivalence (A : Type u) [CommRing A] :
    (pointEval A).IsEquivalence := (pointEquivalence A).isEquivalence_functor

private noncomputable local instance pointConstant_isEquivalence (A : Type u) [CommRing A] :
    (pointConstant A).IsEquivalence := (pointEquivalence A).isEquivalence_inverse

private local instance pointConstant_additive (A : Type u) [CommRing A] :
    (pointConstant A).Additive where
  map_add := by intros; rfl

private local instance pointEval_additive (A : Type u) [CommRing A] :
    (pointEval A).Additive where
  map_add := by intros; rfl

private local instance pointExtend_additive
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B) :
    (ModuleCat.extendScalars.{u, u, u} ρ).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} ρ).left_adjoint_additive

-- The filtration argument for ordinary modules, before transporting it to the site.
end DerivedCategory
