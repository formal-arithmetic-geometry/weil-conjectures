/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitEvaluation

/-! # Direct sums of quasi-coherent modules on an algebraic stack

Source: Stacks Project, stacks-sheaves.tex, Tag 06WN(1); stacks-properties.tex,
Tag 04YC(2),(3), and the finite-support descent argument for sections
(blueprint: lem-sfb-stack-qcoh-direct-sums).

The coproduct assertions use colimiting cofans, including their summand maps.
Thus the scheme-test and section assertions specify the canonical comparisons.
Global sections are compatible families with their pointwise module structure over
`moduliGlobalSectionsRing (moduliStructureSheaf C hC)`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory

/-- Evaluate a compatible family of regular functions at a test object.
Source: Stacks 06TV, compatible-family sections
(blueprint: lem-sfb-stack-qcoh-direct-sums). -/
def moduliGlobalScalarEvaluation {S : Scheme.{u}}
    (C : BasedCategory.{v, w} (Over S)) (hC : IsFibredInGroupoids C) (x : C.objᵒᵖ) :
    moduliGlobalSectionsRing (moduliStructureSheaf C hC) →+*
      (moduliModuleRings C hC).obj.obj x where
  toFun r := r.1 x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Each test value is a module over the ring of global regular functions.
Source: Stacks 06TV, pointwise scalar multiplication
(blueprint: lem-sfb-stack-qcoh-direct-sums). -/
abbrev moduliSectionValue {S : Scheme.{u}} {C : BasedCategory.{v, w} (Over S)}
    {hC : IsFibredInGroupoids C}
    (M : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC)) (x : C.objᵒᵖ) :
    ModuleCat.{max (u + 1) v w}
      (moduliGlobalSectionsRing (moduliStructureSheaf C hC)) :=
  (ModuleCat.restrictScalars (moduliGlobalScalarEvaluation C hC x)).obj (M.val.obj x)

/-- Compatible section families form a submodule of the product of test values.
The carrier is exactly the compatible-family definition of global sections.
Source: Stacks 06TV, 06W6 (blueprint: lem-sfb-stack-qcoh-direct-sums). -/
def moduliSectionsSubmodule {S : Scheme.{u}} {C : BasedCategory.{v, w} (Over S)}
    {hC : IsFibredInGroupoids C}
    (M : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC)) :
    Submodule (moduliGlobalSectionsRing (moduliStructureSheaf C hC))
      (∀ x : C.objᵒᵖ, moduliSectionValue M x) where
  carrier := {s | ∀ ⦃x y : C.objᵒᵖ⦄ (f : x ⟶ y), M.val.map f (s x) = s y}
  zero_mem' := by intro x y f; exact map_zero (M.val.map f).hom
  add_mem' := by
    intro s t hs ht x y f
    change M.val.map f (s x + t x) = s y + t y
    rw [(M.val.map f).hom.map_add, hs f, ht f]
  smul_mem' := by
    intro r s hs x y f
    change M.val.map f (r.1 x • s x) = r.1 y • s y
    rw [M.val.map_smul, hs f]
    exact congrArg (fun a ↦ a • s y) (r.2 f)

/-- Global sections as modules over the actual compatible-family section ring.
Morphisms act on each test value by the original module map.
Source: Stacks 06TV, 06W6 (blueprint: lem-sfb-stack-qcoh-direct-sums). -/
def moduliModuleGlobalSections {S : Scheme.{u}}
    (C : BasedCategory.{v, w} (Over S)) (hC : IsFibredInGroupoids C) :
    ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC) ⥤
      ModuleCat.{max (u + 1) v w}
        (moduliGlobalSectionsRing (moduliStructureSheaf C hC)) where
  obj M := ModuleCat.of _ (moduliSectionsSubmodule M)
  map f := ModuleCat.ofHom
    { toFun := fun s ↦ ⟨fun x ↦ f.val.app x (s.1 x), by
        intro x y g
        rw [← PresheafOfModules.naturality_apply, s.2 g]⟩
      map_add' := by
        intro s t
        apply Subtype.ext
        funext x
        exact (f.val.app x).hom.map_add _ _
      map_smul' := by
        intro r s
        apply Subtype.ext
        funext x
        exact (f.val.app x).hom.map_smul (r.1 x) (s.1 x) }
  map_id M := by ext s x; rfl
  map_comp f g := by ext s x; rfl

/-- Arbitrary quasi-coherent coproducts are ambient module-sheaf coproducts;
scheme-test restriction preserves them, and on a quasi-compact stack so do global
sections, as modules over the ring of global functions.

Source: Stacks Project, Tag 06WN(1), Tag 04YC(2),(3), and finite-support descent
(blueprint: lem-sfb-stack-qcoh-direct-sums).

Proof:
1. Sheafify the sectionwise presheaf sum. The module sheafification adjunction
(lem-weil-pbc-module-sheaves-colimits-forgetful) gives its ambient coproduct cofan,
also for the empty family.
2. Restrict to each scheme slice using
lem-sfb-stack-quasi-coherent-scheme-restriction. Localization preserves colimits
(lem-sfb-fibred-fppf-ringed-inverse-image). The scheme equivalence
lem-sfb-scheme-big-fppf-quasicoherent-equivalence preserves ambient colimits, and
lem-weil-pbc-quasi-coherent-module-coproduct-closure makes the ordinary scheme sum
quasi-coherent. Consequently the ambient sum has local free presentations on every
slice, hence on the original site. Fullness gives its universal property in QCoh;
full faithfulness on slices gives exactly the restricted coproduct cofan.
3. Projections onto each summand recover its coordinate. Identify global sections
with maps out of the structure module by the compatible-family formula of
def-sfb-stack-quasi-coherent-algebra. The section comparison is therefore injective.
4. For a quasi-compact stack choose a quasi-compact smooth atlas using
def-sfb-stack-qcqs-morphism, then a finite affine open cover using
lem-weil-pbc-affine-opens-basis and def-weil-pbc-quasi-compact-scheme. By step 2
and lem-weil-pbc-quasi-coherent-module-colimit-evaluation, a section has finite
support on each affine chart. The union of these finitely many supports is finite.
Subtract the sum of its global coordinates on that union; it vanishes on the atlas.
5. By lem-sfb-smooth-atlas-module-descent, restriction of quasi-coherent module
maps to the atlas is faithful, with no condition on its relation space. Applied
to the map out of the structure module corresponding to the difference, this shows
the difference is zero, proving surjectivity.
6. All summand maps are linear, so this bijection is an isomorphism of modules
over the actual global section ring. Uniqueness in the coproduct universal property
makes the scheme and global comparisons natural in every family morphism. Empty
families, zero modules and the empty atlas obey the same argument. No separatedness,
quasi-separatedness, finiteness of the indexing set, or Noetherian hypothesis is used. -/
theorem moduli_qcoh_direct_sums {S : Scheme.{u}}
    (C : BasedCategory.{v, w} (Over S)) (hC : IsAlgebraicModuliStack C)
    (A : Type (max (u + 1) v w)) (F : A → ModuliQCoh C hC.1.1) :
    ∃ c : Cofan F,
      Nonempty (IsColimit c) ∧
      Nonempty (IsColimit
        ((SheafOfModules.isQuasicoherent (moduliModuleRings C hC.1.1)).ι.mapCocone c)) ∧
      (∀ (r : ModuliSchemeRestriction C hC.1.1) (x : C.obj),
        Nonempty (IsColimit ((r.restriction x).mapCocone c))) ∧
      (IsQuasiCompactModuli C → Nonempty (IsColimit
        (((SheafOfModules.isQuasicoherent (moduliModuleRings C hC.1.1)).ι ⋙
          moduliModuleGlobalSections C hC.1.1).mapCocone c))) := by
  sorry

end CategoryTheory
