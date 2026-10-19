/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Sheafified generators and relations for differentials

Source: Stacks Project, Modules on Sites, Tags 08TP, 04BK, 04BL and 04BN
(blueprint: lem-trf-sheafified-module-differentials-cokernel).

The representing property is stated for sheaf modules, rather than for all presheaf
modules. The relation source uses a disjoint union of the three generator sets: the
free module on this union is the direct sum of the three displayed free modules.

## Main statements

- `sheafified_differentials_cokernel`: the sheaf representing derivations is the
  sheafified sectionwise differential module, with its normalized isomorphism and
  common three-relation cokernel presentation.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open PresheafOfModules.DifferentialsConstruction

namespace CategoryTheory.SheafifiedDifferentials

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C]

/-- The three kinds of relation labels, with their sectionwise restriction maps.
Source: Stacks 08TP, displayed relation map
(blueprint: lem-trf-sheafified-module-differentials-cokernel). -/
def relationLabels (A B : Cᵒᵖ ⥤ CommRingCat.{max u v}) : Cᵒᵖ ⥤ Type (max u v) where
  obj U := (B.obj U × B.obj U) ⊕ ((B.obj U × B.obj U) ⊕ A.obj U)
  map f := TypeCat.ofHom (Sum.map (Prod.map (B.map f) (B.map f))
    (Sum.map (Prod.map (B.map f) (B.map f)) (A.map f)))
  map_id U := by
    ext x
    rcases x with ⟨a, b⟩ | (⟨a, b⟩ | h) <;> simp [Sum.map]
  map_comp f g := by
    ext x
    rcases x with ⟨a, b⟩ | (⟨a, b⟩ | h) <;> simp [Sum.map]

/-- The free presheaf on the differential symbols `[b]`.
Source: Stacks 08TP (blueprint: lem-trf-sheafified-module-differentials-cokernel). -/
noncomputable abbrev symbols (B : Cᵒᵖ ⥤ CommRingCat.{max u v}) :=
  PresheafOfModules.freeObj (R := B ⋙ forget₂ CommRingCat RingCat)
    (B ⋙ forget CommRingCat)

/-- The direct sum of the two pair-relation free modules and the base-relation free module.
Source: Stacks 08TP (blueprint: lem-trf-sheafified-module-differentials-cokernel). -/
noncomputable abbrev relations (A B : Cᵒᵖ ⥤ CommRingCat.{max u v}) :=
  PresheafOfModules.freeObj (R := B ⋙ forget₂ CommRingCat RingCat) (relationLabels A B)

/-- Ring-valued sheafification of a commutative-ring presheaf, forgetting commutativity.
Source: Stacks 08TP (blueprint: lem-trf-sheafified-module-differentials-cokernel). -/
noncomputable abbrev associatedRing (J : GrothendieckTopology C)
    (B : Cᵒᵖ ⥤ CommRingCat.{max u v}) : Sheaf J RingCat.{max u v} :=
  (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
    ((presheafToSheaf J CommRingCat.{max u v}).obj B)

/-- Module sheafification along the ring sheafification unit; its underlying abelian
sheaf is exactly abelian sheafification. The two local bijectivity structures simply
forget commutativity and have the same covering sieves.
Source: Stacks 03CY and 08TP
(blueprint: lem-trf-sheafified-module-differentials-cokernel). -/
noncomputable def associatedModules (J : GrothendieckTopology C)
    (B : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    PresheafOfModules.{max u v} (B ⋙ forget₂ CommRingCat RingCat) ⥤
      ringedSiteModules.{max u v} (associatedRing J B) :=
  let η := Functor.whiskerRight (CategoryTheory.toSheafify J B)
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})
  letI : Presheaf.IsLocallyInjective J η :=
    ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J (CategoryTheory.toSheafify J B) x y h⟩
  letI : Presheaf.IsLocallySurjective J η :=
    ⟨fun s ↦ Presheaf.imageSieve_mem J (CategoryTheory.toSheafify J B) s⟩
  PresheafOfModules.sheafification η

/-- Sheafification preserves the differential module, its universal derivation, and its
explicit three-relation cokernel presentation. A representing pair is quantified by
its defining universal property, so no choice of a second differential module is made.
Source: Stacks 08TP, 04BK, 04BL and 04BN
(blueprint: lem-trf-sheafified-module-differentials-cokernel).

Proof plan:
1. For `F = B[B]` and `E = B[(B × B) ⊔ (B × B) ⊔ A]`, define `r` by the three
   displayed formulas. Ring restrictions preserve all formulas. The sectionwise quotient
   is the existing Kähler module, with `[b]` sent to `d b` (07BK and 00RO).
2. Apply lem-pc-sites-module-sheafification-interface to `E`, `F` and the differential
   presheaf. Its underlying abelian functor is abelian sheafification, which preserves
   cokernels by lem-weil-pbc-sheafification-exact. Module cokernels have those underlying
   abelian cokernels by def-weil-sheaf-of-modules-category.
3. By lem-pc-sites-sheafification-underlying-sets and
   lem-weil-pbc-site-sheafification-sections-local, the ring units and their binary
   products are set sheafifications: lift two sections on a common covering refinement,
   and compare lifts on a further refinement using the site axioms.
4. Free linear extension and the module-sheafification adjunction identify the sheafified
   free terms with the free sheaf modules on the sheafified generator sets. Maps agree
   if they agree on the original generators, so the sheafified relation map has exactly
   the additivity, Leibniz and base-annihilation formulas above.
5. The quotient generator map therefore gives the sheaf derivation `d`. Any sheaf
   derivation into `N` extends uniquely from the free symbols, kills each of the three
   relation types and descends uniquely through the cokernel. This is precisely the
   representing property (04BL).
6. For any other representing pair, apply the two universal properties. The resulting
   maps are inverse because their composites fix the universal derivations. Their values
   on the original sectionwise differentials give the asserted normalization. Transport
   of the colimit along this unique isomorphism gives the common cokernel presentation.
-/
theorem sheafified_differentials_cokernel
    (J : GrothendieckTopology C) {A B : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : A ⟶ B) :
    ∃ (r : relations A B ⟶ symbols B)
      (p : symbols B ⟶ relativeDifferentials' φ),
      (∀ (U : Cᵒᵖ) (a b : B.obj U),
        r.app U (ModuleCat.freeMk (Sum.inl (a, b))) =
          ModuleCat.freeMk (a + b) - ModuleCat.freeMk a - ModuleCat.freeMk b) ∧
      (∀ (U : Cᵒᵖ) (f g : B.obj U),
        r.app U (ModuleCat.freeMk (Sum.inr (Sum.inl (f, g)))) =
          ModuleCat.freeMk (f * g) - g • ModuleCat.freeMk f - f • ModuleCat.freeMk g) ∧
      (∀ (U : Cᵒᵖ) (h : A.obj U),
        r.app U (ModuleCat.freeMk (Sum.inr (Sum.inr h))) = ModuleCat.freeMk (φ.app U h)) ∧
      (∀ (U : Cᵒᵖ) (b : B.obj U),
        p.app U (ModuleCat.freeMk b) = (derivation' φ).d b) ∧
      (∃ h : (associatedModules J B).map r ≫ (associatedModules J B).map p = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ ((associatedModules J B).map p) h))) ∧
      ∃ d : ((associatedModules J B).obj (relativeDifferentials' φ)).val.Derivation'
          (sheafifyMap J φ),
        (∀ (U : Cᵒᵖ) (b : B.obj U),
          d.d ((CategoryTheory.toSheafify J B).app U b) =
            (CategoryTheory.toSheafify J (relativeDifferentials' φ).presheaf).app U
              ((derivation' φ).d b)) ∧
        (∀ (N : ringedSiteModules.{max u v} (associatedRing J B))
          (D : N.val.Derivation' (sheafifyMap J φ)),
          ∃! α : (associatedModules J B).obj (relativeDifferentials' φ) ⟶ N,
            d.postcomp α.val = D) ∧
        (∀ (M : ringedSiteModules.{max u v} (associatedRing J B))
          (dM : M.val.Derivation' (sheafifyMap J φ)),
          (∀ (N : ringedSiteModules.{max u v} (associatedRing J B))
            (D : N.val.Derivation' (sheafifyMap J φ)),
            ∃! α : M ⟶ N, dM.postcomp α.val = D) →
          ∃! e : (associatedModules J B).obj (relativeDifferentials' φ) ≅ M,
            d.postcomp e.hom.val = dM ∧
            (∀ (U : Cᵒᵖ) (b : B.obj U),
              e.hom.val.app U
                ((CategoryTheory.toSheafify J (relativeDifferentials' φ).presheaf).app U
                  ((derivation' φ).d b)) =
                dM.d ((CategoryTheory.toSheafify J B).app U b)) ∧
            ∃ h : (associatedModules J B).map r ≫
                ((associatedModules J B).map p ≫ e.hom) = 0,
              Nonempty (IsColimit
                (CokernelCofork.ofπ ((associatedModules J B).map p ≫ e.hom) h))) := by
  sorry

end CategoryTheory.SheafifiedDifferentials
