/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Fixed-ring module sheaves and modules over the constant ring sheaf

Source: Stacks Project, Modules on Sites, Tag 03CY, and its constant-ring specialization
on arbitrary covering-sieve topologies (blueprint: lem-cbc-constant-ring-module-sheaves).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type (max u v)) [CommRing Λ]

set_option backward.isDefEq.respectTransparency false in
/-- Restrict scalars along the constant-ring sheafification unit, retaining the underlying
abelian presheaf. Source: Stacks Tag 03CY, constant-ring specialization
(blueprint: lem-cbc-constant-ring-module-sheaves). -/
def constantRingModuleRestrictionPresheaf
    (M : ringedSiteModules.{max u v}
      ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ))) :
    Cᵒᵖ ⥤ ModuleCat.{max u v} Λ :=
  let P := (PresheafOfModules.restrictScalars
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).obj M.val
  { obj := P.obj
    map := fun f ↦ P.map f
    map_id := fun X ↦ by ext x; exact congrArg (fun f ↦ f x) (P.map_id X)
    map_comp := fun f g ↦ by
      ext x
      exact P.map_comp_apply f g x }

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along the unit, as a functor into fixed-ring module-valued sheaves.
The sheaf condition is reflected by forgetting module structure to abelian groups.
Source: Stacks Tag 03CY (blueprint: lem-cbc-constant-ring-module-sheaves). -/
def constantRingModuleRestriction :
    ringedSiteModules.{max u v}
      ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)) ⥤
        Sheaf J (ModuleCat.{max u v} Λ) where
  obj M := ⟨constantRingModuleRestrictionPresheaf J Λ M,
    Presheaf.isSheaf_of_isSheaf_comp J _
      (forget₂ (ModuleCat.{max u v} Λ) AddCommGrpCat.{max u v}) M.isSheaf⟩
  map f := { hom :=
    { app := fun X ↦ (ModuleCat.restrictScalars
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X).hom).map
          (f.val.app X)
      naturality := fun _ _ g ↦ by
        ext x
        exact PresheafOfModules.naturality_apply f.val g x } }

/-- The two requirements on an action on the original sections: semilinear restrictions
and extension of the given fixed-ring action along the sheafification unit.
Source: Stacks Tag 03CY (blueprint: lem-cbc-constant-ring-module-sheaves). -/
def IsConstantRingModuleActionExtension (N : Sheaf J (ModuleCat.{max u v} Λ))
    (m : ∀ X : Cᵒᵖ,
      Module (((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
        (N.obj.obj X)) : Prop :=
  (∀ (X Y : Cᵒᵖ) (f : X ⟶ Y)
    (s : ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
    (x : N.obj.obj X),
    N.obj.map f (@SMul.smul _ _ (m X).toSMul s x) =
      @SMul.smul _ _ (m Y).toSMul
        (((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.map f s)
        (N.obj.map f x)) ∧
  (∀ (X : Cᵒᵖ) (a : Λ) (x : N.obj.obj X),
    @SMul.smul _ _ (m X).toSMul
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X a) x = a • x)

/-- Restriction of scalars gives an additive equivalence. The inverse retains the abelian
sheaf and its maps. There is a unique extended action on the original sections, and every
fixed-ring linear natural map is linear for any such extended actions.

Source: Stacks Tag 03CY, constant-ring extension to arbitrary sieve sites
(blueprint: lem-cbc-constant-ring-module-sheaves).

Proof plan:
1. Fixed-ring module presheaves are modules over the constant ring presheaf. Matching tuples
form modules componentwise, so forgetting to abelian groups preserves and reflects the
covering-sieve limit condition.
2. Apply lem-cbc-sieve-module-sheafification, namely Mathlib's module-sheafification adjunction,
to the constant ring presheaf. On a sheaf N the underlying abelian sheafification unit is an
isomorphism: the universal property gives an inverse c, and uniqueness gives both inverse laws.
3. Transport the sheafified action by s * x = c(s * eta(x)). The additive bijection eta verifies
all module laws and naturality; its constant-ring linearity proves extension along the unit.
4. Fullness of scalar restriction lifts the identity between any two extensions. Its underlying
identity map is linear, which makes the two scalar actions equal.
5. Fullness likewise lifts every fixed-ring linear natural map, retaining its components and
proving linearity for the extended actions.
6. Restriction after extension is the original action. Uniqueness identifies extension after
restriction with the original sheaf-of-modules action. Identity underlying maps give both
natural inverse isomorphisms. Both functors preserve addition because their maps are unchanged.
No nonempty-site, nonzero-ring, fibre-product or subcanonicity hypothesis is used. -/
theorem constant_ring_module_sheaves :
    (∃ e : ringedSiteModules.{max u v}
        ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)) ≌
          Sheaf J (ModuleCat.{max u v} Λ),
      e.functor = constantRingModuleRestriction J Λ ∧
      e.functor.Additive ∧ e.inverse.Additive ∧
      e.inverse ⋙ SheafOfModules.toSheaf _ =
        sheafCompose J (forget₂ (ModuleCat.{max u v} Λ) AddCommGrpCat.{max u v})) ∧
    (∀ N : Sheaf J (ModuleCat.{max u v} Λ),
      ∃! m : ∀ X : Cᵒᵖ,
        Module (((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
          (N.obj.obj X), IsConstantRingModuleActionExtension J Λ N m) ∧
    (∀ (N M : Sheaf J (ModuleCat.{max u v} Λ)) (f : N ⟶ M)
      (m : ∀ X : Cᵒᵖ,
        Module (((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
          (N.obj.obj X))
      (n : ∀ X : Cᵒᵖ,
        Module (((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
          (M.obj.obj X)),
      IsConstantRingModuleActionExtension J Λ N m →
      IsConstantRingModuleActionExtension J Λ M n →
      ∀ (X : Cᵒᵖ)
        (s : ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
        (x : N.obj.obj X),
        f.hom.app X (@SMul.smul _ _ (m X).toSMul s x) =
          @SMul.smul _ _ (n X).toSMul s (f.hom.app X x)) := by
  sorry

end CategoryTheory
