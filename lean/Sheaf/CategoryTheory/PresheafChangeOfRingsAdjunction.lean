/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Change of rings for presheaves of modules

Source: Stacks Project, Sheaves, Tag 006R (blueprint: lem-pc-presheaf-change-of-rings-adjunction)
-/

@[expose] public section

universe u v w

open CategoryTheory
open scoped ChangeOfRings

namespace PresheafOfModules

variable (X : TopCat.{u}) (A B : X.Sheaf CommRingCat.{w}) (α : A ⟶ B)

local notation "R" => (A.presheaf ⋙ forget₂ CommRingCat RingCat)
local notation "S" => (B.presheaf ⋙ forget₂ CommRingCat RingCat)
local notation "a" => Functor.whiskerRight α.hom (forget₂ CommRingCat RingCat)

/-- The sectionwise tensor presheaf is left adjoint to restriction of scalars.
The witnesses `T` and `q` present the tensor presheaf functor by sectionwise
`B(U)`-linear isomorphisms from `B(U) ⊗[A(U)] M(U)`. The first two clauses specify
its restrictions and its action on morphisms. The equivalences `e` have the
unit and inverse formulas and are natural in both module presheaves.

Source: Stacks Project, Sheaves, Tag 006R, lemma-adjointness-tensor-restrict-presheaves,
and the definitions immediately preceding it.
(blueprint: lem-pc-presheaf-change-of-rings-adjunction)

Proof (the four steps of the node):
1. Restrict scalars using `a`; the ring morphism's naturality gives semilinear
restrictions. Form sectionwise base change [def-weil-module-base-change]; the tensor
universal property [def-weil-pbc-module-tensor-product] defines restrictions by
`b ⊗ m ↦ b|V ⊗ m|V`. Identity, composition and semilinearity hold on pure tensors,
which generate. This is a presheaf of modules [def-weil-presheaf-modules-sheafification].
2. Apply the scalar-extension Hom equivalence [lem-weil-pbc-scalar-extension-hom]
to each section ring map: forward evaluation on `1 ⊗ m`, inverse `b ⊗ m ↦ b • w(m)`.
3. Forward restriction compatibility follows by evaluating on `1 ⊗ m` and `1|V = 1`.
Inverse compatibility follows on `b ⊗ m` from semilinearity of the restrictions of `N`
and compatibility of `w`; tensor generation extends it to every element
[def-weil-pbc-module-tensor-product]. The sectionwise inverses give inverse presheaf
morphisms [def-weil-presheaf-modules-sheafification], hence the equivalences `e`.
4. For `f : M ⟶ M'`, sectionwise `id ⊗ f` commutes with restrictions on pure tensors
and thus everywhere [def-weil-module-base-change, def-weil-pbc-module-tensor-product].
Evaluate on `1 ⊗ m` to get naturality in `M`. Postcomposition with `β : N ⟶ N'`
gives naturality in `N` by the sectionwise formula [lem-weil-pbc-scalar-extension-hom]. -/
theorem changeOfRingsAdjunction :
    ∃ (T : PresheafOfModules.{max v w} R ⥤ PresheafOfModules.{max v w} S)
      (q : ∀ (M : PresheafOfModules.{max v w} R) (U : (TopologicalSpace.Opens X)ᵒᵖ),
        (ModuleCat.extendScalars (α.hom.app U).hom).obj (M.obj U) ≅ (T.obj M).obj U)
      (e : ∀ (M : PresheafOfModules.{max v w} R) (N : PresheafOfModules.{max v w} S),
        (T.obj M ⟶ N) ≃ (M ⟶ (restrictScalars a).obj N)),
      (∀ (M : PresheafOfModules.{max v w} R)
        (U V : (TopologicalSpace.Opens X)ᵒᵖ) (i : U ⟶ V)
        (b : B.presheaf.obj U) (m : M.obj U),
        (T.obj M).map i ((q M U).hom (b ⊗ₜ[A.presheaf.obj U,(α.hom.app U).hom] m)) =
          (q M V).hom ((B.presheaf.map i b) ⊗ₜ[A.presheaf.obj V,(α.hom.app V).hom]
            (M.map i m))) ∧
      (∀ (M M' : PresheafOfModules.{max v w} R) (f : M ⟶ M')
        (U : (TopologicalSpace.Opens X)ᵒᵖ) (b : B.presheaf.obj U) (m : M.obj U),
        (T.map f).app U ((q M U).hom (b ⊗ₜ[A.presheaf.obj U,(α.hom.app U).hom] m)) =
          (q M' U).hom (b ⊗ₜ[A.presheaf.obj U,(α.hom.app U).hom] (f.app U m))) ∧
      (∀ (M : PresheafOfModules.{max v w} R) (N : PresheafOfModules.{max v w} S)
        (f : T.obj M ⟶ N) (U : (TopologicalSpace.Opens X)ᵒᵖ) (m : M.obj U),
        (e M N f).app U m =
          f.app U ((q M U).hom ((1 : B.presheaf.obj U) ⊗ₜ[A.presheaf.obj U,
            (α.hom.app U).hom] m))) ∧
      (∀ (M : PresheafOfModules.{max v w} R) (N : PresheafOfModules.{max v w} S)
        (g : M ⟶ (restrictScalars a).obj N) (U : (TopologicalSpace.Opens X)ᵒᵖ)
        (b : B.presheaf.obj U) (m : M.obj U),
        ((e M N).symm g).app U
            ((q M U).hom (b ⊗ₜ[A.presheaf.obj U,(α.hom.app U).hom] m)) =
          b • (show N.obj U from g.app U m)) ∧
      (∀ (M M' : PresheafOfModules.{max v w} R) (N : PresheafOfModules.{max v w} S)
        (f : M ⟶ M') (h : T.obj M' ⟶ N),
        e M N (T.map f ≫ h) = f ≫ e M' N h) ∧
      (∀ (M : PresheafOfModules.{max v w} R) (N N' : PresheafOfModules.{max v w} S)
        (β : N ⟶ N') (h : T.obj M ⟶ N),
        e M N' (h ≫ β) = e M N h ≫ (restrictScalars a).map β) := by
  sorry

end PresheafOfModules
