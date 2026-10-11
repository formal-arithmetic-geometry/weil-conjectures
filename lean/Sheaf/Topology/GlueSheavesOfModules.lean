/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Paper.DerivedHomMayerVietoris

/-!
# Glueing morphisms and sheaves of modules along an open covering

Source: Stacks Project, Sheaves, Section 00AK, Lemmas 04TN, 00AL and 00AM
(blueprint: lem-weil-pbc-glue-sheaves-of-modules).
-/

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- Glueing morphisms and sheaves of modules on an open cover.
Restrictions to `U` use the localized site `Over U`: its objects are precisely the
opens `W ≤ U`. Restrictions of local modules use `SheafOfModules.overMap`.
Equality of maps on overlaps is expressed at every such open `W`, so no choices
of comparison isomorphisms for iterated restriction enter the statement.

Source: Stacks Project, Sheaves, Section 00AK, Lemmas 04TN, 00AL and 00AM
(blueprint: lem-weil-pbc-glue-sheaves-of-modules).
Proof (using def-weil-sheaf-of-modules-category throughout):
1. For `s ∈ F(W)`, glue the sections `φᵢ(s|W ∩ Uᵢ)` in `G` using overlap agreement.
2. Check naturality, additivity and O-linearity after restriction to `W ∩ Uᵢ`;
   separation of `G` makes these local identities global.
3. At `W ≤ Uᵢ` this construction equals `φᵢ`; uniqueness of glued sections proves
   uniqueness of the morphism and the stated equality criterion for two morphisms.
4. The cocycle gives `φᵢᵢ = id`. Define `H(W)` as compatible families in the product
   of `Fᵢ(W ∩ Uᵢ)`. Linearity makes this an O(W)-submodule; restriction is componentwise.
5. Glue families componentwise using each `Fᵢ`'s sheaf axiom; separation checks overlap
   compatibility and uniqueness, giving the sheaf axiom for `H`.
6. On `W ≤ Uᵢ`, projection to component `i` is a linear isomorphism: all other
   components are recovered by `φᵢⱼ` from that component, and the cocycle ensures
   these recovered components agree. These maps and inverses commute with restriction.
7. The defining equations of compatible families give `φᵢ ≫ φᵢⱼ = φⱼ` on overlaps. -/
theorem glue_sheaves_of_modules
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (hcover : ⨆ i, U i = ⊤) :
    (∀ (F G : SheafOfModules.{max u v} (moduleRings X))
      (φ : ∀ i : I, F.over (U i) ⟶ G.over (U i)),
      (∀ (i j : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
        (φ i).val.app (op (Over.mk (homOfLE hi))) =
          (φ j).val.app (op (Over.mk (homOfLE hj)))) →
      ∃! ψ : F ⟶ G, ∀ i : I, ψ.over (U i) = φ i) ∧
    (∀ (F G : SheafOfModules.{max u v} (moduleRings X)) (α β : F ⟶ G),
      (∀ i : I, α.over (U i) = β.over (U i)) → α = β) ∧
    (∀ (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
      (φij : ∀ i j : I,
        (SheafOfModules.overMap (moduleRings X) (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj
            (Fi i) ≅
          (SheafOfModules.overMap (moduleRings X)
            (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j)),
      (∀ (i j k : I) (W : Opens X)
        (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
        (φij i k).hom.val.app (op (Over.mk (homOfLE (le_inf hi hk)))) =
          (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
            (φij j k).hom.val.app (op (Over.mk (homOfLE (le_inf hj hk))))) →
      ∃ (H : SheafOfModules.{max u v} (moduleRings X))
        (φi : ∀ i : I, H.over (U i) ≅ Fi i),
        ∀ (i j : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
          (φi i).hom.val.app (op (Over.mk (homOfLE hi))) ≫
            (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) =
              (φi j).hom.val.app (op (Over.mk (homOfLE hj)))) := by
  sorry

end AlgebraicGeometry
