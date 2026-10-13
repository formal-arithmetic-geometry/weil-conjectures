/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.ModuleCupRealizationComplexData

/-! # Cochain obligations for resolution pairings

Source: Stacks Project, Tag 0FKU, construction before Lemma 20.31.3.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

attribute [local instance] cupRealizationMonoidalCategory cupRealizationSymmetricCategory
  cupRealizationHasColimitsOfSize cupRealizationMonoidalPreadditive cupRealizationMonoidalClosed
  cupRealizationHasFunctorialFlatResolution cupRealizationIsGrothendieckAbelian
  cupRealizationDerivedMonoidal cupRealizationQLax

/-- Sheaf tensor linearization and coproduct assembly provide the component maps and their
section formula. Source: Stacks Project, Tag 0FKU, construction before Lemma 20.31.3.
(blueprint: lem-sc-module-cup-resolution-section-map).
Proof: for each nonnegative bidegree, linearize D.pair on each open using the ordinary
module tensor universal property. D.restriction makes these linear maps a presheaf morphism.
Descend it through the sheafification adjunction, obtaining a morphism from the sheaf tensor
to the target term. Transport along the extension isomorphisms. For a bidegree with a
negative factor, that extended factor is zero, so use the zero morphism. In each total
degree assemble these summand morphisms with the coproduct universal property. Its inclusion
equation and the sheafification unit formula give the displayed section formula. -/
theorem moduleCup_component_section_map_exists {F G : X.Modules} (D : CupResolutionPairing F G) :
    ∃ l : ∀ n : ℤ, (D.left.integerComplex ⊗ D.right.integerComplex).X n ⟶
      D.target.integerComplex.X n,
      ∀ (p q : ℕ) (V : X.Opens) (a : Γ(D.left.K.X p, V))
        (b : Γ(D.right.K.X q, V)),
        ((HomologicalComplex.ιTensorObj D.left.integerComplex D.right.integerComplex
            (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ) (by omega)) ≫ l (p + q) ≫
          (D.target.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom).val.app (op V)
          (tmulSection
            ((D.left.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) a)
            ((D.right.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) b)) =
          D.pair p q V a b := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
