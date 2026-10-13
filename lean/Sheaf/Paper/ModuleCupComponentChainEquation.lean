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

/-- The assembled component maps satisfy the signed chain equation by Leibniz. Source: Stacks
Project, Tag 0FKU, construction before Lemma 20.31.3.
(blueprint: lem-sc-module-cup-resolution-chain-equation).
Proof: equality of maps out of a total term can be tested on its coproduct inclusions.
For a nonnegative bidegree, equality out of the tensor sheaf is tested after the
sheafification unit, then on elementary tensors of sections on every open. The assumed
section formula computes l on these tensors. The total tensor differential is the sum
of the left differential and (-1)^p times the right differential; D.leibniz identifies
these with the target differential of D.pair. The extension isomorphisms identify all
nonnegative differentials with the original ones. A negative factor makes its summand
zero, so its equation is automatic. Thus the coproduct equations prove the chain equation.
In particular, degree zero has positive sign and all negative total degrees are zero. -/
theorem moduleCup_component_chain_equation {F G : X.Modules} (D : CupResolutionPairing F G)
    (l : ∀ n : ℤ, (D.left.integerComplex ⊗ D.right.integerComplex).X n ⟶
      D.target.integerComplex.X n)
    (hl : ∀ (p q : ℕ) (V : X.Opens) (a : Γ(D.left.K.X p, V))
      (b : Γ(D.right.K.X q, V)),
      ((HomologicalComplex.ιTensorObj D.left.integerComplex D.right.integerComplex
          (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ) (by omega)) ≫ l (p + q) ≫
        (D.target.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom).val.app (op V)
        (tmulSection
          ((D.left.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) a)
          ((D.right.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) b)) =
        D.pair p q V a b) :
    ∀ (i j : ℤ), (ComplexShape.up ℤ).Rel i j →
      l i ≫ D.target.integerComplex.d i j =
        (D.left.integerComplex ⊗ D.right.integerComplex).d i j ≫ l j
    := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
