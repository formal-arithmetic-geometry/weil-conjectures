/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C9
-/
module

public import Sheaf.Paper.EtaleSystemCofinalData
import Sheaf.Paper.SystemBlockRepetition
import Sheaf.Paper.EtaleSystemCoefficientProjection
import Sheaf.CategoryTheory.SystemLevelLeftExtension

/-! # Composition of normalized cofinal support

Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The normalized geometric support comparison obeys the subsequence cocycle.
Source: Zheng, Construction 4.1 and coefficient-composition compatibility before
Lemma 4.10, printed pp. 21--23
(blueprint: lem-pur-etale-cofinal-support-composition).

Proof: the least-index identity t_(r∘s)(m)=t_s(t_r(m)) identifies the composite
repetition with direct repetition, including every horizontal restriction. The
ordinary selected extension compositors are determined by their units; they are
therefore the tensor associators on the selected representatives. Their normalized
derived comparisons identify the displayed leftAdjointUniq compositors with these
same associators, by uniqueness of total left derived functors.
Substitute CofinalSupport.normalization for the three h factors. Block repetition
commutes with the scalar units and restriction comparisons on sections. The block
coefficient-naturality theorem, applied to proper direct image, identifies the
resulting derived restriction squares; open extension commutes with restriction
already before localization. Thus the two repeated coefficient projection maps have
the same scalar-adjunction transpose and are equal as transformations of derived
systems. Apply the coefficient-projection cocycle and blockDerivedComparison_comp.
The normalized ordinary-unit and derived-counit equations of CofinalFactor cancel
all factorization comparisons, leaving exactly the asserted identity. This calculation
is performed on strict-system transformations using their universal derived-functor
normalizations, not by claiming faithfulness of level evaluations. Identity blocks
use the coefficient-unit and block-identity equations. The argument uses the
normalizations in t and the stated invertibility and cocycle of coefficient projection. -/
theorem etaleCofinalSupport_composition
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (t : CofinalSupport c l)
    (hi : ∀ (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings),
      IsIso (t.projection.q a))
    (hq : ∀ (B C D : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings),
      t.projection.q (a ≫ b) = t.projection.path a b) :
    (∀ (B : Coefficients.{u} l) (r s : ℕ ↪o ℕ)
        (N : Derived X (cofinalCoefficients B (s.trans r)).rings),
        (t.projection.support B).F.map
            ((cofinalExtensionComposition (t.extensionX B r)
              (t.extensionX (cofinalCoefficients B r) s) (t.extensionX B (s.trans r))
              (t.compositionX B r s)).hom.app N) ≫ (t.h B (s.trans r)).hom.app N =
          (t.h B r).hom.app ((t.extensionX (cofinalCoefficients B r) s).model.derived.obj N) ≫
            (t.extensionY B r).model.derived.map ((t.h (cofinalCoefficients B r) s).hom.app N) ≫
            (cofinalExtensionComposition (t.extensionY B r)
              (t.extensionY (cofinalCoefficients B r) s) (t.extensionY B (s.trans r))
              (t.compositionY B r s)).hom.app
                ((t.projection.support (cofinalCoefficients B (s.trans r))).F.obj N)) := by
  sorry

end AlgebraicGeometry.Etale.SystemProjection
