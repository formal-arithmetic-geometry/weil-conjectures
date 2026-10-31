/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSystemCofinalData
import WeilConjectures.AlgebraicGeometry.SystemBlockRepetition
import WeilConjectures.AlgebraicGeometry.EtaleSystemCoefficientProjection
import WeilConjectures.CategoryTheory.SystemLevelLeftExtension
import WeilConjectures.CategoryTheory.IsoWhiskerCancellation

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
/- STATEMENT-DISPUTED: `CofinalSupport` contains no coherence field relating
`compositionX` and `compositionY` to the selected extension data or relating the
three `h` isomorphisms. The hypotheses `hi` and `hq` constrain only coefficient
projection maps, while the conclusion depends on the unconstrained composition
fields, so the claimed equality is not determined by the stated structure. -/
private theorem support_normalization_app
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (t : CofinalSupport c l) (B : Coefficients.{u} l) (r : ℕ ↪o ℕ)
    (N : Derived X (cofinalCoefficients B r).rings) :
    (t.projection.q (cofinalCoefficient B r)).app
      ((t.repetition B r).x.R.mapDerivedCategory.obj N) ≫
        (t.projection.support B).F.map ((t.factorX B r).derived.inv.app N) ≫
      (t.h B r).hom.app N ≫
      (t.factorY B r).derived.hom.app
        ((t.projection.support (cofinalCoefficients B r)).F.obj N) =
      (t.projection.scalarY (cofinalCoefficient B r)).model.T.map
        ((t.repetition B r).kappa.hom.app N) :=
  t.normalization B r N

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
  intro B r s N
  have _hnorm := support_normalization_app t B (s.trans r) N
  have _cancel := CategoryTheory.cancel_iso_whiskers
    (Iso.refl _) (Iso.refl _) ((t.h B (s.trans r)).hom.app N)
    ((t.h B (s.trans r)).hom.app N) (by simp)
  sorry

end AlgebraicGeometry.Etale.SystemProjection
