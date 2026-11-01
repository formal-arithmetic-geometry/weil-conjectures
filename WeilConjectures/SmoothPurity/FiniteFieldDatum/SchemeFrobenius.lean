/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobeniusFiniteRadicial
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import Mathlib.Algebra.CharP.Invertible

/-!
# Scheme and Galois Frobenius of the geometric fibre

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation, order 2415,
`def-trf-scheme-frobenius.md` (blueprint: def-trf-scheme-frobenius).

The q-power scheme Frobenius is the scalar extension of the model's relative Frobenius.
The Galois Frobenius maps are the geometric Frobenius automorphism and its inverse.
Derived pullbacks use the recorded finite, completed integral, rational and common-stage
coefficient operations, as well as the ordinary constant-ring specialization.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

/-- The scalar-extended q-power scheme Frobenius of a finite-type model.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius).
The map is the base change of the absolute q-power Frobenius supplied by
`relativeFrobenius`; its affine formula is `a ⊗ b ↦ a ^ q ⊗ b`. -/
noncomputable def schemeFrobenius
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber X₀).left :=
  D.relativeFrobenius X₀

/-- The m-fold iterate of the scalar-extended scheme Frobenius.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius). -/
noncomputable def schemeFrobeniusIterate
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (m : ℕ) :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber X₀).left :=
  let Φ : End (D.geometricFiber X₀).left := D.schemeFrobenius X₀
  Φ ^ m

/-- Arithmetic Galois Frobenius on the geometric fibre, namely the inverse of
geometric Frobenius. Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius). -/
noncomputable def arithmeticGaloisFrobenius
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber X₀).left :=
  (D.geometricFrobenius X₀).inv

/-- Geometric Galois Frobenius on the geometric fibre.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius). -/
noncomputable def geometricGaloisFrobenius
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber X₀).left :=
  (D.geometricFrobenius X₀).hom

/-- The finiteness and radiciality assertions for the constructed Frobenius.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius); dependency
`lem-trf-scheme-frobenius-finite-radicial`.
Proof: unfold `schemeFrobenius`, which is the recorded scalar-extended relative
Frobenius, and apply `relativeFrobenius_isFinite_isRadicial` from that dependency. -/
theorem schemeFrobenius_isFinite_isRadicial
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    IsFinite (D.schemeFrobenius X₀) ∧
      UniversallyInjective (D.schemeFrobenius X₀) := by
  exact D.relativeFrobenius_isFinite_isRadicial X₀

end WeilConjectures.FiniteFieldDatum
