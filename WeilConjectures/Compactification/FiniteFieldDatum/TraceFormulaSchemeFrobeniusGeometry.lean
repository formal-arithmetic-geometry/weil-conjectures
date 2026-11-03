/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobeniusFiniteRadicial

/-! # Coefficient-independent scheme Frobenius geometry

The geometric declarations and their proofs are reused with distinct helper names from
`SchemeFrobenius`; the original coefficient specializations remain intact.
Source: latest blueprint, scheme Frobenius construction
(blueprint: lem-trf-coefficient-free-scheme-frobenius-geometry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.FiniteFieldDatum

/-- The scalar-extended q-power scheme Frobenius of a finite-type model.
Source: latest blueprint, scheme Frobenius definition
(blueprint: lem-trf-coefficient-free-scheme-frobenius-geometry).
The map is the base change of the absolute q-power Frobenius supplied by
`relativeFrobenius`; its affine formula is `a ⊗ b ↦ a ^ q ⊗ b`. -/
noncomputable def coefficientFreeSchemeFrobenius
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber X₀).left :=
  D.relativeFrobenius X₀

/-- The m-fold iterate of the scalar-extended scheme Frobenius.
Source: latest blueprint, scheme Frobenius definition
(blueprint: lem-trf-coefficient-free-scheme-frobenius-geometry). -/
noncomputable def coefficientFreeSchemeFrobeniusIterate
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (m : ℕ) :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber X₀).left :=
  let Φ : End (D.geometricFiber X₀).left := D.coefficientFreeSchemeFrobenius X₀
  Φ ^ m

/-- The finiteness and radiciality assertions for the constructed Frobenius.
Source: latest blueprint, scheme Frobenius definition
(blueprint: lem-trf-coefficient-free-scheme-frobenius-geometry); dependency
`lem-trf-scheme-frobenius-finite-radicial`.
Proof: unfold `coefficientFreeSchemeFrobenius`, which is the recorded scalar-extended relative
Frobenius, and apply `relativeFrobenius_isFinite_isRadicial` from that dependency. -/
theorem coefficientFreeSchemeFrobenius_isFinite_isRadicial
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    IsFinite (D.coefficientFreeSchemeFrobenius X₀) ∧
      UniversallyInjective (D.coefficientFreeSchemeFrobenius X₀) := by
  exact D.relativeFrobenius_isFinite_isRadicial X₀

end WeilConjectures.FiniteFieldDatum
