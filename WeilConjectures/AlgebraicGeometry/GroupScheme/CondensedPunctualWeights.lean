/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedWeil.ConstantExtensionPunctualWeights

/-! # Punctual weights of constructible condensed Weil sheaves

Source: latest blueprint, sec-purity-real-sheaves/sk-d-real-weights,
def-weil-punctual-weights.md (blueprint: def-weil-punctual-weights).

The existing ordinary condensed weight formulas are restricted to the finite constant
model heart specified by the blueprint. The constructibility argument and the distinct
coefficient prime are explicit. These are transparent aliases, not new weight formulas.
The scalar fibre is the actual geometric-point pullback followed by sections, with the
canonical local geometric-Frobenius return. No common-stage or adic presentation is input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Every local Frobenius eigenvalue has complex norm equal to the residue cardinality
raised to half the real weight. The domain is a constructible condensed Weil module;
its constructibility is precisely the finite constant model condition of Cons.
Source: latest blueprint, def-weil-punctual-weights.md, purity display
(blueprint: def-weil-punctual-weights). -/
abbrev condensedIsPunctuallyPureOfWeight
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (F : CondensedWeil.WeilModule D ell Y₀)
    (_hF : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
      (D.geometricFiber Y₀).left F.carrier)
    (iota : PadicAlgCl ell →+* ℂ) (w : ℝ) : Prop :=
  CondensedWeil.Pure D ell Y₀ F iota w

/-- A finite filtration by constructible Weil submodules, starting at zero and ending
at F, with punctually pure successive quotients of real weights at most w. The ambient
Weil-module cokernel carries its induced Weil structure; no quotient structure is chosen.
Length zero is permitted. Source: latest blueprint, def-weil-punctual-weights.md,
mixedness display (blueprint: def-weil-punctual-weights). -/
abbrev condensedIsMixedOfWeightsAtMost
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (F : CondensedWeil.WeilModule D ell Y₀)
    (_hF : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
      (D.geometricFiber Y₀).left F.carrier)
    (iota : PadicAlgCl ell →+* ℂ) (w : ℝ) : Prop :=
  CondensedWeil.Mixed D ell Y₀ F iota w

/-- The eigenvalue set is independent of the residue-field embedding and hence of the
associated geometric lift. Source: latest blueprint, def-weil-punctual-weights.md,
last sentence (blueprint: def-weil-punctual-weights).

Proof (node assembly step 4): place the constructible Weil module in degree zero and
apply lem-weil-local-frobenius-conjugacy-class with j = 0. Exact geometric pullback and
point sections identify degree-zero cohomology with the ordinary scalar fibre used
here. The pullback compositors and the canonical point reparametrization identify
its operator with closedOperator: both iterate the Weil structure by the residue
degree and then use the same semilinear return. The resulting scalar-linear
intertwiner sends a nonzero alpha-eigenvector to a nonzero alpha-eigenvector. Apply
its inverse for the converse. This includes zero fibres and residue degree one. -/
theorem condensedPunctualEigenvalues_independent
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (F : CondensedWeil.WeilModule D ell Y₀)
    (_hF : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
      (D.geometricFiber Y₀).left F.carrier)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (i i' : Y₀.left.residueField y.val →+* D.k)
    (hi : i.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (hi' : i'.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (α : PadicAlgCl ell) :
    Module.End.HasEigenvalue (CondensedWeil.closedOperator D ell Y₀ F y i hi).hom α ↔
      Module.End.HasEigenvalue (CondensedWeil.closedOperator D ell Y₀ F y i' hi').hom α := by
  sorry

end WeilConjectures
