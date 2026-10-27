/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.ResidueFiber
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.AffineFiniteTypeGeneratingSections
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre

/-! # Correcting a section in one residue fibre

Source: Stacks Project, Tag 0F20,
`properties-lemma-quasi-affine-invertible-nonvanishing-section`, proof, affine specialization
with W = X: global generation in the base case and addition in the induction step.
(blueprint: lem-sfb-affine-invertible-section-fibre-correction)
-/

@[expose] public section

universe u

set_option autoImplicit false

namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine scheme, a section vanishing at `z` can be corrected by `f • t` to be
nonzero there, while preserving its residue values on any subset where `f` vanishes.
`residueValue` is the germ tensored with 1; the canonical tensor/quotient equivalence
identifies it with the image in L_x / m_x L_x. Scalar values are `X.Γevaluation`.

Source: Stacks Project, Tag 0F20,
`properties-lemma-quasi-affine-invertible-nonvanishing-section`, proof, affine specialization
with W = X, base case and induction step.
(blueprint: lem-sfb-affine-invertible-section-fibre-correction)

Proof:
1. Invertibility (`def-sc-invertible-module`) gives quasi-coherence and local freeness of
   rank one. Local trivializations give finite type (`pqf-def-coherent`). By
   `lem-weil-pbc-affine-finite-type-generating-sections`, choose finitely many global
   sections generating L.
2. Adjoin the zero section so the family is indexed by Fin (n + 1), still generating.
   Apply `lem-weil-pbc-invertible-generating-sections-fibre` at z. It supplies a member t
   whose germ is outside m_z L_z, equivalently whose residue value is nonzero.
3. Germs and residue values respect addition and scalar multiplication, so the value of
   s + f*t at y is s(y) + f(y)*t(y). At z, s(z) = 0 and f(z) is a nonzero element of the
   field kappa(z) (`def-weil-residue-field`). Its inverse shows f(z)*t(z) is nonzero.
4. At every x in F, f(x) = 0 gives (s + f*t)(x) = s(x). Thus t has both required
   properties, with no finiteness or closedness assumption on F. -/
theorem exists_affine_invertible_section_fibre_correction
    (X : Scheme.{u}) [IsAffine X] (L : X.Modules) [L.IsInvertible]
    (F : Set X) (z : X) (s : Γ(L, ⊤)) (f : Γ(X, ⊤))
    (hs : residueValue s z trivial = 0)
    (hf : X.Γevaluation z f ≠ 0)
    (hF : ∀ x ∈ F, X.Γevaluation x f = 0) :
    ∃ t : Γ(L, ⊤), residueValue (s + f • t) z trivial ≠ 0 ∧
      ∀ x ∈ F, residueValue (s + f • t) x trivial = residueValue s x trivial := by
  sorry

end AlgebraicGeometry.Scheme.Modules
