/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import Sheaf.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Restriction-zero sections are killed by a power of an invertible section

Source: Stacks Project, Properties, Lemma 01PW (lemma-invert-s-sections), injectivity.
(blueprint: lem-sc-p1-section-restriction-s-torsion)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- A section vanishing on the nonvanishing open of an invertible section is
annihilated by a tensor power of that section.

Source: Stacks Project, Properties, Lemma 01PW (lemma-invert-s-sections), part (1).
(blueprint: lem-sc-p1-section-restriction-s-torsion)

Proof:
1. By quasi-compactness and local rank-one freeness, choose a finite affine cover
   trivializing `L` (def-weil-pbc-quasi-compact-scheme, def-sc-invertible-module).
   Write `s = f_i e_i` in each trivialization. Nonzero residue-field value is equivalent
   to `f_i` lying outside the point's prime, so `X_s` meets the chart in `D(f_i)`
   (def-weil-residue-field).
2. Quasi-coherence identifies the restricted `F` with the tilde of its section module
   (pqf-def-coherent, lem-weil-pbc-affine-tilde-gamma-adjunction).
   Restriction to `D(f_i)` is localization
   (lem-weil-pbc-spec-module-tilde-sections). Since `t` vanishes there, the localization
   kernel criterion gives `f_i ^ n_i * t_i = 0` for some natural `n_i`
   (def-weil-pbc-module-localization).
3. Take the maximum of the finitely many `n_i` (zero for the empty cover). Multiplication
   by the corresponding tensor power of `s` vanishes on every chart, since in the local
   basis it is multiplication by `f_i ^ m` (def-sc-invertible-module).
   The sheaf property then makes the global tensor-product section zero.
-/
theorem section_restriction_s_torsion
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (L F : X.Modules) [L.IsInvertible] [F.IsQuasicoherent]
    (s : Γ(L, ⊤)) (t : Γ(F, ⊤))
    (X_s : X.Opens) (hXs : (X_s : Set X) = nonvanishingLocus L s)
    (hzero : F.presheaf.map (homOfLE (show X_s ≤ ⊤ from le_top)).op t = 0) :
    ∃ m : ℕ, tmulSection t (tensorPowSectionOne (homOfGlobalSection L s) m ⊤) = 0 := by
  sorry

end AlgebraicGeometry.Scheme.Modules
