/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Prescribing independent split-torus character values

Source: Milne, Algebraic Groups (2017), Proposition 23.7, printed p.486, and
Theorem 12.9(a), printed pp.233--234: the independent-character lattice-extension
argument underlying the prescribed simple-root values
(blueprint: lem-sfb-independent-torus-character-values).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- Independent characters of a split torus attain every prescribed tuple of units.
The right-hand side is the F-point of G_m whose Laurent coordinate is the given unit.
Source: Milne, Proposition 23.7, p.486, and Theorem 12.9(a), pp.233--234;
the independent-character generalization is the following lattice argument
(blueprint: lem-sfb-independent-torus-character-values).

Proof:
1. Choose a splitting and apply lem-sfb-split-torus-hom-matrices. The characters
   become independent exponent vectors u_i in Z^r. Their independence gives a
   well-defined homomorphism on N = sum Z u_i sending u_i to c_i.
2. Apply lem-sfb-pid-submodule-smith-bases (Submodule.exists_smith_normal_form_of_le)
   to N contained in Z^r. Obtain bases v_j of N and b_j of Z^r with v_j = a_j b_j.
   Each a_j is nonzero since v_j is a basis vector.
3. Put d_j = h_N(v_j). If a_j > 0, choose a root of X^(a_j) - d_j; if a_j < 0,
   choose a root of X^(-a_j) - d_j^(-1). Algebraic closedness gives these roots,
   which are nonzero because d_j is a unit. Thus w_j^(a_j) = d_j. Set the remaining
   w_j to 1. This remains valid when the characteristic divides a_j.
4. Extend to h : Z^r -> F^units by sending b_j to w_j. Its agreement with h_N on
   the basis v_j implies agreement on all of N.
5. Set x_k = h(e_k) for the standard basis and transport this torus point through
   the splitting. The monomial formula gives chi_i(t) = h(u_i) = c_i. For m = 0
   the identity point suffices; for r = 0 independence forces m = 0.
-/
theorem exists_torus_point_of_independent_characters
    (F : Type u) [Field F] [IsAlgClosed F]
    (T : Grp (Over (Spec (.of F)))) [IsAffine T.X.left]
    (r m : ℕ) (hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (χ : Fin m → (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hind : ∀ n : Fin m → ℤ,
      (List.ofFn (fun i : Fin m ↦ (χ i).hom.hom ^ n i)).prod = 1 →
        ∀ i, n i = 0)
    (c : Fin m → Fˣ) :
    ∃ t : Over.mk (𝟙 (Spec (.of F))) ⟶ T.X, ∀ i : Fin m,
      (t ≫ (χ i).hom.hom).left =
        Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id F) (c i))) := by
  sorry

end AlgebraicGeometry
