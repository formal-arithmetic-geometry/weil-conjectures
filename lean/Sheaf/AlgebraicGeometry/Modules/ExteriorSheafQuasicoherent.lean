/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Quasi-coherence of exterior sheaves on affine schemes

Source: Stacks Project, Section 26.7, Lemmas 26.7.1 and 26.7.2(2), Tag 01I6.
(blueprint: new-q1-exterior-sheaf-quasicoherent).
-/

@[expose] public section
set_option autoImplicit false
universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Exterior powers of a quasi-coherent module on an affine scheme are quasi-coherent.

Source: Stacks Project, Section 26.7, Lemmas 26.7.1, 26.7.2(2), and 26.7.4, Tag 01I6.
(blueprint: new-q1-exterior-sheaf-quasicoherent).

Proof: Write A = Gamma(X, top) and P = Gamma(X, M). The affine equivalence
(Lemma 26.7.4) identifies M with the associated A-module P. On a principal open
D(f), its sections are the localization P_f. Localization commutes with nth
exterior powers: the canonical alternating map sends a tuple of fractions to
the fraction whose numerator is the wedge of the numerators and whose
denominator is their product. The inverse is induced by the alternating
universal property after localization. The two maps are inverse on pure
wedges, which generate the exterior power. These identifications commute with
restrictions to smaller principal opens, checked on pure wedges. They identify
the exterior presheaf on the principal-open basis with the associated module
of the algebraic exterior power of P. Sheafification and restriction to this
basis therefore give an isomorphism from exteriorSheaf M n to that associated
module (Lemma 26.7.2(2)). The latter is quasi-coherent (Lemma 26.7.1), and
quasi-coherence is invariant under isomorphism. No finite generation, local
freeness, or regular immersion hypothesis is needed. In degree zero the
algebraic exterior power is A; on an empty affine scheme A is the zero ring
and the associated sheaf is zero. The same localization argument includes
M = 0, with degree-zero exterior power A and positive degrees zero.
-/
theorem isQuasicoherent_exteriorSheaf_of_isAffine {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (exteriorSheaf M n).IsQuasicoherent := by sorry

end AlgebraicGeometry.Scheme.Modules
