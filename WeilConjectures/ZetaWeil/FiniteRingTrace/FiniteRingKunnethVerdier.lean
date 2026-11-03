/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.FiniteRingTrace.FiniteRingProductComparisons

/-! # Künneth–Verdier with arbitrary finite primary coefficients

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/
thm-trf-kunneth-verdier.md and its proof (blueprint: thm-trf-kunneth-verdier).
The comparison is the existing evaluation/counit construction, with the discrete
finite coefficient ring. No replacement isomorphism or ambient exceptional adjoint
is supplied. Compactifications and the coefficient unit are represented explicitly.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing
open AlgebraicGeometry.ProEtale.CondensedRing.ProductComparisons
open scoped CategoryTheory.Obj

namespace WeilConjectures.FiniteRingTrace

/-- The canonical finite-coefficient Künneth–Verdier comparison is invertible.

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/
thm-trf-kunneth-verdier.md (blueprint: thm-trf-kunneth-verdier).

Proof plan, following the four DAG steps:
1. The coefficient unit is constructible by its one-stratum constant model and has
Tor interval [0,0]. The constructible exceptional restriction sends this unit to
omega_Y. The identity's exceptional adjoint is canonically the identity, by uniqueness
of right adjoints. Thus (A_X,M) and (N,omega_Y) satisfy the external-Hom hypotheses.
2. Apply prop-trf-external-hom to these pairs. The tensor-unit identifications give
an isomorphism b from M boxtimes D_Y N to RHom(Lp_Y^*N,M boxtimes omega_Y).
3. Apply prop-trf-exceptional-kunneth to (id_X,a_Y) at (M,A_s). Its counit-defined
alpha, including the identity and target-unit identifications, is an isomorphism a
from M boxtimes omega_Y to Rp_X^!M. All exceptional adjoints are constructible.
4. The definition of productComparisons, through ProductComparisons.kappa, is exactly
b followed by RHom(1,a), transported at the target by the unique counit-compatible
isomorphism to traceFormulaCtfUpperShriek. Its inverse composes the inverses in reverse order.
Functoriality and the inverse identities prove both composites are identities.

The bundled product W with its Cartesian square represents X times_k Y; c records
compactification models. The coefficient is the recorded regular object in degree zero.
The target uses the recorded traceFormulaCtfUpperShriek via rightAdjointUniq;
the auxiliary Brown presentation adds no hypothesis or new admissibility notion. -/
theorem kunnethVerdier_isIso (A : Type) [CommRing A] [Finite A]
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p)
    (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
    (X Y W : SepFinType D.k) (pX : W ⟶ X) (pY : W ⟶ Y)
    (sq : IsPullback pX.hom.left pY.hom.left X.obj.hom Y.obj.hom)
    (c : Models (verdierGeometry X Y W pX pY sq))
    (M : Ctf A X.obj.left) (N : Ctf A Y.obj.left) :
    IsIso (kunnethVerdierMap A D ell hell hA X Y W pX pY sq c M N) := by
  sorry

end WeilConjectures.FiniteRingTrace
