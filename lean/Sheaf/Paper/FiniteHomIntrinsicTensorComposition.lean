/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Paper.EtaleFiniteCoefficientHomArrow

/-! # Composition of the intrinsic finite scalar tensorators
Source: blueprint thm-coef-finite-hom, successive quotient paragraph
(blueprint: lem-coef-finite-hom-intrinsic-tensor-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The normalized tensorators commute with the prescribed scalar associator.
Source: blueprint thm-coef-finite-hom, proof of the A to B to C cocycle
(blueprint: lem-coef-finite-hom-intrinsic-tensor-composition).

Proof: represent both tensor inputs by flat-term K-flat complexes of modules over
the constant coefficient ring sheaf. The quotient calculus tensor_model computes
each tensorator by ordinary scalar balancing. The normalized quotient adjunctions
compute finiteHomIntrinsicAssoc by successive scalar multiplication: (x tensor b)
tensor c maps to x tensor bc. Following either side of the displayed square on
pure tensors therefore gives (x tensor bc) tensor (y tensor 1). These maps respect
the signed total differential, since coefficients have degree zero. K-flat change
of rings permits both successive quotient computations even when the quotients
are not flat. The localization comparison is invertible on these models, so
cancelling it proves the square on their derived images. Resolve arbitrary inputs
and use naturality to obtain the displayed equation for all ambient complexes.
Identity quotients and zero inputs give the same multiplication formula. -/
theorem finiteHomIntrinsic_tensorComposition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    {n m r : ℕ} (h : m ≤ n) (k : r ≤ m) (K M : normalizedDVRDerived l E X n) :
    let S := (coefficientDerivedSystemEvaluationCalculus l E X).choose
    let μ := S.quotientCalculus.tensor h
    let ν := S.quotientCalculus.tensor k
    let ξ := S.quotientCalculus.tensor (k.trans h)
    let α := finiteHomIntrinsicAssoc l E X h k
    let F := coefficientFiniteQuotientDerived l E X h
    let G := coefficientFiniteQuotientDerived l E X k
    G.map (μ.hom.app (K, M)) ≫ ν.hom.app (F.obj K, F.obj M) ≫
        (finiteIntrinsicClosed l E X r).tensor.map
          (Prod.mkHom (α.hom.app K) (α.hom.app M)) =
      α.hom.app ((finiteIntrinsicClosed l E X n).tensor.obj (K, M)) ≫
        ξ.hom.app (K, M) := by
  sorry

end WeilConjectures
