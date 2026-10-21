/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.IteratedWeilMap
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.TraceFormulaStrictWeilComplex
import Sheaf.SixFunctors.SchemeFrobenius

/-!
# Cocycle identity for iterated Weil isomorphisms

Source: Weil conjectures blueprint, main-20261015,
sec-trace-formula/sk-d-weil/lem-trf-iterated-weil-cocycle.md
(blueprint: lem-trf-iterated-weil-cocycle).

The statement compares the specified positive iterates using the canonical
constant-coefficient derived pullback comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.TraceFormulaCoefficientConventions

/-- The specified iterated Weil isomorphisms satisfy the cocycle identity after
canonical pullback identification.

Source: Weil conjectures blueprint, main-20261015,
sec-trace-formula/sk-d-weil/lem-trf-iterated-weil-cocycle.md
(blueprint: lem-trf-iterated-weil-cocycle).
Proof: use the canonical derived pullback composition comparison and its coherence
for powers of geometric Frobenius.  Expand the defining iterated isomorphisms into
successive pulled-back factors.  Functoriality shifts the factors in the second
block by `m`, and associativity concatenates the two blocks to the `(m+n)`-fold
composite, giving the displayed equality. -/
theorem iterated_weil_cocycle
    (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (T.iteratedWeilIsomorphism K (m + n) (by omega)).hom =
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback T.coefficientRing)
        (by
          simpa [Nat.add_comm] using (pow_add
            (End.of (T.datum.geometricGaloisFrobenius T.X₀)) n m))) ≪≫
        (proEtaleConstantRingPullbackComposition
          ((End.of (T.datum.geometricGaloisFrobenius T.X₀)) ^ m)
          ((End.of (T.datum.geometricGaloisFrobenius T.X₀)) ^ n)
          T.coefficientRing).symm).hom.app K.obj.carrier ≫
      (proEtaleConstantRingDerivedPullback T.coefficientRing
        ((End.of (T.datum.geometricGaloisFrobenius T.X₀)) ^ m)).map
        (T.iteratedWeilIsomorphism K n hn).hom ≫
      (T.iteratedWeilIsomorphism K m hm).hom := by
  sorry

end WeilConjectures.TraceFormulaCoefficientConventions
