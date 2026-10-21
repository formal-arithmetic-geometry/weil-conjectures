/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy
public import WeilConjectures.RepresentationTheory.CompositionSeries
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations
public import WeilConjectures.WeilSheaf.Stalk
import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Basic
import Sheaf.Paper.EtaleWeilSheafEquivalence
import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra
import Sheaf.Paper.AdicLocalCharacteristicFactor

/-!
# Reality survives semisimplification

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-r-real-linear,
lemma lem-wf-real-semisimplification (blueprint: lem-wf-real-semisimplification).

We use the published Weil-representation model of lisse Weil sheaves. The representation
is the one underlying the recorded monodromy datum; semisimplification is the recorded
direct sum of its composition factors. `WeilGroup.localPolynomial` is the local factor
`det(1 - T F_x)`, and `WeilGroup.IsReal` is its coefficientwise reality condition, as in
`WeilSheaf.IsReal` for the stalk Frobenius modules.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilGroup

/-- An `ι`-real lisse Weil representation remains lisse and `ι`-real after
semisimplification, with exactly the same local characteristic factors at every closed point.
Source: blueprint main-20261015, sec-purity-real-sheaves/sk-r-real-linear,
lemma lem-wf-real-semisimplification (blueprint: lem-wf-real-semisimplification).

Proof: For the zero representation the composition series has no factors, its direct sum
is zero, and every local determinant factor is one. Otherwise use
`Representation.exists_compositionSeries` (lem-mg-composition-series-exists). Each step of
`Representation.CompositionSeries` (def-mg-weil-composition-series) is Weil-stable, with
simple quotient. The exact tensor equivalence of
prop-wf-weil-sheaf-representation-equivalence identifies this filtration with the lisse Weil
subsheaf filtration and its quotients. The definition def-mg-weil-semisimplification is the
finite direct sum of these quotients, which is again lisse by continuity of the quotient
and direct-sum actions (def-real-weil-representation-operations).

At any closed point, p-real-operations identifies the local factor with the determinant
of one minus the local Frobenius action times T. Apply p-linear-filtration, namely
`LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ`, successively to the invariant
filtration. Convert characteristic polynomials to local determinant factors using
`det(1 - T f) = T^(dim V) det(T^(-1) - f)` in Laurent polynomials and additivity of dimension.
Apply the same calculation to the partial sums of the composition factors. Both local
polynomials are the product of the same quotient factors, for every composition series.
Finally their equality transfers the real-coefficient condition def-wf-iota-real from the
original representation to its semisimplification. No distinct-eigenvalue or nonzero-rank
assumption is used. -/
theorem isReal_semisimplification
    {K : Type u} [Field K] [Finite K] {C : Scheme.{u}}
    {p : C ⟶ Spec (.of K)} [IsCurve p] (W : WeilGroup p)
    {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
    {n : Type u} [Fintype n] [DecidableEq n]
    (D : Monodromy.RepresentedDegreeDatum W.carrier n (PadicAlgCl l))
    (ι : PadicAlgCl l →+* ℂ) (hLisse : W.IsLisse l D.asRepresentation)
    (hReal : W.IsReal l D.asRepresentation ι)
    (s : D.asRepresentation.CompositionSeries) :
    W.IsLisse l s.semisimplification ∧ W.IsReal l s.semisimplification ι ∧
      ∀ x : C.finitePoints,
        W.localPolynomial l s.semisimplification x =
          W.localPolynomial l D.asRepresentation x := by
  sorry

end AlgebraicGeometry.WeilGroup
