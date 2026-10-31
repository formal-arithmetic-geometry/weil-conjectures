/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
public import WeilConjectures.RepresentationTheory.CompositionSeries
import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra

/-!
# Reality survives semisimplification

Source: literature/blueprint/master/blueprint/sec-purity-real-sheaves/sk-r-real-linear/
lem-wf-real-semisimplification.md, node lem-wf-real-semisimplification, order 2601
(blueprint: lem-wf-real-semisimplification).

We use the published Weil-representation model of lisse Weil sheaves. The representation
is the one underlying the recorded monodromy datum; semisimplification is the recorded
direct sum of its composition factors. `WeilGroup.localPolynomial` is the local factor
`det(1 - T F_x)`, and `WeilGroup.IsReal` is its coefficientwise reality condition
(def-wf-iota-real, read through the sheaf-representation correspondence).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry
namespace WeilGroup

/-- Reality survives semisimplification: an `ι`-real lisse Weil representation remains lisse
and `ι`-real after semisimplification, with exactly the same local characteristic factors at
every closed point.

Source: literature/blueprint/master/blueprint/sec-purity-real-sheaves/
  sk-r-real-linear/lem-wf-real-semisimplification.md, node
  `lem-wf-real-semisimplification` (blueprint: lem-wf-real-semisimplification).

Proof: (1) For the zero representation the composition series has no factors, its direct
sum is zero, and every local determinant factor is one. Otherwise use
`Representation.exists_compositionSeries` (lem-mg-composition-series-exists). Each step of
`Representation.CompositionSeries` (def-mg-weil-composition-series) is Weil-stable, with
simple quotient. (2) The exact tensor equivalence of
prop-wf-weil-sheaf-representation-equivalence identifies this filtration with the lisse Weil
subsheaf filtration and its quotients. The definition def-mg-weil-semisimplification is the
finite direct sum of these quotients, which is again lisse by continuity of the quotient
and direct-sum actions (def-real-weil-representation-operations).
(3) At any closed point, p-real-operations identifies the local factor with the determinant
of one minus the local Frobenius action times T. Apply p-linear-filtration, namely
`LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ`, successively to the invariant
filtration. Convert characteristic polynomials to local determinant factors using
`det(1 - T f) = T^(dim V) det(T^(-1) - f)` in Laurent polynomials and additivity of dimension.
(4) Apply the same calculation to the partial sums of the composition factors. Both local
polynomials are the product of the same quotient factors, for every composition series.
(5) Finally their equality transfers the real-coefficient condition def-wf-iota-real from the
original representation to its semisimplification. No distinct-eigenvalue or nonzero-rank
assumption is used.

In Lean, the representation `s.semisimplification` is already the model, so step (2) is
`IsLisse.subquotient` and `IsLisse.directSum`. Steps (3)-(4) use
`LinearMap.charpoly_eq_prod_charpoly_mapQ_of_le` on the series filtration and
`Representation.charpoly_directSum` on the direct sum; then both local factors are the
reverse of the same product, since `localPolynomial` is `charpolyRev`. -/
theorem isReal_semisimplification {K : Type u} [Field K] [Finite K] {C : Scheme.{u}}
    {p : C ⟶ Spec (.of K)} [IsCurve p] (W : WeilGroup p) {l : ℕ} [Fact l.Prime]
    [Fact (ringChar K ≠ l)] {n : Type u} [Fintype n] [DecidableEq n]
    (D : Monodromy.RepresentedDegreeDatum W.carrier n (PadicAlgCl l))
    (ι : PadicAlgCl l →+* ℂ) (hLisse : W.IsLisse l D.asRepresentation)
    (hReal : W.IsReal l D.asRepresentation ι)
    (s : D.asRepresentation.CompositionSeries) :
    W.IsLisse l s.semisimplification ∧
      W.IsReal l s.semisimplification ι ∧
      ∀ x : C.finitePoints,
        W.localPolynomial l s.semisimplification x =
          W.localPolynomial l D.asRepresentation x := by
  let F : ℕ → Subrepresentation D.asRepresentation := fun i ↦
    s.series ⟨min i s.length, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have h0 : F 0 = ⊥ := by
    rw [← s.head_eq, RelSeries.head]
    exact congrArg s.series (Fin.ext (by simp))
  have hn : F s.length = ⊤ := by
    rw [← s.last_eq, RelSeries.last]
    exact congrArg s.series (Fin.ext (by simp))
  have hF : ∀ i < s.length, F i ⋖ F (i + 1) := by
    intro i hi
    convert s.covBy ⟨i, hi⟩ using 2 <;> refine Fin.ext ?_ <;> simp <;> omega
  have hle : ∀ i < s.length, F i ≤ F (i + 1) := by
    intro i hi
    exact (hF i hi).le
  have hF_eq (i : Fin s.length) : F (i.val + 1) = s.series i.succ := by
    dsimp [F]
    congr 1
    apply Fin.ext
    simp
  have hF_eq0 (i : Fin s.length) : F i.val = s.series i.castSucc := by
    dsimp [F]
    congr 1
    apply Fin.ext
    simp
  have hsum : W.IsLisse l (s.semisimplification) := by
    change W.IsLisse l (Representation.directSum (fun i : Fin s.length => s.factor i))
    apply WeilGroup.IsLisse.directSum
    intro i
    exact hLisse.subquotient (s.series i.succ) (s.series i.castSucc)
  have hpoly : ∀ x : C.finitePoints, W.localPolynomial l s.semisimplification x =
      W.localPolynomial l D.asRepresentation x := by
    intro x
    rw [localPolynomial, localPolynomial, LinearMap.charpolyRev, LinearMap.charpolyRev]
    change ((Representation.directSum (fun i : Fin s.length => s.factor i)
      (W.frobenius x)).charpoly).reverse = _
    rw [Representation.charpoly_directSum]
    symm
    rw [LinearMap.charpoly_eq_prod_charpoly_mapQ_of_le
      (D.asRepresentation (W.frobenius x)) (fun i ↦ (F i).toSubmodule) s.length
      (by exact congrArg Subrepresentation.toSubmodule h0)
      (by exact congrArg Subrepresentation.toSubmodule hn)
      (fun i hi ↦ by exact_mod_cast hle i hi)
      (fun i ↦ (F i).apply_mem_toSubmodule (W.frobenius x))]
    rw [← Fin.prod_univ_eq_prod_range]
    apply congrArg Polynomial.reverse
    apply Finset.prod_congr rfl
    intro i _
    rw [hF_eq i, hF_eq0 i]
    simp only [Representation.CompositionSeries.factor]
    rfl
  refine ⟨hsum, fun x m ↦ ?_, hpoly⟩
  rw [hpoly x]
  exact hReal x m

end WeilGroup
end AlgebraicGeometry
