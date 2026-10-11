module

public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # Tensoring a quasi-coherent module by an invertible module

Source: literature/stacks-project/coherent.tex, Cohomology of Schemes, Lemma 09MR
(blueprint: lem-sc-invertible-tensor-qcoherent).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/--
For a quasi-coherent module and an invertible module, tensoring by every integer
power of the invertible module is quasi-coherent. The nonnegative power is
`L.tensorPow n`; the negative power is `(dual L).tensorPow (-n)`.
Source: literature/stacks-project/coherent.tex, Cohomology of Schemes, Lemma 09MR
(blueprint: lem-sc-invertible-tensor-qcoherent).
Proof: the dual and tensor-product closure clauses of
`lem-pc-tensor-dual-invertible` make every integer power invertible. The
quasi-coherent tensor-product theorem
`lem-weil-pbc-quasi-coherent-tensor-product-affine-sections` then gives the
conclusion for `F` and each power.
-/
theorem isQuasicoherent_tensor_integer_power {X : Scheme.{u}} (F L : X.Modules)
    [F.IsQuasicoherent] [L.IsInvertible] (n : ℤ) :
    (tensorObj F (if h : 0 ≤ n then L.tensorPow n.toNat else
      (dual L).tensorPow (-n).toNat)).IsQuasicoherent := by
  sorry

end AlgebraicGeometry.Scheme.Modules
