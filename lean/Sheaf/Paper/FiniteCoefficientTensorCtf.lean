/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Algebra.Homology.DerivedTensor
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Paper.FiniteTensorConstructibleCohomology
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite

/-!
# Derived tensor on the finite-Tor constructible subcategory

Source: Weil conjectures blueprint, `sec-six-functors/sk-prop-sf-biduality-general`,
`lem-sf-tensor-ctf`, order 2119 (blueprint: lem-sf-tensor-ctf).

The two derived inputs are expressed by arbitrary cochain representatives `K` and `M`.
The tensor is the recorded `derivedTensor`, using any K-flat resolution `f : P ⟶ K`.
Its defining quasi-isomorphism and K-flatness conditions specify the computation,
without placing any additional condition on the derived inputs.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Tensoring a bounded constructible complex by a finite-Tor constructible complex
preserves bounded constructibility. If both inputs have Tor intervals, the output
is finite-Tor constructible with the sum interval.

Source: Weil blueprint, `sec-six-functors/sk-prop-sf-biduality-general`,
`lem-sf-tensor-ctf`, clauses (i) and (ii), order 2119
(blueprint: lem-sf-tensor-ctf).

Proof:
1. The global datum and `l ≠ D.p` make `l` invertible on the finite-type `D.k`-scheme.
By lem-sf-flat-model choose a flat model of the first input concentrated in `[a,b]`.
It is K-flat by lem-pc-bounded-above-flat-kflat-site. Def-weil-derived-tensor and
lem-weil-derived-tensor-functorial identify the tensor computed on this model with
that computed on any chosen resolution `f : P ⟶ K`.
2. Bounded constructibility of `M` gives cohomological bounds `c' < d'`.
Good upper truncation in degree `d'` uses the kernel of the outgoing differential;
good lower truncation in degree `c'` uses the cokernel of the incoming differential.
Their comparison maps preserve the remaining cohomology and remove only zero
cohomology. They therefore produce a representative concentrated in `[c',d']`.
By def-pc-tensor-complex-sheaves the tensor totalization has terms given by sums
of pairs of terms with degrees adding to the total degree. All terms vanish
outside `[a+c',b+d']`, so the resulting derived tensor has bounded cohomology.
3. Lem-pur-finite-tensor-constructible-cohomology makes every cohomology sheaf
of this tensor constructible: both inputs are bounded constructible over `A_{E,n}`,
`n ≥ 1`, and `l` is invertible on `X`. Together with step 2 this is exactly
def-weil-finite-torsion-constructibility, proving clause (i).
4. For clause (ii) choose also a flat model of `M` concentrated in `[c,d]`,
by lem-sf-flat-model. Tensor associativity identifies the tensor functor of two
flat terms with a composite of exact tensor functors, so their tensor is flat
(def-pc-flat-sheaf-modules). The totalization has only finitely many nonzero
summands in each degree. Tensoring their finite sum is a finite sum of exact
functors; kernels and cokernels are their finite sums, hence the sum is flat.
A nonzero pair of terms requires `a ≤ q ≤ b` and `c ≤ r ≤ d`, giving
`a+c ≤ q+r ≤ b+d`. This is a flat model in the sum interval. The reverse
implication of lem-sf-flat-model gives that Tor interval; clause (i) supplies
bounded constructibility, hence membership in `Dᵇ_ctf` by def-weil-finite-tor-amplitude.
-/
theorem finiteCoefficient_tensor_ctf
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    (K M P : CochainComplex (proEtaleRingModules X
      (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))) ℤ)
    (f : P ⟶ K) (hf : QuasiIso f)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing X (Padic.coefficientExtensionRing l E n)) P)
    (a b : ℤ)
    (_hK : WeilConjectures.finiteTorConstructible l E n hn X (DerivedCategory.Q.obj K))
    (_hKa : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n)
      (DerivedCategory.Q.obj K) a b)
    (_hM : intrinsicFiniteTorsionConstructible l E n hn X (DerivedCategory.Q.obj M)) :
    intrinsicFiniteTorsionConstructible l E n hn X
      (derivedTensor X (Padic.coefficientExtensionRing l E n) K M P f hf hP) ∧
    ∀ c d : ℤ,
      WeilConjectures.finiteTorConstructible l E n hn X (DerivedCategory.Q.obj M) →
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n)
        (DerivedCategory.Q.obj M) c d →
      WeilConjectures.finiteTorConstructible l E n hn X
        (derivedTensor X (Padic.coefficientExtensionRing l E n) K M P f hf hP) ∧
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n)
        (derivedTensor X (Padic.coefficientExtensionRing l E n) K M P f hf hP)
        (a + c) (b + d) := by
  sorry

end AlgebraicGeometry.Scheme
