/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Conventions
public import WeilConjectures.AlgebraicGeometry.CondensedGenericWeil.ConstituentNonexceptional
public import WeilConjectures.AlgebraicGeometry.CondensedAffineLine.MiddleExtensionStatement
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights

/-!
# The weight of the condensed Fourier transform

Source: latest blueprint,
`part-weights-riemann-hypothesis/sec-deligne-laumon-a1/`
`sec-the-weight-of-the-fourier-transform/sk-p-dl-a1-fourier-weight`
(blueprint: sk-p-dl-a1-fourier-weight).

This statement uses the reviewed Q41 affine-line conventions, the reviewed
N9 condensed generic-Weil constituent predicate, and the reviewed NA
Fourier-partner relation on `CondensedAffineLine.Datum`. The native `Pure`
predicate is the punctual-purity predicate supplied by those conventions.
The proof is postponed at stage 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedAffineLine

variable (D : WeilConjectures.FiniteFieldDatum.{u})
variable (ell : ℕ) [Fact ell.Prime]

/-- Let `X` be a nonzero irreducible lisse condensed Weil sheaf on a dense open of the
affine line, constituent-nonexceptional for the nontrivial character `ψ` and punctually
`ι`-pure of weight `w`, and let `Y` be its nonzero irreducible lisse Fourier partner
(`FT_ψ((j_*M)[1]) ≅ (j'_*M')[1]`). Then `Y` is punctually `ι`-pure of weight exactly `w + 1`.

Source: latest blueprint, `part-weights-riemann-hypothesis/sec-deligne-laumon-a1/`
`sec-the-weight-of-the-fourier-transform/sk-p-dl-a1-fourier-weight/_section.md`,
node `sk-p-dl-a1-fourier-weight` (order 747), with the standing hypotheses of the section;
proof `sk-p-dl-a1-fourier-weight.proof.md`. Proof (node steps):
1. By `sk-p-dl-a1-middle` the partner `Y` is nonzero irreducible lisse on a dense open with
   `FT_ψ((j_*M)[1]) ≅ (j'_*M')[1]`; by `sk-p-dl-a1-some-weight` it is punctually pure of some
   real weight `v`.
2. The shift `[1]` multiplies the alternating trace (`sk-def-wrp-l2-definition`) by `-1`, so
   `ν(K[1]) = ν(K)`; isomorphic Weil complexes have equal `ν`, whence
   `ν(FT_ψ((j_*M)[1])) = ν(j'_*M')`.
3. Dense opens of the line are smooth geometrically connected affine curves, so
   `sk-thm-wrp-l2-dictionary` gives `ν(M) = w`, `ν(M') = v`, and `sk-lem-wft-l2-middle` gives
   `ν(j_*M) = w`, `ν(j'_*M') = v`; all are finite.
4. The rank-one Plancherel shift `sk-cor-plancherel` applied to `K = (j_*M)[1]` gives
   `v = ν(j'_*M') = ν(FT_ψ((j_*M)[1])) = ν((j_*M)[1]) + 1 = w + 1`; substitute into step 1.
(blueprint: sk-p-dl-a1-fourier-weight)
-/
theorem pure_weight_add_one
    (hEll : ell ≠ D.p)
    (ψ : AddChar D.k₀ (MonObj.Γ (Λ ell)))
    (hψ : ψ ≠ 1)
    (X Y : Datum D ell)
    (hM : Simple (lisseObject D ell X))
    (hne : CondensedGenericWeil.IsConstituentNonexceptional D (UModel D X.U₀)
      ell X.j₀ (lisse D ell X) ψ)
    (hY : Simple (lisseObject D ell Y))
    (hFT : IsFourierPartner D ell ψ X Y)
    (iota : PadicAlgCl ell →+* ℂ) {w : ℝ}
    (hw : WeilConjectures.NativeL2.Pure D ell (UModel D X.U₀) X.F.obj iota w) :
    WeilConjectures.NativeL2.Pure D ell (UModel D Y.U₀) Y.F.obj iota (w + 1) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedAffineLine
