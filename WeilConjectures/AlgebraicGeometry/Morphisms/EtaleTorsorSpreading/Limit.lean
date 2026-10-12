/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.Datum

/-!
# Reduction of the spreading theorem to a Noetherian base

The spreading theorem (blueprint `sbc-thm-spreading-finite-etale-galois`, [Stacks 0EZJ]) for a
qcqs integral normal base follows from the Noetherian case ([Stacks 0EYJ]) by a limit argument
(`AlgebraicGeometry.Scheme.SpreadingDatum.exists_isFinite_etale_isPullback_of_isNoetherian`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.SpreadingDatum

variable {G : Type (u + 1)} [Group G] [Finite G]

/-- Step of the proof of blueprint `sbc-thm-spreading-finite-etale-galois` (the limit argument
of [Stacks 0EZJ]): if the Galois cover of the generic fibre extends to a finite étale cover for
every spreading datum over a Noetherian base, it does so for every spreading datum.

Proof sketch ([Stacks 0EZJ]). Write `S = lim S_i` as a directed limit with affine transition
maps of schemes of finite type over `ℤ` ([Stacks 01ZA], absolute Noetherian approximation), and
replace `S_i` by the normalization `S'_i` of `S_i` in `S`; it is finite over `S_i` and normal
integral of finite type over `ℤ` (Nagata: `ℤ` is universally Japanese, [Stacks 0335]), and
`S = lim S'_i`. For some `i`, `c` descends to a smooth `C_i ⟶ S_i` of finite presentation
([Stacks 01ZM] and Limits, Section 32.8), `σ` to a section `σ_i`, and after replacing
`C_i` by the open union `C_i^0` of the connected components of the fibres meeting `σ_i`
([Stacks 055R]) the fibres are geometrically connected; `|G|` becomes invertible on `S_i`.
The generic fibre `C_η` is the limit of the `C_{i, η_i}`, so `Z` with its `G`-action and its
rational point over `σ(η)` descend to a Galois cover `Z_i` of `C_{i, η_i}`. The Noetherian case
gives a finite étale extension `Y_i` of `Z_i` over `C_i`, and `Y_i ×_{C_i} C` extends `Z`.

Status: this step is left open. The base cannot be taken Noetherian in the application: the
vanishing theorem (`AlgebraicGeometry.Etale.exists_etaleTorsor_cohomologyMap_eq_zero`) applies it
to the base of a curve-test datum, which is the spectrum of the integral closure of an arbitrary
ring in an algebraically closed field. Even for affine `S` and `C` the argument needs
infrastructure that is not available: that finitely generated `ℤ`-domains are Japanese
([Stacks 0335], to keep the approximating `S'_i` Noetherian *and* normal), the descent of
smooth morphisms with geometrically connected fibres and of Galois covers of the generic fibre
along the limit, and the general (non-affine) absolute Noetherian approximation. Only its affine
case `AlgebraicGeometry.exists_isLimit_isNoetherian_Spec` and the descent of finite étale
algebras (`AlgebraicGeometry.exists_finset_algEquiv_tensorProduct_of_finite_of_etale`) exist. -/
theorem exists_isFinite_etale_isPullback_of_isNoetherian
    (H : ∀ D' : SpreadingDatum.{u} G, IsNoetherian D'.S →
      ∃ (Y : Scheme.{u}) (p : Y ⟶ D'.C) (_ : IsFinite p) (_ : Etale p) (ψ : D'.Z.P ⟶ Y),
        IsPullback ψ D'.Z.π p D'.j)
    (D : SpreadingDatum.{u} G) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ D.C) (_ : IsFinite p) (_ : Etale p) (ψ : D.Z.P ⟶ Y),
      IsPullback ψ D.Z.π p D.j :=
  sorry

end AlgebraicGeometry.Scheme.SpreadingDatum
