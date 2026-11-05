/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGaloisFields
public import WeilConjectures.TraceFormula.Specialization.SliceTraitValuation
public import WeilConjectures.RingTheory.Valuation.GaloisResidueRoot
public import WeilConjectures.RingTheory.Valuation.KummerHensel

/-!

# Hensel's lemma for Kummer equations over the slice compositum

Let `D` be a slice trait with compositum `L = Ω(S(x)) ⊆ Ω'` and valuation subring `𝒪 ⊆ Ω'`,
and let `p` be the residual characteristic.

* `SliceTrait.exists_residual_artinSchreier_root`: every Artin–Schreier equation
  `n ^ p - n = β` with `β ∈ L ∩ 𝒪` has a solution in `L ∩ 𝒪` modulo the maximal ideal of `𝒪`.
  This uses that the residue field of `𝒪` is purely inseparable over the separably closed
  residue field of `R`.
* `SliceTrait.exists_pow_eq_one_add`: in characteristic zero, if `x ∈ L` is negligible, i.e.
  `v(x) ^ (p - 1) ≤ v(p) ^ p`, then `1 + x` is a `p`-th power in `L`.

-/

@[expose] public section

universe u

open IsLocalRing IntermediateField

namespace AlgebraicGeometry.SliceTrait

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

variable {R : Type u} [CommRing R] [IsLocalRing R] {Ω : Type u} [Field Ω] [Algebra R Ω]
  {κ : Type u} [Field κ] {b : R →+* κ} (D : SliceTrait (algebraMap R Ω) b)

end AlgebraicGeometry.SliceTrait
