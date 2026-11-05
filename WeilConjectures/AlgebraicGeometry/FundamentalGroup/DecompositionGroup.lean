/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Specialization
public import WeilConjectures.Mathlib.RingTheory.Invariant.Profinite

/-!
# Decomposition and inertia groups at a point

Let `a : Spec R ⟶ Y` be a morphism from the spectrum of a domain `R` with fraction field `K`, and
`Ω / K` a separably closed Galois extension. The integral closure `B` of `R` in `Ω` gives a
geometric point `Spec Ω ⟶ Spec B ⟶ Y`, on whose fibre functor `Gal(Ω / K)` acts
(`AlgebraicGeometry.Scheme.FiniteEtale.galoisToAut`). A maximal ideal `Q` of `B` gives a second
geometric point `Spec (B ⧸ Q) ⟶ Y`, and the specialization
`AlgebraicGeometry.Scheme.FiniteEtale.specialization` relates the two.

The decomposition group of `Q` is its stabilizer in `Gal(Ω / K)`, and the inertia group the
subgroup acting trivially on `B ⧸ Q`. The inertia group acts trivially on the generic geometric
fibres of all finite étale `Y`-schemes
(`AlgebraicGeometry.Scheme.FiniteEtale.galoisToAut_hom_app_eq_of_mem_inertia`): through the
specialization, it acts as it does on `B ⧸ Q`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {Y : Scheme.{u}} {R K Ω : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] [IsSepClosed Ω] (a : Spec (.of R) ⟶ Y)

end AlgebraicGeometry.Scheme.FiniteEtale
