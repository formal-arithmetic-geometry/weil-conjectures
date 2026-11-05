/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolutionDerived
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.MumfordComparison
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.RfPerfect

/-!
# Mumford's complex over a Noetherian affine base

Let `p : Y ⟶ S` be proper of finite presentation over an affine scheme `S` whose ring of global
sections `A = Γ(S, ⊤)` is Noetherian, and `𝒢` an `𝒪_Y`-module of finite presentation, flat over
`S`. Every point of `S` has a basic open neighbourhood `D(a)` over which there is a bounded
complex `P` of finite free `𝒪_{D(a)}`-modules whose pullback along every `g : T' ⟶ D(a)` computes
the higher direct images of the base change of `𝒢`
(`exists_isFiniteFreeComplex_higherDirectImage_of_isNoetherianRing`).

The Čech complex `Č(U, 𝒢)` of a finite affine cover is quasi-isomorphic, compatibly with every
base change, to its truncation, a perfect complex of flat `A`-modules; locally on `Spec A` it is
therefore modelled by a complex of finite free modules
(`CochainComplex.exists_free_away_quasiIso_baseChange`), and the complex of free sheaves with the
same matrices computes the higher direct images after any base change
(`AlgebraicGeometry.Scheme.Modules.nonempty_homology_freeComplexOfBasis_iso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
