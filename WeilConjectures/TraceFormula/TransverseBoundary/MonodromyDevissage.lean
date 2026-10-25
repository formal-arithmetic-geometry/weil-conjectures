/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisCoverConnected
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.TraceFormula.TransverseBoundary.Basic

/-!
# Dévissage of complexes with finite `ℓ`-group monodromy

Let `V` be a connected scheme, `ℓ` a prime and `Λ` a finite commutative ring with `ℓ` nilpotent
in `Λ`. Every sheaf `H` of `Λ`-modules on `V_ét` with finite `ℓ`-group monodromy
(`AlgebraicGeometry.Etale.HasFiniteEllGroupMonodromy`) is an iterated extension of constant
sheaves `N_V` with `N` a finite `Λ`-module killed by `ℓ`: after replacing the trivializing Galois
cover by a connected subcover (`AlgebraicGeometry.Scheme.GaloisCover.exists_connected_subcover`),
the `ℓ`-group `G` acts `Λ`-linearly on the nonzero finite `ℓ`-group `M = Γ(P, π^* H)` and has a
nonzero fixed vector `v` with `ℓ v = 0`; the fixed vector descends to a section of `H` over `V`,
which spans an injection `(Λ v)_V ↪ H` whose cokernel is trivialized by the same cover with the
smaller value `M / Λ v`. By induction on the cardinality of `M`, and by truncation for bounded
complexes, a property of objects of `D(V_ét, Λ)` stable under isomorphisms, shifts and extensions
which holds for these constant sheaves holds for every bounded complex whose cohomology sheaves
have finite `ℓ`-group monodromy (blueprint `det-tf-transverse-corner-vanishing`, dévissage).

## Main statements

- `AlgebraicGeometry.Etale.prop_singleFunctor_of_hasFiniteEllGroupMonodromy`: the dévissage for
  sheaves.
- `AlgebraicGeometry.Etale.prop_of_isBoundedFiniteEllGroupMonodromy`: the dévissage for bounded
  complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime] {Λ : Type (u + 1)}
  [CommRing Λ] [Finite Λ] (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)
  (P : ObjectProperty (DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
  [P.IsClosedUnderIsomorphisms]
  (hshift : ∀ (K : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ),
    P K → P (K⟦n⟧))
  (hext : ∀ T ∈ distTriang (DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
    P T.obj₁ → P T.obj₃ → P T.obj₂)
  (hconst : ∀ (N : ModuleCat.{u + 1} Λ), Finite N → (∀ n : N, (ℓ : Λ) • n = 0) →
    P ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)))

include hΛ hext hconst in
/-- **Dévissage of sheaves with finite `ℓ`-group monodromy** (blueprint
`det-tf-transverse-corner-vanishing`): on a connected scheme, a property of objects of
`D(V_ét, Λ)` stable under isomorphisms and extensions which holds for the constant sheaves `N_V`,
`N` a finite `Λ`-module killed by `ℓ`, holds for every sheaf with finite `ℓ`-group monodromy,
placed in degree `0`. -/
theorem prop_singleFunctor_of_hasFiniteEllGroupMonodromy
    (H : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hH : HasFiniteEllGroupMonodromy ℓ H) :
    P ((DerivedCategory.singleFunctor _ 0).obj H) := by
  sorry

include hΛ hshift hext hconst in
/-- **Dévissage of complexes with finite `ℓ`-group monodromy** (blueprint
`det-tf-transverse-corner-vanishing`): on a connected scheme, a property of objects of
`D(V_ét, Λ)` stable under isomorphisms, shifts and extensions which holds for the constant
sheaves `N_V`, `N` a finite `Λ`-module killed by `ℓ`, holds for every bounded complex whose
cohomology sheaves have finite `ℓ`-group monodromy. -/
theorem prop_of_isBoundedFiniteEllGroupMonodromy
    (E : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : IsBoundedFiniteEllGroupMonodromy ℓ E) : P E := by
  sorry

end AlgebraicGeometry.Etale
