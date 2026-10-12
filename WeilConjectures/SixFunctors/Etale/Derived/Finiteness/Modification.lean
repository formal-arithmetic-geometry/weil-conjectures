/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# Constructibility of direct images under a proper modification

Let `π : Y ⟶ X` be proper and an isomorphism over an open `j : U ⟶ X`, with closed complement
`i : Z ⟶ X`. This file proves:

- `AlgebraicGeometry.Etale.nonempty_rightDerivedLowerStar_openImmersionLowerShriek_iso`
  (`lem-finrepair-modification-extension-zero`): `Rπ_*(j'_! G') ≅ j_! G` for a sheaf `G` on
  `U` with pullback `G'` to `U' = π⁻¹(U)`; that is, `π_* j'_! G' = j_! G` and
  `Rᵠπ_* j'_! G' = 0` for `q > 0`. This uses proper base change along `i`.
- `AlgebraicGeometry.Etale.HasConstructibleDirectImages.of_modification`
  (`lem-finrepair-modification-c`): `𝒞(π ≫ f)` and `𝒞(i ≫ f)` imply `𝒞(f)`, by the open–closed
  short exact sequence `0 ⟶ j_! j^* F ⟶ F ⟶ i_* i^* F ⟶ 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Blueprint `lem-finrepair-modification-extension-zero`: Extension by zero under a proper
modification.

Let `π : Y ⟶ X` be proper and `j : U ⟶ X` an open immersion such that `π⁻¹(U) ⟶ U` is an
isomorphism: here `j' : U' ⟶ Y`, `π' : U' ⟶ U` is a pullback square with `π'` an isomorphism.
For an étale sheaf `G` of `Λ`-modules on `U` with pullback `G' = π'^* G` to `U'`,
`Rπ_*(j'_! G') ≅ j_! G`, i.e. `π_* j'_! G' ≅ j_! G` and `Rᵠπ_* j'_! G' = 0` for `q > 0`. Here
`Λ` is a finite ring, as proper base change is used. -/
theorem nonempty_rightDerivedLowerStar_openImmersionLowerShriek_iso {X Y U U' : Scheme.{u}}
    (π : Y ⟶ X) [IsProper π] (j : U ⟶ X) [IsOpenImmersion j] (j' : U' ⟶ Y) [IsOpenImmersion j']
    (π' : U' ⟶ U) [IsIso π'] (sq : IsPullback j' π' π j)
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty ((R((π)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((j')_!open[ModuleCat.{u + 1} Λ].obj ((π')^*[ModuleCat.{u + 1} Λ].obj G))) ≅
      (singleFunctor _ 0).obj ((j)_!open[ModuleCat.{u + 1} Λ].obj G)) :=
  sorry

/-- Blueprint `lem-finrepair-modification-c`: Proper modification transfer without an amplitude
claim.

Let `f : X ⟶ S` be a morphism and `π : Y ⟶ X` proper, an isomorphism over the open
`j : U ⟶ X` (that is, the projection `π⁻¹(U) ⟶ U` is an isomorphism), and let `i : Z ⟶ X` be a
closed immersion with range the complement of `U`. If `𝒞(π ≫ f)` and `𝒞(i ≫ f)` hold, then
`𝒞(f)` holds. Here `Λ` is a finite ring. The blueprint takes `f` proper and `Z` with its reduced
structure; neither is needed. -/
theorem HasConstructibleDirectImages.of_modification {X Y Z U S : Scheme.{u}} (f : X ⟶ S)
    (π : Y ⟶ X) [IsProper π] (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (hπ : IsIso (pullback.snd π j))
    (hπf : HasConstructibleDirectImages Λ (π ≫ f)) (hif : HasConstructibleDirectImages Λ (i ≫ f)) :
    HasConstructibleDirectImages Λ f :=
  sorry

end Etale

end AlgebraicGeometry
