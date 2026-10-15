/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedBaseChangeNaturality
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets

/-! # Statements of the new targets (batch 2) about `DerivedBaseChangeNaturality`

Kept in their own module so that `Sheaf.AlgebraicGeometry.DerivedBaseChangeNaturality`, which the first task's targets use, is unchanged.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The unbounded derived base-change map is natural in a complex of étale module sheaves.
Source: blueprint, sec-smooth-base-change, sk-def-bc, node sbc-lem-bc-naturality
(blueprint: sbc-lem-bc-naturality).

Proof: expand sbc-def-base-change-map into four arrows `a`, `b`, `c`, `d`: the unit of
`Le* ⊣ Re*` whiskered by `Lf* Rg*`, the two canonical composite-functor identifications,
and the counit of `Lf* ⊣ Rf*`. Write their source and target functors as `F₀`, ..., `F₄`.
Unit naturality and functoriality give `F₀(u) ≫ a(K') = a(K) ≫ F₁(u)`.
Naturality of the two canonical identifications gives
`F₁(u) ≫ b(K') = b(K) ≫ F₂(u)` and `F₂(u) ≫ c(K') = c(K) ≫ F₃(u)`.
Counit naturality gives `F₃(u) ≫ d(K') = d(K) ≫ F₄(u)`.
Substitute these equations successively, using associativity, to move `u` through the
four arrows. Their composite is the recorded `derivedBaseChangeMap` on the exchanged
square `sq.toCommSq.flip`, so the result is precisely the displayed equality.
Equivalently apply the naturality axiom of that natural transformation; no geometric
base-change isomorphism theorem is needed. -/
theorem derivedBaseChangeMap_naturality
    (Λ : Type (u + 1)) [CommRing Λ] {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g)
    {K K' : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (v : K ⟶ K') :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map
        ((R((g)_*[ModuleCat.{u + 1} Λ])).map v) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).app K' =
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).app K ≫
        (R((h)_*[ModuleCat.{u + 1} Λ])).map
          ((L((e)^*[ModuleCat.{u + 1} Λ])).map v) := by
  sorry

end AlgebraicGeometry.Etale

