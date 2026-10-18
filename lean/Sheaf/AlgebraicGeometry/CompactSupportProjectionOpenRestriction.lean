/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Sheaf.AlgebraicGeometry.CompactProjectionExchange

/-!
# Compact-support projection and open restriction

Source: Stacks Project, more-etale.tex Tag 0F7L (lemma-base-change-shriek) and
sites-cohomology.tex Tag 0E48 (remark-compatible-with-diagram)
(blueprint: lem-amb-shriek-projection-open-restriction).

The coefficient-first projection map is `compactProjectionMapCoeffFirst`, built from the
proper projection map and open tensor comparison, with the canonical signed symmetries.
The exchange is the normalized compactification-independent
`rightDerivedLowerShriekBaseChangeMap`. Exact constant-coefficient inverse image identifies
its total left derived functor with the termwise functor. Thus the derived pullback tensor
comparisons below are exactly the monoidal identifications in the node's display.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The actual coefficient-first compactified projection maps commute with restriction to
an open subscheme of the base, on arbitrary unbounded complexes.
Source: Stacks Project, Tags 0F7L and 0E48
(blueprint: lem-amb-shriek-projection-open-restriction).
Proof: (1) specialize `compactProjectionMapCoeffFirst_baseChangeMap`
[lem-asd-compact-projection-exchange] to `IsPullback.of_hasPullback f u`. Its projection map
is precisely the proper/open compactified map with the coefficient first, and its exchange
is the compactified exchange. (2) The refinement comparisons of
[lem-amb-unbounded-compact-support-comparisons] identify these with the canonical functors
and maps independently of compactification. The proper factor is normalized by
[def-kun-unbounded-exchange] and the open factor by
[def-weil-pbc-etale-shriek-base-change-map]. The open tensor identification is
[lem-pur-etale-open-derived-tensor]; the tensor pullback transports are those of
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. These identifications give exactly
the four-factor equality below, without any amplitude restriction. -/
theorem compactSupportProjection_open_restriction
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S U : Scheme.{u}} [IsNoetherian X] [IsNoetherian S] [IsNoetherian U]
    (f : X ⟶ S) (u : U ⟶ S) [IsOpenImmersion u]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (K : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((u)^*[ModuleCat.{u + 1} Λ]).map (compactProjectionMapCoeffFirst Λ f K M) ≫
        (rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.of_hasPullback f u)).app
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj K)).obj M) ≫
        (R(pullback.snd f u)_![ModuleCat.{u + 1} Λ]).map
          (((leftDerivedUpperStarTensorComparison _ (pullback.fst f u)).app
            (L((f)^*[ModuleCat.{u + 1} Λ]).obj K)).app M) ≫
        (R(pullback.snd f u)_![ModuleCat.{u + 1} Λ]).map
          (((-⊗ᴸ-(pullback f u)[ModuleCat.{u + 1} Λ]).map
            (derivedSquareUpperStarIsoInvApp _ (IsPullback.of_hasPullback f u).toCommSq K)).app
              (L((pullback.fst f u)^*[ModuleCat.{u + 1} Λ]).obj M)) =
      ((leftDerivedUpperStarTensorComparison _ u).app K).app
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj M) ≫
        ((-⊗ᴸ-(U)[ModuleCat.{u + 1} Λ]).obj (L((u)^*[ModuleCat.{u + 1} Λ]).obj K)).map
          ((rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.of_hasPullback f u)).app M) ≫
        compactProjectionMapCoeffFirst Λ (pullback.snd f u) (L((u)^*[ModuleCat.{u + 1} Λ]).obj K)
          (L((pullback.fst f u)^*[ModuleCat.{u + 1} Λ]).obj M) := by
  exact compactProjectionMapCoeffFirst_baseChangeMap Λ (IsPullback.of_hasPullback f u) M K

/-- The corresponding identity for inverse projection maps, if both projection maps are
isomorphisms. No extra invertibility assumption on the exchange is needed.
Source: Stacks Project, Tags 0F7L and 0E48
(blueprint: lem-amb-shriek-projection-open-restriction).
Proof: (3) precompose the preceding equality with the image under inverse image of the
inverse projection map for `f`, and postcompose with the inverse projection map for the
base change. Functoriality, the two inverse identities and associativity cancel the two
projection maps, giving the displayed equation. Compactification independence is inherited
from the same normalized maps as in the preceding theorem. -/
theorem compactSupportProjection_open_restriction_inverse
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S U : Scheme.{u}} [IsNoetherian X] [IsNoetherian S] [IsNoetherian U]
    (f : X ⟶ S) (u : U ⟶ S) [IsOpenImmersion u]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (K : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsIso (compactProjectionMapCoeffFirst Λ f K M)]
    [IsIso (compactProjectionMapCoeffFirst Λ (pullback.snd f u)
      (L((u)^*[ModuleCat.{u + 1} Λ]).obj K)
      (L((pullback.fst f u)^*[ModuleCat.{u + 1} Λ]).obj M))] :
        (rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.of_hasPullback f u)).app
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj K)).obj M) ≫
        (R(pullback.snd f u)_![ModuleCat.{u + 1} Λ]).map
          (((leftDerivedUpperStarTensorComparison _ (pullback.fst f u)).app
            (L((f)^*[ModuleCat.{u + 1} Λ]).obj K)).app M) ≫
        (R(pullback.snd f u)_![ModuleCat.{u + 1} Λ]).map
          (((-⊗ᴸ-(pullback f u)[ModuleCat.{u + 1} Λ]).map
            (derivedSquareUpperStarIsoInvApp _ (IsPullback.of_hasPullback f u).toCommSq K)).app
              (L((pullback.fst f u)^*[ModuleCat.{u + 1} Λ]).obj M)) ≫
      inv (compactProjectionMapCoeffFirst Λ (pullback.snd f u)
          (L((u)^*[ModuleCat.{u + 1} Λ]).obj K)
          (L((pullback.fst f u)^*[ModuleCat.{u + 1} Λ]).obj M)) =
    L((u)^*[ModuleCat.{u + 1} Λ]).map (inv (compactProjectionMapCoeffFirst Λ f K M)) ≫
      ((leftDerivedUpperStarTensorComparison _ u).app K).app
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj M) ≫
        ((-⊗ᴸ-(U)[ModuleCat.{u + 1} Λ]).obj (L((u)^*[ModuleCat.{u + 1} Λ]).obj K)).map
          ((rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.of_hasPullback f u)).app M) := by
  have h := compactSupportProjection_open_restriction Λ f u K M
  have h' := congrArg
    (fun e ↦ L((u)^*[ModuleCat.{u + 1} Λ]).map
      (inv (compactProjectionMapCoeffFirst Λ f K M)) ≫ e ≫
        inv (compactProjectionMapCoeffFirst Λ (pullback.snd f u)
          (L((u)^*[ModuleCat.{u + 1} Λ]).obj K)
          (L((pullback.fst f u)^*[ModuleCat.{u + 1} Λ]).obj M))) h
  simpa only [Functor.map_inv, Category.assoc, IsIso.inv_hom_id_assoc,
    IsIso.hom_inv_id, Category.comp_id] using h'

end AlgebraicGeometry.Etale
