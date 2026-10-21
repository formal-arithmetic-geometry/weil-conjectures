module

public import Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts
public import Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology

/-! Declarations of ours that lived in the upstream file `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!
# The proper direct image for the `ℓ`-adic coefficient rings: the inputs

Let `ℓ` be a prime, `k` a field in which `ℓ` is invertible, and `p : Z ⟶ Y` a proper morphism to
a noetherian `k`-scheme. For the `ℓ`-adic condensed coefficient rings `Λ = E, 𝒪_E, ℚ̄_ℓ`, the
properties of the derived direct image `Rp_*` on module objects over `Λ` used for the
compact-support direct image on `Loc(Dᵇc)` (blueprint `det-sf-comp-coherence-single`) are:

* `Rp_*` maps `Dᵇc(Z)⟦Λ⟧` into `Dᵇc(Y)⟦Λ⟧` (blueprint `sk-thm-sfb-proper-base-change`):
  `boundedConstructible_rightDerivedLowerStar_obj_of_isProper_continuousMapRingObj`,
  `boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicIntegersRingObj`,
  `boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj`;
* `Rp_*` has finite amplitude on the ind-constructible heart and commutes with direct sums there
  (`AlgebraicGeometry.ProEtale.CondensedRing.ProperLowerStarHeartHypotheses`, blueprints
  `sk-lem-proper-heart-bound` for `E` and `ℚ̄_ℓ`, `det-prop-int-compactness-direct-sums` (1) for
  `𝒪_E`): `properLowerStarHeartHypotheses_continuousMapRingObj`,
  `properLowerStarHeartHypotheses_padicIntegersRingObj`,
  `properLowerStarHeartHypotheses_padicAlgClRingObj`.

From the latter, the restriction of `Rp_*` to `Loc(Dᵇc(Z)⟦Λ⟧)` preserves direct sums
(`AlgebraicGeometry.ProEtale.CondensedRing.ProperLowerStarHeartHypotheses.preservesColimitsOfShape`,
blueprint `det-prop-int-compactness-direct-sums` (2), (3), proved by dévissage and left
completeness).

## Sorried input

All six statements above are `sorry`ed: they are the ℓ-adic finiteness theorems for proper
morphisms (Bhatt–Scholze, Section 6.8), which rest on the reduction to torsion coefficients via
derived completeness, the étale finiteness and cohomological dimension theorems for proper
morphisms, and the Milnor sequence.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

private theorem properLowerStarHeartHypotheses_of_uniformBound
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p]
    (hb : ∃ d : ℤ, ∀ M, constructibleCoproductClosure Λ Z M →
      (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE d) :
    ProperLowerStarHeartHypotheses Λ p := by
  refine ⟨hb, fun J N _ ↦ ?_⟩
  have := condensed_boundedBelow_preservesCoproduct Λ p J 0
    (fun j ↦ (DerivedCategory.singleFunctor _ 0).obj (N j))
    (fun j ↦ inferInstance)
  exact inferInstanceAs (IsIso (sigmaComparison R((p)_*⟦Λ⟧)
    (fun j ↦ (DerivedCategory.singleFunctor _ 0).obj (N j))))

private theorem bounded_rightDerivedLowerStar_of_uniformBound
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (hb : ∃ d : ℤ, ∀ M, constructibleCoproductClosure Λ Z M →
      (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE d)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) (hK : boundedConstructible _ K) :
    DerivedCategory.TStructure.t.bounded (R((p)_*⟦Λ⟧).obj K) := by
  obtain ⟨d, hd⟩ := hb
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.1
  have : K.IsGE a := ha
  have : K.IsLE b := hb
  refine ⟨⟨a, Functor.isGE_rightDerivedFunctor_obj _ K a⟩, ⟨b + d, ?_⟩⟩
  exact DerivedCategory.isLE_obj_of_isLE_of_homologyProperty R((p)_*⟦Λ⟧) d
    (constructibleCoproductClosure Λ Z) hd K hK.1
    (fun n ↦ ObjectProperty.le_weakSerreCoproductClosure _ _ (hK.2 n)) b

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]

/-! ### The coefficient ring `E` -/

include ℓ in
include ℓ in
/-! ### The coefficient ring `𝒪_E` -/

include ℓ in
/-! ### The coefficient ring `ℚ̄_ℓ` -/

end AlgebraicGeometry.ProEtale.CondensedRing
