/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.BirationalCommonDenseOpens
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# A birational morphism is an isomorphism over a dense open

Source: Stacks Project, Morphisms, Tag 0BAJ,
lemma-birational-isomorphism-over-dense-open, separated and locally finitely presented case
(blueprint: lem-sfb-birational-isomorphism-dense-open).
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A separated, locally finitely presented birational morphism between schemes with finitely
many irreducible components is an isomorphism over a dense open of its target. Birationality
means that the given morphism bijects the generic points and induces isomorphisms of their
local rings; neither scheme is assumed reduced.

Source: Stacks Project, Morphisms, Tag 0BAJ,
lemma-birational-isomorphism-over-dense-open, separated and locally finitely presented case
(blueprint: lem-sfb-birational-isomorphism-dense-open).

Proof:
1. Apply [lem-sfb-birational-common-dense-opens] (Stacks 0BAC(2)) to obtain dense opens
   `U` in `Y` and `V` in `X`, with the restriction `g : U ⟶ V` an isomorphism. The open
   inclusion of `U` factors through `W = f ⁻¹ᵁ V` by [def-weil-open-immersion].
2. The restriction `p : W ⟶ V` is separated by [lem-weil-pbc-separated-base-change].
   Compose the inverse of `g` with `U ⟶ W` to obtain a section of `p`. This is a closed
   immersion by [lem-weil-pbc-section-separated-closed-immersion], so its image `U` is
   closed in `W` by [def-weil-closed-immersion].
3. Since `U` is dense in `Y` and `W` is open, `U` is dense in `W`. Closedness therefore
   gives `U = W`. Their open subscheme structures agree by [def-weil-open-immersion],
   and `p` is the isomorphism `g`. This also covers empty schemes.
-/
theorem exists_dense_open_isIso_of_separated_birational
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsSeparated f] [LocallyOfFinitePresentation f]
    (hX : (irreducibleComponents X).Finite) (hY : (irreducibleComponents Y).Finite)
    (hgeneric : Set.BijOn f (genericPoints Y) (genericPoints X))
    (hstalk : ∀ η : Y, η ∈ genericPoints Y → IsIso (f.stalkMap η)) :
    ∃ V : X.Opens, Dense (V : Set X) ∧ IsIso (f ∣_ V) := by
  obtain ⟨U, V, hU, hV, hUV, hg⟩ :=
    exists_common_dense_opens_isIso_of_birational f hX hY hgeneric hstalk
  refine ⟨V, hV, ?_⟩
  have : IsIso (f.resLE V U hUV) := hg
  have : IsClosedImmersion (Y.homOfLE hUV ≫ f ∣_ V) := by
    change IsClosedImmersion (f.resLE V U hUV)
    infer_instance
  have : IsClosedImmersion (Y.homOfLE hUV) :=
    IsClosedImmersion.of_comp _ (f ∣_ V)
  have hrange : Set.range (Y.homOfLE hUV) =
      (f ⁻¹ᵁ V).ι ⁻¹' (U : Set Y) := by
    change ((Y.homOfLE hUV).opensRange : Set (f ⁻¹ᵁ V).toScheme) = _
    rw [Scheme.opensRange_homOfLE]
    rfl
  have hc : IsClosed ((f ⁻¹ᵁ V).ι ⁻¹' (U : Set Y)) := by
    rw [← hrange]
    exact (IsClosedImmersion.isClosedEmbedding (Y.homOfLE hUV)).isClosed_range
  have hd : Dense ((f ⁻¹ᵁ V).ι ⁻¹' (U : Set Y)) :=
    hU.preimage (f ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap
  have heq : U = f ⁻¹ᵁ V := by
    apply le_antisymm hUV
    intro x hx
    have hx' := hd (⟨x, hx⟩ : (f ⁻¹ᵁ V).toScheme)
    rw [hc.closure_eq] at hx'
    exact hx'
  subst U
  simpa only [Scheme.Hom.resLE, Scheme.homOfLE_rfl, Category.id_comp] using hg

end AlgebraicGeometry
