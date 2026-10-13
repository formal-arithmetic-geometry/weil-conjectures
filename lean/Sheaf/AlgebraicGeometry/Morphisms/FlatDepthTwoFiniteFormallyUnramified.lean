/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.RingTheory.Depth
import Sheaf.RingTheory.DepthLeSupportDimension
import Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatCodimensionOneEtaleNeighbourhood

/-!
# A flat finite depth-two extension is formally unramified

Source: Stacks Project, Tag 0BJH, as applied in Tag 0EY6(3).
(blueprint: lem-sbc-flat-depth-two-finite-formally-unramified)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Flatness removes ramification of a finite depth-two extension of an etale cover.

Source: Stacks Project, Tag 0BJH (pione-lemma-ramification-quasi-finite-flat),
as applied in Tag 0EY6(3) (pione-lemma-extend-S2).
(blueprint: lem-sbc-flat-depth-two-finite-formally-unramified)

Proof: Finiteness over the locally Noetherian target makes E locally Noetherian
and p quasi-finite. At z over U the restriction is etale, hence p is formally
unramified at z. Otherwise depth O(E,z) is at least two, so z is not a generic
point of any irreducible component. Every generalization z' specializing to z
with dim O(E,z') = 1 lies over U: outside U the depth bound would contradict
depth bounded by local dimension. Thus p is unramified at every such z'.
Flatness, quasi-finiteness, the nongeneric condition and this dimension-one
unramifiedness are exactly the four hypotheses of 0BJH, which gives etaleness
at z. Consequently p is formally unramified at every source point, and this
property is local on the source. No target boundary depth, smooth family or
fibre density is needed. Empty sources and U = L are included. -/
theorem formallyUnramified_of_flat_depth_two_finite_extension
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    {E : Scheme.{u}} (p : E ⟶ L) [IsFinite p] [Flat p] [Etale (p ∣_ U)]
    (hboundary : ∀ z : E, p z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z)) :
    FormallyUnramified p := by
  classical
  let : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian p
  have hdim (z : E) :
      (IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z) : WithBot ℕ∞) ≤
        ringKrullDim (E.presheaf.stalk z) := by
    simpa only [Module.supportDim_self_eq_ringKrullDim] using
      IsLocalRing.depth_le_supportDim (R := E.presheaf.stalk z) (E.presheaf.stalk z)
  have hopen : FormallyUnramified ((p ⁻¹ᵁ U).ι ≫ p) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hneighbourhood (z : E) :
      ∃ V : E.Opens, z ∈ V ∧ FormallyUnramified (V.ι ≫ p) := by
    by_cases hz : p z ∈ U
    · exact ⟨p ⁻¹ᵁ U, hz, hopen⟩
    · have htwo : (2 : WithBot ℕ∞) ≤ ringKrullDim (E.presheaf.stalk z) :=
        (WithBot.coe_le_coe.mpr (hboundary z hz)).trans (hdim z)
      have hunram (z' : E) (_ : Specializes z' z)
          (hdimOne : ringKrullDim (E.presheaf.stalk z') = 1) :
          ∃ V : E.Opens, z' ∈ V ∧ FormallyUnramified (V.ι ≫ p) := by
        have hz'U : p z' ∈ U := by
          by_contra hz'
          have hbad : (2 : WithBot ℕ∞) ≤ (1 : WithBot ℕ∞) := by
            simpa only [hdimOne, WithBot.coe_ofNat] using
              (WithBot.coe_le_coe.mpr (hboundary z' hz')).trans (hdim z')
          norm_num at hbad
        exact ⟨p ⁻¹ᵁ U, hz'U, hopen⟩
      obtain ⟨V, hzV, hV⟩ :=
        exists_etale_neighbourhood_of_finite_flat_of_codimension_one p z
          (lt_of_lt_of_le (by norm_num) htwo) hunram
      let := hV
      exact ⟨V, hzV, inferInstance⟩
  choose V hzV hV using hneighbourhood
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @FormallyUnramified) V
    (eq_top_iff.mpr (fun z _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hzV z⟩))
  exact hV

end AlgebraicGeometry.Scheme
