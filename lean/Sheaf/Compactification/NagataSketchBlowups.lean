/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Blowup.Extension
import Sheaf.Compactification.BoundaryRefinement

/-!
# Finite refinements of admissible blow-ups

Source: blueprint main-20261015, sec-nagata-compactification,
`sk-lem-nagata-sketch-blowups/_section.md`, Stacks Project Tags 080A, 080B and 080M
(blueprint: sk-lem-nagata-sketch-blowups).

The statement has three clauses. First, a finite family of `U`-admissible blow-ups of a
quasi-compact quasi-separated scheme `T` is dominated by one such blow-up. Second, the
composition of an admissible blow-up with one admissible over the pulled-back open is
admissible. Third, an admissible blow-up over a quasi-compact open `V` containing `U`
extends across `V`; the displayed pullback condition records that its restriction is the
original blow-up. This module records the statement only; the proof is deferred to
the stage-3 proof node.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Finite refinements, composition, and extension of admissible blow-ups.

Source: blueprint main-20261015, sec-nagata-compactification,
`sk-lem-nagata-sketch-blowups/_section.md`, Stacks Project Tags 080A, 080B and 080M
(blueprint: sk-lem-nagata-sketch-blowups).

Proof plan, following the node's two proof paragraphs:
1. For a finite family, multiply the finite-type center ideals. The blow-up of the product
   dominates each member because after the product becomes invertible every factor is
   invertible; induction gives the finite-family assertion. The composition clause uses
   the finite-type ideal calculation of Tag 080B, expressed by the canonical isomorphism.
2. For extension, extend the finite-type quasi-coherent ideal from the quasi-compact open
   and multiply by a finite-type ideal cutting out the complement of the larger open. The
   resulting center remains disjoint from `U`; Tag 080M gives the displayed pullback.
-/
theorem nagata_sketch_blowups {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    {U : T.Opens} (hU : IsCompact (U : Set T)) :
    (∀ (n : ℕ) (B : Fin n → IsAdmissible T U),
      ∃ (C : IsAdmissible T U)
        (m : ∀ i : Fin n, C.I.blowup ⟶ (B i).I.blowup),
        ∀ i : Fin n, m i ≫ (B i).I.blowupMap = C.I.blowupMap) ∧
    (∀ (B₁ : IsAdmissible T U)
        (B₂ : IsAdmissible B₁.I.blowup (B₁.I.blowupMap ⁻¹ᵁ U)),
      ∃ (C : IsAdmissible T U) (e : B₂.I.blowup ≅ C.I.blowup),
        e.hom ≫ C.I.blowupMap = B₂.I.blowupMap ≫ B₁.I.blowupMap) ∧
    (∀ (V : T.Opens) (hV : IsCompact (V : Set T)) (hUV : U ≤ V)
        (J : V.toScheme.IdealSheafData) (hJ : J.ofFiniteType)
        (hdisj : Disjoint ((V.ι ⁻¹ᵁ U : V.toScheme.Opens) : Set V.toScheme)
          (J.support : Set V.toScheme)),
      ∃ (B : IsAdmissible T U) (h : J.blowup ⟶ B.I.blowup),
        h ≫ B.I.blowupMap = J.blowupMap ≫ V.ι ∧
          IsPullback J.blowupMap h V.ι B.I.blowupMap) := by
  sorry

end AlgebraicGeometry
