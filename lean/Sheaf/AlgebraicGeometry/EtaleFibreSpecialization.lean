/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Specialization bound for geometric fibres of separated étale morphisms

Source: literature/stacks-project/more-morphisms.tex, Lemma 37.45.7 (Tag 09Z0)
(blueprint: lem-weil-pbc-etale-fibre-specialization-bound).

The geometric fibre of `f : X ⟶ Y` over a geometric point `ȳ : Spec Ω ⟶ Y` is the fibre
product `pullback f ȳ` (def-weil-geometric-fibre); its cardinality is the number of points of
its underlying space.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The geometric fibre of a quasi-compact separated étale morphism cannot increase in
cardinality under specialization (Stacks, Lemma 37.45.7, Tag 09Z0)
(blueprint: lem-weil-pbc-etale-fibre-specialization-bound).

Proof:
1. Work over an affine open of `Y` containing the image of the specialization. The étale
   morphism is flat and locally of finite presentation, and its separated quasi-compact
   restriction is quasi-finite, so the flat, finitely presented, quasi-finite stratification
   (lem-weil-pbc-flat-fp-qf-stratification, Stacks 07RZ) applies.
2. Its strata `S_r = Z_r \ Z_{r-1}` satisfy: the fibre over `y` is finite locally free of
   degree `r` exactly when `y ∈ S_r`. The fibre `X_y` is étale and finite over `κ(y)`, hence
   the spectrum of a finite product of finite separable field extensions
   (lem-weil-pbc-etale-algebra-over-field-product), so this degree is the number of points of
   the geometric fibre; the locus of geometric fibre cardinality at most `r` is the closed set
   `Z_r`.
3. If the generic geometric fibre has finite cardinality `r`, then `y_gen ∈ Z_r`; closed sets
   are stable under specialization, so `y_sp ∈ Z_r`. -/
theorem etale_geometricFiber_card_le_of_specializes
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsSeparated f] [Etale f]
    {Ωgen Ωsp : Type u} [Field Ωgen] [IsAlgClosed Ωgen] [Field Ωsp] [IsAlgClosed Ωsp]
    (ygen : Spec (.of Ωgen) ⟶ Y) (ysp : Spec (.of Ωsp) ⟶ Y)
    (hsp : ygen (default : Spec (.of Ωgen)) ⤳ ysp (default : Spec (.of Ωsp)))
    [Finite ↥(pullback f ygen : Scheme.{u})] :
    Finite ↥(pullback f ysp : Scheme.{u}) ∧
      Nat.card ↥(pullback f ysp : Scheme.{u}) ≤ Nat.card ↥(pullback f ygen : Scheme.{u}) := by
  sorry

/-- If the geometric fibres over a dense open have cardinality strictly below `d`, then all
geometric fibres have cardinality strictly below `d` (Stacks, Lemma 37.45.7, Tag 09Z0)
(blueprint: lem-weil-pbc-etale-fibre-specialization-bound).

Proof: on each affine open `V` of `Y`, the stratification of steps 1-2 above gives a closed
subset `Z_{d-1}` of `V`, the locus where the geometric fibre has cardinality less than `d`.
It contains the dense subset `U ∩ V` of `V`, hence equals `V`. These affine opens cover `Y`,
so every geometric fibre has cardinality strictly less than `d`. -/
theorem etale_geometricFiber_card_lt_of_dense_open
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsSeparated f] [Etale f]
    (U : Set Y) (hUopen : IsOpen U) (hUdense : Dense U) (d : ℕ)
    (hU : ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ Y), y (default : Spec (.of Ω)) ∈ U →
        Finite ↥(pullback f y : Scheme.{u}) ∧ Nat.card ↥(pullback f y : Scheme.{u}) < d) :
    ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ Y),
      Finite ↥(pullback f y : Scheme.{u}) ∧ Nat.card ↥(pullback f y : Scheme.{u}) < d := by
  sorry

end AlgebraicGeometry
