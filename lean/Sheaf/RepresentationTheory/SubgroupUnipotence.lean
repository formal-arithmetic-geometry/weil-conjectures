/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Algebra.Operations

/-!
# Unipotence and augmentation powers for a subgroup

Source: ILO, Expose XVII, Definitions 11.1.1–11.1.2, Proposition 11.2.1(vi)–(xi)
and Propositions 11.3.1–11.3.4, pp. 327–330
(blueprint: def-per-normal-subgroup-unipotence).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Rep

variable {R : Type u} [CommRing R] {G : Type v} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- Finite increasing filtrations by G-stable submodules with H-trivial successive quotients.
The difference condition states triviality on the quotient without choosing quotient actions.
Source: ILO XVII 11.1.1 and 11.3.1
(blueprint: def-per-normal-subgroup-unipotence). -/
def IsSubgroupUnipotent (H : Subgroup G) (M : DiscreteContinuousRep.{u, v, w} R G) : Prop :=
  ∃ (n : ℕ) (F : ℕ → Submodule R M.obj.V),
    F 0 = ⊥ ∧ F n = ⊤ ∧ Monotone F ∧
    (∀ (i : ℕ) (g : G) (m : M.obj.V), m ∈ F i → M.obj.ρ g m ∈ F i) ∧
    (∀ (i : ℕ), i < n → ∀ (h : H) (m : M.obj.V),
      m ∈ F (i + 1) → M.obj.ρ h.val m - m ∈ F i)

/-- The augmentation ideal of R[H], viewed as an R-submodule of its group algebra.
The augmentation is the algebra homomorphism sending each group element to 1;
its kernel is a two-sided ideal even when H is noncommutative.
Source: ILO XVII 11.1 and 11.3
(blueprint: def-per-normal-subgroup-unipotence). -/
noncomputable def subgroupAugmentationIdeal (H : Subgroup G) :
    Submodule R (MonoidAlgebra R H) :=
  LinearMap.ker ((MonoidAlgebra.lift R R H) 1).toLinearMap

/-- Powers of the augmentation ideal as R-submodules, with zeroth power the whole algebra.
The recursive product is the R-span of products, which is the ideal product for the
(two-sided) augmentation ideal. This also fixes the literal degree-zero convention.
Source: ILO XVII 11.2.1(vi)–(vii), 11.3.4
(blueprint: def-per-normal-subgroup-unipotence). -/
noncomputable def subgroupAugmentationPower (H : Subgroup G) :
    ℕ → Submodule R (MonoidAlgebra R H)
  | 0 => ⊤
  | q + 1 => subgroupAugmentationIdeal (R := R) H * subgroupAugmentationPower H q

/-- An augmentation power annihilates a vector in the restricted H-representation.
Source: ILO XVII 11.2.1(vi)–(vii), 11.3.4
(blueprint: def-per-normal-subgroup-unipotence). -/
def SubgroupAugmentationKills (H : Subgroup G)
    (M : DiscreteContinuousRep.{u, v, w} R G) (q : ℕ) (m : M.obj.V) : Prop :=
  ∀ a ∈ subgroupAugmentationPower (R := R) H q,
    Representation.asAlgebraHom (M.obj.ρ.comp H.subtype) a m = 0

/-- Ind-unipotent discrete modules for H, as actual filtered colimits of unipotent objects.
This uses Mathlib's `ObjectProperty.ind`, including a colimit presentation, rather than
replacing the definition by its augmentation criterion.
Source: ILO XVII 11.2.1(xi), 11.3.4
(blueprint: def-per-normal-subgroup-unipotence). -/
abbrev subgroupIndUnipotent (H : Subgroup G) :
    ObjectProperty (DiscreteContinuousRep.{u, v, w} R G) :=
  ObjectProperty.ind.{w} (IsSubgroupUnipotent (R := R) H)

end Rep
