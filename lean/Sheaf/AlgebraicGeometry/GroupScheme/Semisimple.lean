/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Semisimple group schemes and the algebraic derived subgroup

Source: Milne, Algebraic Groups (2017), Proposition 6.18, Proposition 6.30 and 6.44.
(blueprint: def-sfb-semisimple-group-scheme)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The commutator morphism, with value `xyx⁻¹y⁻¹` on points.
Source: Milne, Proposition 6.18. (blueprint: def-sfb-semisimple-group-scheme) -/
noncomputable def groupSchemeCommutator {F : Type u} [Field F]
    (G : Over (Spec (.of F))) [GrpObj G] : G ⊗ G ⟶ G :=
  fst G G * snd G G * (fst G G)⁻¹ * (snd G G)⁻¹

/-- The inclusion of the smallest closed subgroup through which the commutator factors.
Minimality is expressed by factorization of inclusions, so no representative is chosen.
Source: Milne, Proposition 6.18. (blueprint: def-sfb-semisimple-group-scheme) -/
def IsDerivedGroupScheme {F : Type u} [Field F]
    {G D : Over (Spec (.of F))} [GrpObj G] [GrpObj D] (i : D ⟶ G) : Prop :=
  IsClosedSubgroupScheme i ∧
    (∃ c : G ⊗ G ⟶ D, c ≫ i = groupSchemeCommutator G) ∧
    ∀ (K : Over (Spec (.of F))) [GrpObj K] (j : K ⟶ G),
      IsClosedSubgroupScheme j →
      (∃ c : G ⊗ G ⟶ K, c ≫ j = groupSchemeCommutator G) →
      ∃ f : D ⟶ K, f ≫ j = i

/-- The derived series reaches the trivial group after the specified number of steps.
A trivial group is terminal among schemes over the field; each successor takes the
smallest closed subgroup containing the commutator morphism. This predicate retains
all scheme structure, including nonreduced subgroup schemes.
Source: Milne, Proposition 6.30. (blueprint: def-sfb-semisimple-group-scheme) -/
def GroupSchemeDerivedLength {F : Type u} [Field F]
    (G : Over (Spec (.of F))) [GrpObj G] : ℕ → Prop
  | 0 => Nonempty (IsTerminal G)
  | n + 1 => ∃ (D : Over (Spec (.of F))) (_ : GrpObj D) (i : D ⟶ G),
      IsDerivedGroupScheme i ∧ GroupSchemeDerivedLength D n

/-- Solvability means termination of the scheme-theoretic derived series.
Source: Milne, Proposition 6.30. (blueprint: def-sfb-semisimple-group-scheme) -/
def IsSolvableGroupScheme {F : Type u} [Field F]
    (G : Over (Spec (.of F))) [GrpObj G] : Prop :=
  ∃ n : ℕ, GroupSchemeDerivedLength G n

/-- A semisimple group scheme over an algebraically closed field is smooth, connected,
affine and of finite type, with no nontrivial smooth connected solvable normal closed
subgroup scheme. Triviality is terminality over the base, rather than a statement only
about rational points. Source: Milne, 6.44.
(blueprint: def-sfb-semisimple-group-scheme) -/
def IsSemisimpleGroupScheme {F : Type u} [Field F] [IsAlgClosed F]
    (G : Over (Spec (.of F))) [GrpObj G] : Prop :=
  Smooth G.hom ∧ ConnectedSpace G.left ∧ IsAffine G.left ∧
    LocallyOfFiniteType G.hom ∧ QuasiCompact G.hom ∧
    ∀ (N : Over (Spec (.of F))) [GrpObj N] (i : N ⟶ G),
      IsClosedSubgroupScheme i → IsNormalSubgroupScheme i →
      Smooth N.hom → ConnectedSpace N.left → IsSolvableGroupScheme N →
      Nonempty (IsTerminal N)

end AlgebraicGeometry
