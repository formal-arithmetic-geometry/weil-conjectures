/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-! # The diagonalizable group of an abelian group

Source: Milne, Algebraic Groups (2017), Proposition 12.3 and Theorem 12.9(a), pp.231--233
(blueprint: def-sfb-diagonalizable-group).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- The spectrum of the additive group algebra, with its canonical Hopf group structure.
The basis element e_m has coproduct e_m ⊗ e_m, counit 1 and antipode e_(-m).
Source: Milne, Algebraic Groups (2017), Proposition 12.3, p.231
(blueprint: def-sfb-diagonalizable-group). -/
noncomputable abbrev diagonalizableGroup (F : Type u) [Field F]
    (M : Type u) [AddCommGroup M] : Grp (Over (Spec (.of F))) :=
  (hopfSpec (.of F)).obj (op (CommHopfAlgCat.of F (AddMonoidAlgebra F M)))

/-- Contravariance of the group-algebra spectrum: α induces e_m ↦ e_(α m).
This is the actual Hopf-spectrum map, not an unspecified homomorphism.
Source: Milne, Algebraic Groups (2017), Theorem 12.9(a), p.233
(blueprint: def-sfb-diagonalizable-group). -/
noncomputable abbrev diagonalizableGroupMap (F : Type u) [Field F]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] (α : M →+ N) :
    diagonalizableGroup F N ⟶ diagonalizableGroup F M :=
  (hopfSpec (.of F)).map (CommHopfAlgCat.ofHom
    (AddMonoidAlgebra.mapDomainBialgHom F α)).op

/-- Multiplication on D(M) by the image of D(N), for the map induced by α : M → N.
Source: Milne, Algebraic Groups (2017), Theorem 12.9(b),(c), pp.233--234,
and Section 5(j), pp.116--118 (blueprint: def-sfb-diagonalizable-group). -/
noncomputable abbrev diagonalizableGroupAction (F : Type u) [Field F]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] (α : M →+ N) :
    (diagonalizableGroup F M).X ⊗ (diagonalizableGroup F N).X ⟶
      (diagonalizableGroup F M).X :=
  lift (fst _ _) (snd _ _ ≫ (diagonalizableGroupMap F α).hom.hom) ≫
    μ[(diagonalizableGroup F M).X]

end AlgebraicGeometry
