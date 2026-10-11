/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Torsion abelian sheaves on the small étale site

Source: the blueprint of the Weil conjectures, chapter `sec-proper-base-change`, unit
`sk-def-pbc` (blueprint: def-weil-pbc-torsion-etale-sheaf); Stacks Project, Etale cohomology,
Section 0DDB.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Positive integers indexing the torsion filtration. Source: blueprint
`sec-proper-base-change/sk-def-pbc`, statement (blueprint: def-weil-pbc-torsion-etale-sheaf). -/
structure PositiveNat where
  val : ℕ
  pos : 0 < val

/-- The divisibility order on positive integers. Source: blueprint
`sec-proper-base-change/sk-def-pbc`, statement (blueprint: def-weil-pbc-torsion-etale-sheaf). -/
instance : PartialOrder PositiveNat where
  le n m := n.val ∣ m.val
  lt n m := n.val ∣ m.val ∧ ¬m.val ∣ n.val
  le_refl n := dvd_refl n.val
  le_trans _ _ _ hnm hmk := dvd_trans hnm hmk
  le_antisymm n m hnm hmn := by
    cases n
    cases m
    congr
    exact Nat.dvd_antisymm hnm hmn
  lt_iff_le_not_ge := by intro a b; rfl

/-- The kernel inclusion for positive integers ordered by divisibility. Source: blueprint
`sec-proper-base-change/sk-def-pbc`, statement (blueprint: def-weil-pbc-torsion-etale-sheaf). -/
theorem torsionKernelTransition_condition {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n m : PositiveNat) (hnm : n.1 ∣ m.1) :
    kernel.ι (n.val • 𝟙 F) ≫ (m.val • 𝟙 F) = 0 := by
  sorry

/-- The canonical kernel inclusions satisfy the identity law. Source: blueprint
`sec-proper-base-change/sk-def-pbc`, statement (blueprint: def-weil-pbc-torsion-etale-sheaf). -/
theorem torsionKernelTransition_id {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : PositiveNat) :
    kernel.lift (n.val • 𝟙 F) (kernel.ι (n.val • 𝟙 F))
        (torsionKernelTransition_condition F n n (dvd_refl n.1)) = 𝟙 _ := by
  sorry

/-- The canonical kernel inclusions satisfy the composition law. Source: blueprint
`sec-proper-base-change/sk-def-pbc`, statement (blueprint: def-weil-pbc-torsion-etale-sheaf). -/
theorem torsionKernelTransition_comp {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n m k : PositiveNat) (hnm : n.1 ∣ m.1) (hmk : m.1 ∣ k.1) :
    kernel.lift (m.val • 𝟙 F) (kernel.ι (n.val • 𝟙 F))
        (torsionKernelTransition_condition F n m hnm) ≫
      kernel.lift (k.val • 𝟙 F) (kernel.ι (m.val • 𝟙 F))
        (torsionKernelTransition_condition F m k hmk) =
      kernel.lift (k.val • 𝟙 F) (kernel.ι (n.val • 𝟙 F))
        (torsionKernelTransition_condition F n k (dvd_trans hnm hmk)) := by
  sorry

/-- Source: blueprint `sec-proper-base-change/sk-def-pbc`, statement
(blueprint: def-weil-pbc-torsion-etale-sheaf). For a sheaf `F` of abelian groups on the
small étale site of `T`, form the filtered diagram indexed by positive natural numbers ordered
by divisibility, whose value at `n` is `ker (n : F ⟶ F)` and whose transition maps are the
canonical inclusions. The sheaf `F` is torsion when the canonical map from the colimit of this
diagram to `F`, induced by the kernel inclusions, is an isomorphism (Stacks Project, Section
0DDB). The construction follows the node proof step by step: divisibility gives the positive
integer index category; the kernel inclusion condition gives transition maps; the identity and
composition lemmas give a functor `D`; the kernel inclusions give a cocone `c`; and
`colimit.desc D c` is the canonical map whose `IsIso` property defines torsion. -/
noncomputable def IsTorsionAbelianSheaf {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  let D : PositiveNat ⥤ Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    { obj := fun n => kernel (n.val • 𝟙 F)
      map := fun {n m} hnm => kernel.lift (m.val • 𝟙 F) (kernel.ι (n.val • 𝟙 F))
        (torsionKernelTransition_condition F n m hnm.down.down)
      map_id := by
        intro n
        exact torsionKernelTransition_id F n
      map_comp := by
        intro n m k hnm hmk
        exact (torsionKernelTransition_comp F n m k hnm.down.down hmk.down.down).symm }
  let c : Cocone D :=
    { pt := F
      ι := { app := fun n => kernel.ι (n.val • 𝟙 F)
             naturality := by
               intro n m hnm
               simp [D] } }
  IsIso (colimit.desc D c)

end AlgebraicGeometry.Scheme
