/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Smooth algebras over a filtered colimit descend to a finite stage

Source: Stacks Project, Algebra, Lemma Tag 0CAQ
(blueprint: lem-weil-pbc-smooth-algebra-filtered-colimit-descent).
-/

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

/-- Source: Stacks Project, Algebra, Lemma Tag 0CAQ
(blueprint: lem-weil-pbc-smooth-algebra-filtered-colimit-descent).

Proof, following the node:
1. By lem-weil-pbc-smooth-algebra-finite-type-model choose a finitely generated
   subring A₀ of A and a smooth A₀-algebra B₀ whose base change is B.
2. By lem-weil-pbc-finite-type-ring-map-factors-filtered-colimit, the inclusion
   A₀ → A factors through a stage Aᵢ: finitely many generators and relations
   lift to a common stage of the filtered category.
3. Set Bᵢ = Aᵢ ⊗[A₀] B₀. It is smooth over Aᵢ by
   lem-weil-pbc-smooth-ring-map-base-change-composition.
4. By lem-weil-pbc-tensor-cancel-base-change, the further base change of Bᵢ
   to A is A ⊗[A₀] B₀. Compose the inverse of this cancellation isomorphism
   with the model isomorphism from step 1 to obtain the asserted A-algebra isomorphism.
-/
theorem exists_smooth_algebra_of_filteredColimit
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (B : Type u) [CommRing B]
    (f : (colimit F : CommRingCat.{u}) ⟶ CommRingCat.of B)
    (hf : letI := f.hom.toAlgebra; Smooth (colimit F : CommRingCat.{u}) B) :
    ∃ (i : I) (Bi : Type u) (_ : CommRing Bi)
      (g : F.obj i ⟶ CommRingCat.of Bi),
      letI := g.hom.toAlgebra
      letI := (colimit.ι F i).hom.toAlgebra
      letI := f.hom.toAlgebra
      Smooth (F.obj i) Bi ∧
        Nonempty (B ≃ₐ[(colimit F : CommRingCat.{u})]
          ((colimit F : CommRingCat.{u}) ⊗[F.obj i] Bi)) := by
  sorry

end Algebra
