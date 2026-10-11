/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Etale algebras over a filtered colimit descend to a finite stage

Source: Stacks Project, Algebra, Lemma Tag 00U2 (9), and more-algebra.tex,
proof of Lemma Tag 0A02 (blueprint: lem-weil-pbc-etale-algebra-filtered-colimit-descent).
-/

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Source: Stacks Project, Algebra, Lemma Tag 00U2 (9), and more-algebra.tex,
proof of Lemma Tag 0A02 (blueprint: lem-weil-pbc-etale-algebra-filtered-colimit-descent).

Proof, following the node:
1. By lem-weil-pbc-etale-algebra-finite-type-model choose a finitely generated
   subring A₀ of A and an etale A₀-algebra B₀ whose base change is B.
2. By lem-weil-pbc-finite-type-ring-map-factors-filtered-colimit, the inclusion
   A₀ → A factors through a stage Aᵢ: finitely many generators and relations
   lift to a common stage of the filtered category.
3. Set Bᵢ = Aᵢ ⊗[A₀] B₀. It is etale over Aᵢ by
   lem-weil-pbc-etale-ring-base-change.
4. By lem-weil-pbc-tensor-cancel-base-change, the further base change of Bᵢ
   to A is A ⊗[A₀] B₀. Compose the inverse of this cancellation isomorphism
   with the model isomorphism from step 1 to obtain the asserted A-algebra isomorphism.
-/
theorem exists_etale_algebra_of_filteredColimit
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (B : Type u) [CommRing B]
    (f : (colimit F : CommRingCat.{u}) ⟶ CommRingCat.of B)
    (hf : Etale (Spec.map f)) :
    ∃ (i : I) (Bi : Type u) (_ : CommRing Bi)
      (g : F.obj i ⟶ CommRingCat.of Bi),
      Etale (Spec.map g) ∧
      let A : Type u := (colimit F : CommRingCat.{u})
      letI : CommRing A := inferInstance
      letI : Algebra (F.obj i) A := (colimit.ι F i).hom.toAlgebra
      letI : Algebra (F.obj i) Bi := g.hom.toAlgebra
      letI : Algebra A B := f.hom.toAlgebra
      Nonempty (B ≃ₐ[A] (A ⊗[F.obj i] Bi)) := by
  sorry

end AlgebraicGeometry
