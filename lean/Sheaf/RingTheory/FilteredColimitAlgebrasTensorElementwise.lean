/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Sheaf.RingTheory.FilteredColimitAlgebrasUnderlyingModule

/-!
# Base change of a filtered colimit of algebras, elementwise

Source: Stacks Project, Algebra, Tags 00DD, 00D6 and 00D7
(blueprint: lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise).
-/

@[expose] public section

universe uR uI vA uN uM

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace CommAlgCat

/--
Base change by tensor product preserves the elementwise description of a filtered
colimit of commutative algebras.

Source: Stacks Project, Algebra, Tags 00DD, 00D6 and 00D7
(blueprint: lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise).
Proof:
1. Apply `lem-weil-pbc-filtered-colimit-algebras-underlying-module` to the algebra
   diagram and its colimit: forgetting to modules gives a module colimit, in the
   sense of `def-weil-pbc-category-colimit`.
2. Apply `lem-weil-pbc-tensor-commutes-with-colimits` (Tag 00DD) to that module
   diagram and `N`. Its colimit is the tensor product with the stated coprojections.
3. Apply `lem-weil-pbc-filtered-colimit-modules-elementwise` (Tags 00D6 and 00D7)
   to this tensor diagram. Every element lifts to a stage, and an element whose
   image is zero becomes zero along a morphism to a later stage.
4. For the algebra clause, apply `lem-weil-pbc-algebra-tensor-map-ring-hom` to
   each coprojection and transition map; this is `Algebra.TensorProduct.rTensor`.
-/
theorem filteredColimit_tensorProduct_elementwise
    (R : Type uR) [CommRing R]
    {I : Type uI} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{vA, uR} R) [HasColimit F]
    (N : Type uN) [AddCommGroup N] [Module R N] :
    (∀ (x : (colimit F : CommAlgCat R) ⊗[R] N),
      ∃ (i : I) (t : (F.obj i : Type vA) ⊗[R] N),
        LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap t = x) ∧
    (∀ (i : I) (t : (F.obj i : Type vA) ⊗[R] N),
      LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap t = 0 →
        ∃ (j : I) (u : i ⟶ j),
          LinearMap.rTensor N (F.map u).hom.toLinearMap t = 0) := by
  sorry

/-- The parenthetical module-colimit clause, written as the universal property:
every compatible family of linear maps factors uniquely through the tensor colimit.

Source: Stacks Project, Algebra, Tag 00DD
(blueprint: lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise).
Proof: first forget the filtered algebra colimit to modules using
`lem-weil-pbc-filtered-colimit-algebras-underlying-module`, then apply
`lem-weil-pbc-tensor-commutes-with-colimits`. Unpack the resulting `IsColimit`
using `def-weil-pbc-category-colimit`: compatibility gives a unique factorization. -/
theorem filteredColimit_tensorProduct_universal
    (R : Type uR) [CommRing R]
    {I : Type uI} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{vA, uR} R) [HasColimit F]
    (N : Type uN) [AddCommGroup N] [Module R N]
    (M : Type uM) [AddCommGroup M] [Module R M]
    (μ : ∀ i : I, (F.obj i : Type vA) ⊗[R] N →ₗ[R] M)
    (hμ : ∀ (i j : I) (u : i ⟶ j),
      (μ j).comp (LinearMap.rTensor N (F.map u).hom.toLinearMap) = μ i) :
    ∃! l : (colimit F : CommAlgCat R) ⊗[R] N →ₗ[R] M,
      ∀ i : I, l.comp (LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap) = μ i := by
  sorry

/-- When the tensor factor is a commutative algebra, the tensor coprojections and
transition maps are underlying maps of ring homomorphisms.

Source: Stacks Project, Algebra, Sections Tags 00CV and 05G3
(blueprint: lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise).
Proof: apply `lem-weil-pbc-algebra-tensor-map-ring-hom` to every coprojection and
transition algebra homomorphism. `Algebra.TensorProduct.rTensor` supplies the algebra
homomorphism, whose underlying linear map is the displayed `LinearMap.rTensor`.
Taking `AlgHom.toRingHom` gives the required ring homomorphisms. -/
theorem filteredColimit_tensorProduct_ringHom
    (R : Type uR) [CommRing R]
    {I : Type uI} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{vA, uR} R) [HasColimit F]
    (N : Type uN) [CommRing N] [Algebra R N] :
    (∀ i : I, ∃ φ : (F.obj i : Type vA) ⊗[R] N →+*
        (colimit F : CommAlgCat R) ⊗[R] N,
      ∀ t, φ t = LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap t) ∧
    (∀ (i j : I) (u : i ⟶ j),
      ∃ φ : (F.obj i : Type vA) ⊗[R] N →+* (F.obj j : Type vA) ⊗[R] N,
        ∀ t, φ t = LinearMap.rTensor N (F.map u).hom.toLinearMap t) := by
  sorry

end CommAlgCat
