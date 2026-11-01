/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# Associated graded of the tensor filtration

Source: Stacks Project, More on Algebra, Section `section-kunneth-spectral-sequence`,
the paragraph preceding Tag 0H7W (blueprint: lem-pur-kunneth-tensor-associated-graded).

The image filtration is characterized by its steps. The quotient maps and graded
isomorphisms are characterized by the tensor quotient maps on the coproduct of
filtered tensor summands.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex.KunnethTensorAssociatedGraded

variable (R : Type u) [CommRing R]

/-- Module-valued cochain complexes. Source: Stacks, More on Algebra,
`section-kunneth-spectral-sequence` (blueprint: lem-pur-kunneth-tensor-associated-graded). -/
abbrev ModuleComplex := CochainComplex (ModuleCat.{u} R) ℤ

/-- The total direct sum of the graded tensor pieces with total filtration index `n`.
Source: Stacks, text before Tag 0H7W (blueprint: lem-pur-kunneth-tensor-associated-graded). -/
noncomputable abbrev gradedTensor (K L : ModuleComplex R)
    (FK : DecreasingFiltration K) (FL : DecreasingFiltration L) (n : ℤ) :
    ModuleComplex R :=
  ∐ fun q : {q : ℤ × ℤ // q.1 + q.2 = n} ↦
    CochainComplex.mapBifunctor (FK.gradedPiece q.1.1) (FL.gradedPiece q.1.2)
      (curriedTensor (ModuleCat.{u} R))

/-- The canonical map from a filtered tensor summand to the total tensor complex.
Source: Stacks, text before Tag 0H7W (blueprint: lem-pur-kunneth-tensor-associated-graded). -/
noncomputable abbrev tensorSummandMap (K L : ModuleComplex R)
    (FK : DecreasingFiltration K) (FL : DecreasingFiltration L) (i j : ℤ) :
    CochainComplex.mapBifunctor (FK.step i) (FL.step j)
        (curriedTensor (ModuleCat.{u} R)) ⟶
      CochainComplex.mapBifunctor K L (curriedTensor (ModuleCat.{u} R)) :=
  HomologicalComplex.mapBifunctorMap (FK.step i).arrow (FL.step j).arrow
    (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)

/-- The coproduct of all filtered tensor summands of total index `n`.
Source: Stacks, text before Tag 0H7W (blueprint: lem-pur-kunneth-tensor-associated-graded). -/
noncomputable abbrev tensorFilteredSource (K L : ModuleComplex R)
    (FK : DecreasingFiltration K) (FL : DecreasingFiltration L) (n : ℤ) :
    ModuleComplex R :=
  ∐ fun q : {q : ℤ × ℤ // q.1 + q.2 = n} ↦
    CochainComplex.mapBifunctor (FK.step q.1.1) (FL.step q.1.2)
      (curriedTensor (ModuleCat.{u} R))

/-- The map from the filtered tensor coproduct to the total tensor complex.
Source: Stacks, text before Tag 0H7W (blueprint: lem-pur-kunneth-tensor-associated-graded). -/
noncomputable abbrev tensorFilteredDesc (K L : ModuleComplex R)
    (FK : DecreasingFiltration K) (FL : DecreasingFiltration L) (n : ℤ) :
    tensorFilteredSource R K L FK FL n ⟶
      CochainComplex.mapBifunctor K L (curriedTensor (ModuleCat.{u} R)) :=
  Limits.Sigma.desc (fun q ↦ tensorSummandMap R K L FK FL q.1.1 q.1.2)

/-- The quotient map from a filtered tensor summand to its graded tensor summand.
Source: Stacks, text before Tag 0H7W (blueprint: lem-pur-kunneth-tensor-associated-graded). -/
noncomputable abbrev gradedSummandProjection (K L : ModuleComplex R)
    (FK : DecreasingFiltration K) (FL : DecreasingFiltration L)
    (i j n : ℤ) (h : i + j = n) :
    CochainComplex.mapBifunctor (FK.step i) (FL.step j)
        (curriedTensor (ModuleCat.{u} R)) ⟶ gradedTensor R K L FK FL n :=
  HomologicalComplex.mapBifunctorMap
      (FK.complexQuotientπ i (i + 1) (Int.le_add_one (show i ≤ i from le_rfl)))
      (FL.complexQuotientπ j (j + 1) (Int.le_add_one (show j ≤ j from le_rfl)))
      (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) ≫
    Limits.Sigma.ι (fun q : {q : ℤ × ℤ // q.1 + q.2 = n} ↦
      CochainComplex.mapBifunctor (FK.gradedPiece q.1.1) (FL.gradedPiece q.1.2)
        (curriedTensor (ModuleCat.{u} R))) ⟨(i, j), h⟩

/-- The coproduct of the canonical graded tensor quotient maps.
Source: Stacks, text before Tag 0H7W (blueprint: lem-pur-kunneth-tensor-associated-graded). -/
noncomputable abbrev gradedTensorDesc (K L : ModuleComplex R)
    (FK : DecreasingFiltration K) (FL : DecreasingFiltration L) (n : ℤ) :
    tensorFilteredSource R K L FK FL n ⟶ gradedTensor R K L FK FL n :=
  Limits.Sigma.desc (fun q ↦ gradedSummandProjection R K L FK FL q.1.1 q.1.2 n q.2)

/-- The subobject generated by all filtered tensor summands of total index `n`.
Source: Stacks, text before Tag 0H7W (blueprint: lem-pur-kunneth-tensor-associated-graded). -/
noncomputable def tensorFilteredImage (K L : ModuleComplex R)
    (FK : DecreasingFiltration K) (FL : DecreasingFiltration L) (n : ℤ) :
    Subobject (CochainComplex.mapBifunctor K L (curriedTensor (ModuleCat.{u} R))) :=
  imageSubobject (tensorFilteredDesc R K L FK FL n)

end CochainComplex.KunnethTensorAssociatedGraded

namespace CochainComplex.KunnethTensorAssociatedGraded

private noncomputable def tensorFilteredStepMap (K L : ModuleComplex R)
    (FK : DecreasingFiltration K) (FL : DecreasingFiltration L) (n : ℤ) :
    tensorFilteredSource R K L FK FL (n + 1) ⟶
      tensorFilteredSource R K L FK FL n := by
  let f (q : {q : ℤ × ℤ // q.1 + q.2 = n + 1}) :
      CochainComplex.mapBifunctor (FK.step q.1.1) (FL.step q.1.2)
          (curriedTensor (ModuleCat.{u} R)) ⟶
        CochainComplex.mapBifunctor (FK.step q.1.1) (FL.step (q.1.2 - 1))
          (curriedTensor (ModuleCat.{u} R)) :=
    HomologicalComplex.mapBifunctorMap
      (𝟙 (FK.step q.1.1 : ModuleComplex R))
      (Subobject.ofLE (FL.step q.1.2) (FL.step (q.1.2 - 1))
        (FL.antitone_step (by omega)))
      (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)
  exact Limits.Sigma.desc (fun q ↦
    f q ≫ Limits.Sigma.ι (fun q : {q : ℤ × ℤ // q.1 + q.2 = n} ↦
      CochainComplex.mapBifunctor (FK.step q.1.1) (FL.step q.1.2)
        (curriedTensor (ModuleCat.{u} R)))
      ⟨(q.1.1, q.1.2 - 1), by omega⟩)

private theorem tensorFilteredStepMap_desc (K L : ModuleComplex R)
    (FK : DecreasingFiltration K) (FL : DecreasingFiltration L) (n : ℤ) :
    tensorFilteredStepMap R K L FK FL n ≫ tensorFilteredDesc R K L FK FL n =
      tensorFilteredDesc R K L FK FL (n + 1) := by
  apply Limits.Sigma.hom_ext
  intro q
  simp [tensorFilteredStepMap, tensorFilteredDesc, tensorSummandMap,
    HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp,
    ← Functor.map_comp, Subobject.ofLE_arrow]

end CochainComplex.KunnethTensorAssociatedGraded
