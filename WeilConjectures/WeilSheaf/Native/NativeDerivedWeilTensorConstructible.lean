/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
import WeilConjectures.WeilSheaf.Native.NativeGeometricTensorComparison
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleTensorPreservation
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Native derived-Weil tensor preserves bounded constructible complexes

The native derived tensor of bounded constructible Weil complexes is again bounded
constructible.

## Implementation details

The tensor is the recorded ambient native tensor, and the conclusion uses the existing
bounded-constructible object property. The proof transfers the question along
`nativeGeometricForget` to the geometric fiber, where the cohomological criterion
`weil_geometric_hom_constructibility` and `adicConstructibilityPredicateComparison` reduce it to
the ordinary tensor closure `boundedConstructible_tensor_closure`, through the comparison
`nativeGeometricForget_tensorComparison`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

/-- The native derived tensor of bounded constructible Weil complexes is bounded
with constructible cohomology after forgetting the Weil structure. -/
theorem nativeDerivedTensor_mem_weilComplex
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (A B : WeilComplex k₀ l X) :
    WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.nativeDerivedTensor k₀ l X).obj (B.obj, A.obj)) := by
  let Y := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let aY := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  let Λ := Profinite.padicAlgClRingObj.{u} l
  let U := ProEtaleWeilSheaf.nativeGeometricForget k₀ l X
  let : IsNoetherian Y :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian aY
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace aY }
  let : Fact (ringChar (AlgebraicClosure k₀) ≠ l) :=
    ⟨by rw [← Algebra.ringChar_eq k₀ (AlgebraicClosure k₀)]
        exact Fact.out⟩
  let Z : Over (Spec (CommRingCat.of (AlgebraicClosure k₀))) := Over.mk aY
  let : LocallyOfFiniteType Z.hom := inferInstanceAs (LocallyOfFiniteType aY)
  let : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact aY)
  let : IsSeparated Z.hom := inferInstanceAs (IsSeparated (Limits.pullback.snd _ _))
  have hCriterion := (ProEtaleWeilSheaf.weil_geometric_hom_constructibility k₀ l X).1
  have hPred := ProEtale.adicConstructibilityPredicateComparison l Y Λ (.algebraicClosure)
  have hA := (hCriterion A.obj).mp A.property
  have hB := (hCriterion B.obj).mp B.property
  rw [← hPred.2] at hA hB
  have hTensor := ProEtale.CondensedRing.boundedConstructible_tensor_closure (X := Z) l
    (U.obj B.obj) (U.obj A.obj) hB hA
  have hTensor' : ProEtale.constantModelBoundedConstructible Λ Y
      (((ProEtale.CondensedRing.derivedTensor Λ Y).obj (U.obj B.obj)).obj
        (U.obj A.obj)) := by
    rw [← hPred.2]
    exact hTensor
  obtain ⟨e⟩ := ProEtaleWeilSheaf.nativeGeometricForget_tensorComparison k₀ l X
  apply (hCriterion _).mpr
  rw [← hPred.2] at hTensor' ⊢
  let i := (e.app (B.obj, A.obj)).symm
  exact ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso i hTensor'.1,
    fun n ↦ _root_.constructible_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso i) (hTensor'.2 n)⟩

end AlgebraicGeometry.WeilComplex
