/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageComparisonMap
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
public import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageBoundedBelow
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarCoproducts

/-!
# Unbounded comparison of direct images for finite coefficients

For schemes of finite type over a finite or algebraically closed field `k` and a finite
`ℓ`-primary coefficient ring `A`, the comparison map `ν_Y^* Rg_* K ⟶ Rg_* ν_X^* K` is an
isomorphism for every unbounded complex `K` of étale sheaves. The bounded below case is
`AlgebraicGeometry.ProEtale.unboundedDirectImageComparison_boundedBelow`.

## Implementation details

Only the finiteness of `A` and the finite type hypotheses are used. In a fixed degree `m`, both
sides only depend on a truncation `τ_{≥ N} K` for `N ≪ m`: the étale direct image has finite
cohomological dimension, and the pro-étale direct image has finite amplitude on complexes with
cohomology sheaves of étale origin. For the bounded below complex `τ_{≥ N} K` the map is an
isomorphism by `AlgebraicGeometry.ProEtale.unboundedDirectImageComparison_boundedBelow`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

/-- **Unbounded comparison of direct images for finite coefficients**: let `k` be a finite or
algebraically closed field, `ℓ` a prime invertible in `k`, `A` a finite `ℓ`-primary ring and
`g : X ⟶ Y` a morphism of schemes of finite type over `k`. For every
`K ∈ D(X_ét, A)`, the comparison map `ν_Y^* Rg_* K ⟶ Rg_* ν_X^* K`
(`AlgebraicGeometry.ProEtale.unboundedDirectImageComparisonMap`) is an isomorphism. The proof only
uses that `A` is finite and the finite type hypotheses. -/
theorem isIso_unboundedDirectImageComparisonMap
    (k : Type u) [Field k] (_hbase : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A] (_hA : ∃ r : ℕ, (ℓ : A) ^ r = 0)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of k))]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso (unboundedDirectImageComparisonMap A g K) := by
  have : LocallyOfFiniteType g := by
    have : LocallyOfFiniteType (g ≫ Y ↘ Spec (.of k)) := by
      rw [CategoryTheory.comp_over g (Spec (.of k))]; infer_instance
    exact locallyOfFiniteType_of_comp g (Y ↘ Spec (.of k))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : QuasiCompact g := by
    have : QuasiCompact (g ≫ Y ↘ Spec (.of k)) := by
      rw [CategoryTheory.comp_over g (Spec (.of k))]; infer_instance
    exact QuasiCompact.of_comp g (Y ↘ Spec (.of k))
  let aY := Y ↘ Spec (.of k)
  have hAt : IsAddTorsion A := isAddTorsion_of_finite
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (g ≫ aY)
  have : QuasiSeparated g := inferInstance
  let C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let D := Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)
  let FY := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
  let FX := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let R := (Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor
  let S := (ProEtale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor
  obtain ⟨d, hd⟩ := Etale.hasFiniteCohomologicalDimensionMorphism A hAt (g ≫ aY) aY g rfl
  have hcd : ∀ (F : C) (q : ℕ), d.toNat < q →
      IsZero (((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerived q).obj F) :=
    fun F q hq ↦ Functor.isZero_rightDerived_of_isZero_homology _ F q (hd F q (by lia))
  obtain ⟨e, he⟩ :=
    exists_isLE_rightDerivedLowerStar_of_etaleOriginHomology A g (g ≫ aY) aY rfl
  rw [DerivedCategory.isIso_iff]
  intro m
  let N : ℤ := m - d.toNat - e.toNat - 2
  let t := DerivedCategory.TStructure.t (C := C)
  let J := (t.truncLT N).obj K
  let T := (t.truncGE N).obj K
  let f : K ⟶ T := (t.truncGEπ N).app K
  have : J.IsLE (N - 1) := t.isLE_truncLT_obj K N (N - 1) (by omega)
  have : T.IsGE N := inferInstanceAs (t.IsGE ((t.truncGE N).obj K) N)
  have hRJ : (FY.obj (R.obj J)).IsLE (N - 1 + d.toNat) := by
    have := Functor.isLE_rightDerivedFunctor_obj _ d.toNat hcd J (N - 1)
    exact (comparisonUpperStar (ModuleCat.{u + 1} A) Y).isLE_mapDerivedCategory_obj _ _
  have hSJ : (S.obj (FX.obj J)).IsLE (N - 1 + e) :=
    he _ (N - 1) (DerivedCategory.etaleOriginHomology_mapDerivedCategory_obj J)
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).isLE_mapDerivedCategory_obj J (N - 1))
  have hleft : IsIso ((DerivedCategory.homologyFunctor D m).map (FY.map (R.map f))) := by
    have htri := FY.map_distinguished _ (R.map_distinguished _ (t.triangleLTGE_distinguished N K))
    exact DerivedCategory.isIso_homologyMap_mor₂ _ htri m (m + 1) rfl
      (DerivedCategory.isZero_of_isLE _ (N - 1 + d.toNat) m (by omega) (hX := hRJ))
      (DerivedCategory.isZero_of_isLE _ (N - 1 + d.toNat) (m + 1) (by omega) (hX := hRJ))
  have hright : IsIso ((DerivedCategory.homologyFunctor D m).map (S.map (FX.map f))) := by
    have htri := S.map_distinguished _ (FX.map_distinguished _ (t.triangleLTGE_distinguished N K))
    exact DerivedCategory.isIso_homologyMap_mor₂ _ htri m (m + 1) rfl
      (DerivedCategory.isZero_of_isLE _ (N - 1 + e) m (by omega) (hX := hSJ))
      (DerivedCategory.isZero_of_isLE _ (N - 1 + e) (m + 1) (by omega) (hX := hSJ))
  have hT : IsIso (unboundedDirectImageComparisonMap A g T) :=
    unboundedDirectImageComparison_boundedBelow A g T N
  have hw := congrArg (DerivedCategory.homologyFunctor D m).map
    (unboundedDirectImageComparisonMap_naturality A g f)
  simp only [Functor.map_comp] at hw
  have hh : IsIso ((DerivedCategory.homologyFunctor D m).map
      (unboundedDirectImageComparisonMap A g K) ≫
        (DerivedCategory.homologyFunctor D m).map (S.map (FX.map f))) := by
    rw [← hw]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor D m).map (S.map (FX.map f)))
end AlgebraicGeometry.ProEtale
