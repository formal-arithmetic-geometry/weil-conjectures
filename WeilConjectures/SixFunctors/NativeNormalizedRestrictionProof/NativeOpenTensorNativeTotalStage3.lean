/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorDescentData

/-! Native total restriction data for open tensor descent.
(blueprint: new-sf-native-open-tensor-total-stage3) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits Opposite
universe u a b
namespace NativeNormalizedRestrictionProof

/-- A total restriction comparison together with its summand equation. -/
structure TotalDataCore
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    [c.R.PreservesZeroMorphisms]
    (sr : c.SB ⋙ c.R ≅ c.R.prod c.R ⋙ c.SA) where
  total : Functor.uncurry.obj c.TB ⋙ c.R.mapHomologicalComplex (.up ℤ) ≅
    (c.R.mapHomologicalComplex (.up ℤ)).prod (c.R.mapHomologicalComplex (.up ℤ)) ⋙
      Functor.uncurry.obj c.TA
  summands : ∀ P T (p q n : ℤ) (h : p + q = n),
    c.R.map (m.iB P T p q n h) ≫ (total.hom.app (P, T)).f n =
      sr.hom.app (P.X p, T.X q) ≫
        m.iA ((c.R.mapHomologicalComplex (.up ℤ)).obj P)
          ((c.R.mapHomologicalComplex (.up ℤ)).obj T) p q n h

@[irreducible] def TotalData
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    [c.R.PreservesZeroMorphisms]
    (sr : c.SB ⋙ c.R ≅ c.R.prod c.R ⋙ c.SA) : Type _ :=
  TotalDataCore c m sr

def totalDataMk
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    [c.R.PreservesZeroMorphisms]
    (sr : c.SB ⋙ c.R ≅ c.R.prod c.R ⋙ c.SA)
    (total : Functor.uncurry.obj c.TB ⋙ c.R.mapHomologicalComplex (.up ℤ) ≅
      (c.R.mapHomologicalComplex (.up ℤ)).prod (c.R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj c.TA)
    (summands : ∀ P T (p q n : ℤ) (h : p + q = n),
      c.R.map (m.iB P T p q n h) ≫ (total.hom.app (P, T)).f n =
        sr.hom.app (P.X p, T.X q) ≫
          m.iA ((c.R.mapHomologicalComplex (.up ℤ)).obj P)
            ((c.R.mapHomologicalComplex (.up ℤ)).obj T) p q n h) :
    TotalData c m sr := by
  unfold TotalData
  exact ⟨total, summands⟩

def totalData_total
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    [c.R.PreservesZeroMorphisms]
    (sr : c.SB ⋙ c.R ≅ c.R.prod c.R ⋙ c.SA)
    (d : TotalData c m sr) :
    Functor.uncurry.obj c.TB ⋙ c.R.mapHomologicalComplex (.up ℤ) ≅
      (c.R.mapHomologicalComplex (.up ℤ)).prod (c.R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj c.TA := by
  unfold TotalData at d
  exact d.total

theorem totalData_summands
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    [c.R.PreservesZeroMorphisms]
    (sr : c.SB ⋙ c.R ≅ c.R.prod c.R ⋙ c.SA)
    (d : TotalData c m sr) : ∀ P T (p q n : ℤ) (h : p + q = n),
      c.R.map (m.iB P T p q n h) ≫
          ((totalData_total c m sr d).hom.app (P, T)).f n =
        sr.hom.app (P.X p, T.X q) ≫
          m.iA ((c.R.mapHomologicalComplex (.up ℤ)).obj P)
            ((c.R.mapHomologicalComplex (.up ℤ)).obj T) p q n h := by
  unfold TotalData at d
  exact d.summands

end NativeNormalizedRestrictionProof

namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local instance] OpenTensorDescentInput.r_add OpenTensorDescentInput.r_lim
  OpenTensorDescentInput.r_colim OpenTensorDescentInput.r_zero

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- The native total restriction comparison exists under the native model links.

Source: Stacks 012Z (totalization) and 07A4.
(blueprint: new-sf-native-open-tensor-total-stage3)

Proof: the native totals are `(nativeTensorBifunctor _ _ X).flip.map₂CochainComplex` and the
sheaf tensors are the uncurried same bifunctors. Restriction is a left adjoint, so it
preserves the coproducts over p+q=n; the total-bifunctor comparison applied to the
natural isomorphism sr gives a natural chain isomorphism, compatible with the signed
total differentials by naturality of sr in both variables. By hm the insertions of m are
the native ιMapBifunctor, so on the (p,q)-summand the comparison is sr followed by the
open insertion, which is the summand equation. -/
theorem totalComparisonStage3
    (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j))
    (hm : NativeOpenTensorModelsCompatibility k₀ l j s m)
    (sr : (nativeOpenTensorDescentInput k₀ l j).SB ⋙
      (nativeOpenTensorDescentInput k₀ l j).R ≅
      (nativeOpenTensorDescentInput k₀ l j).R.prod
        (nativeOpenTensorDescentInput k₀ l j).R ⋙
      (nativeOpenTensorDescentInput k₀ l j).SA) :
    Nonempty (NativeNormalizedRestrictionProof.TotalData
      (nativeOpenTensorDescentInput k₀ l j) m sr) := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
