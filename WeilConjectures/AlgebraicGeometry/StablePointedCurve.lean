/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleMorphism
public import WeilConjectures.AlgebraicGeometry.NodalGeometricFibres
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.ReducedNormalization
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Data.Set.Card

/-! # Stable pointed curves

Source: de Jong, Families of curves and alterations (1997), §3.6 and Lemma 3.7,
with the stable pointed convention in the DAG
(blueprint: def-sfb-stable-pointed-curve).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The canonical map from the normalization of a reduced irreducible component.
Source: de Jong (1997), §3.6, component normalization convention
(blueprint: def-sfb-stable-pointed-curve). -/
def Scheme.normalizedComponentMap (C : Scheme.{u}) (Z : irreducibleComponents C) :
    (C.reducedNormalizationComponent Z).normalization ⟶ C :=
  (C.reducedNormalizationComponent Z).fromNormalization ≫
    (Scheme.IdealSheafData.vanishingIdeal
      ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι

/-- Genus of the canonical normalization of a geometric component, using its structural map.
Source: de Jong (1997), §3.6 (blueprint: def-sfb-stable-pointed-curve). -/
def Scheme.normalizedComponentGenus {Ω : Type u} [Field Ω] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of Ω)) (Z : irreducibleComponents C) : ℕ :=
  @Scheme.arithmeticGenus Ω _ (C.reducedNormalizationComponent Z).normalization
    ⟨C.normalizedComponentMap Z ≫ p⟩

/-- A stable labelled pointed family, allowing no markings. Special points are counted on
normalizations: the two branches of a self-node are distinct points. Projectivity uses
finite-type quasi-coherent projective bundles. ConnectedSpace includes nonemptiness.
Source: de Jong (1997), §3.6 and Lemma 3.7, stable pointed convention
(blueprint: def-sfb-stable-pointed-curve). -/
def IsStablePointedCurve {W T : Scheme.{u}} (f : W ⟶ T) {n : ℕ}
    (s : Fin n → (T ⟶ W)) (hs : ∀ i, s i ≫ f = 𝟙 T) : Prop :=
  IsProjectiveBundle f ∧ Flat f ∧
    ∃ hfp : LocallyOfFinitePresentation f,
      @HasNodalGeometricFibres W T f hfp ∧
      Pairwise (fun i j : Fin n ↦ Disjoint (Set.range (s i)) (Set.range (s j))) ∧
      (∀ i : Fin n, Set.range (s i) ⊆ (f.smoothLocus : Set W)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ T),
        IsReduced (pullback f a) ∧ (pullback f a).IsPureDimension 1 ∧
        ∀ Z : irreducibleComponents (pullback (C := Scheme.{u}) f a),
          ((pullback f a).normalizedComponentGenus (pullback.snd f a) Z = 0 →
            3 ≤ ((pullback f a).normalizedComponentMap Z ⁻¹'
              ({x | x ∉ (pullback.snd f a).smoothLocus} ∪
                ⋃ i : Fin n, Set.range (f.baseChangeSection (s i) (hs i) a))).encard) ∧
          ((pullback f a).normalizedComponentGenus (pullback.snd f a) Z = 1 →
            1 ≤ ((pullback f a).normalizedComponentMap Z ⁻¹'
              ({x | x ∉ (pullback.snd f a).smoothLocus} ∪
                ⋃ i : Fin n, Set.range (f.baseChangeSection (s i) (hs i) a))).encard)

end AlgebraicGeometry
