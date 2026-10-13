/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: SHEAF group N4
-/
module

public import Sheaf.CategoryTheory.Abelian.InjectiveResolutionDerivedComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# Boundary compatibility of the explicit resolution comparisons

Source: Stacks Project, Derived Categories, Tags 014Q, 05TE and 015B.
(blueprint: lem-sc-p1-horseshoe-comparison-boundary).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The explicit comparisons respect the connecting arrow of the derived
horseshoe triangle.

Source: Stacks Project, Derived Categories, Tags 014Q, 0159 and 015B;
fixed-horseshoe comparison, Steps 1-3.
(blueprint: lem-sc-p1-horseshoe-comparison-boundary).

Proof:
1. Extend the compatible horseshoe and its augmentations by zero. Each degree
row splits because its first term is injective. Use the split triangle with
connecting chain map section, differential, retraction; its cone comparison fixes
the sign. The augmentation maps are quasi-isomorphisms.
2. Transport this triangle to the single objects. Maps from X₁[0][1] to X₃[0]
vanish: compute into the bounded below injective resolution of X₃ in the homotopy
category, where the supports are disjoint. Third-map uniqueness identifies the
transported boundary with the canonical single-triangle boundary.
3. Apply the derived functor. The unit is invertible on the three bounded below
injective complexes. Its naturality supplies the first two squares; its shift
compatibility supplies the third square. Termwise additivity preserves the split
connecting map and the minus sign in the shifted differential. Commute the
termwise functor past extension by zero using mapExtendIso.
4. The comparisons in Steps 2-3 equal the explicit comparisons below: compose
with a lift of the identity from the chosen resolution. Any two such lifts are
homotopic, so their localized maps agree. Naturality of the derived unit applied
to this lift identifies the inverse-unit comparison for the fixed resolution
with the chosen-resolution comparison followed by the lift. The quotient
factorization and mapExtendIso identify its target with Q(EvI). Thus the first
and third components are exactly the displayed explicit comparisons, and the
third triangle square is the asserted equation.
-/
theorem horseshoe_comparison_boundary
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [EnoughInjectives A] [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v]
    (S : ShortComplex A) (hS : S.ShortExact)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (_hιA : IA.ι ≫ α = (CochainComplex.single₀ A).map S.f ≫ IB.ι)
    (_hιB : IB.ι ≫ β = (CochainComplex.single₀ A).map S.g ≫ IC.ι)
    (_hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval A (ComplexShape.up ℕ) k)).ShortExact)
    (hvH : ((ShortComplex.mk α β hαβ).map
      (v.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact)
    (hExt : (((ShortComplex.mk α β hαβ).map
      (v.mapHomologicalComplex (ComplexShape.up ℕ))).map
      (ComplexShape.embeddingUpNat.extendFunctor B)).ShortExact) :
    let T := (v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
      hS.singleTrianglePlus
    let U := DerivedCategory.triangleOfSES hExt
    (T.mor₃ ≫ (injectiveResolutionDerivedComparison v IA)⟦(1 : ℤ)⟧' =
      injectiveResolutionDerivedComparison v IC ≫ U.mor₃) := by sorry

end CategoryTheory
