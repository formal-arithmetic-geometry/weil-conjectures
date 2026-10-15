/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Whiskering

/-!
# Total right derived functors from enough K-injective complexes

Source: Stacks Project, Derived Categories, Tag 070K, lemma-enough-K-injectives-implies,
and Tag 070Y, lemma-K-injective-defined (blueprint: lem-weil-pbc-kinjective-total-derived).
-/

@[expose] public section

universe w v u vT uT

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Enough K-injective complexes give a total right derived functor, computed on every
K-injective complex. Source: Stacks Project, Derived Categories, Tag 070K,
lemma-enough-K-injectives-implies; Tag 070Y, lemma-K-injective-defined
(blueprint: lem-weil-pbc-kinjective-total-derived).

Proof plan:
1. For each complex K choose a quasi-isomorphism u_K : K → I_K to a K-injective complex.
   Its image q_K under the localization Q is invertible. Set RF(QK) = F(I_K), using
   def-weil-abstract-derived-category.
2. Lift q_K⁻¹ ≫ a ≫ q_L uniquely to a homotopy-category morphism I_K → I_L using
   lem-weil-pbc-kinjective-hom-derived. Apply F to define RF(a). Uniqueness gives preservation
   of identities and composition.
3. Put η_K = F(u_K). Injectivity of the same Hom bijection gives naturality of η.
4. Given α : F → Q ⋙ G, define β_QK = α_I_K ≫ G(q_K⁻¹). Naturality of α at the lifted
   maps gives naturality of β; naturality at u_K gives η ≫ whiskerLeft Q β = α.
5. The lift computing RF(q_K) is u_I_K, so RF(q_K) = η_I_K. Naturality of any other
   factorization at q_K forces its component to equal α_I_K ≫ G(q_K⁻¹). Thus the map on
   natural transformations is bijective.
6. If J is K-injective, u_J is a quasi-isomorphism between K-injectives, hence a homotopy
   equivalence by lem-weil-pbc-kinjective-hom-derived. Its homotopy class is invertible,
   so η_J = F(u_J) is invertible. -/
theorem exists_rightDerived_of_enough_isKInjective
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (h : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (f : K ⟶ J), J.IsKInjective ∧ QuasiIso f)
    {T : Type uT} [Category.{vT} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ T)
    [F.CommShift ℤ] [F.IsTriangulated] :
    ∃ (RF : DerivedCategory A ⥤ T) (η : F ⟶ DerivedCategory.Qh ⋙ RF),
      (∀ G : DerivedCategory A ⥤ T,
        Function.Bijective
          (fun β : RF ⟶ G ↦ η ≫ Functor.whiskerLeft DerivedCategory.Qh β)) ∧
      (∀ (J : CochainComplex A ℤ), J.IsKInjective →
        IsIso (η.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J))) := by
  sorry

end CategoryTheory
