/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.StrictRoosModel
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-! # Roos augmentations of extensions of a constant tower
Source: Stacks Project, Tag 0941, proof of lemma-derived-limit-is-ok; the finite-sum
calculation in Bhatt--Scholze Lemma 3.4.12
(blueprint: lem-sp-roos-nilpotent-exact-augmentation). -/

@[expose] public section
set_option autoImplicit false
universe u v w g
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

section Construction
variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
variable {P : CochainComplex A ℤ} {V : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}

/-- Evaluate a strict map from a constant tower at a level.
Source: Stacks Tag 0941 (blueprint: lem-sp-roos-nilpotent-exact-augmentation). -/
def constantTowerComponents
    (i : ((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ⟶ V) (n : ℕ) : P ⟶ V.asFunctor.obj (op n) where
  f k := (i.f k).app (op n)
  comm' k l h := by
    exact congrArg (fun f ↦ f.app (op n)) (i.comm k l)

omit [HasCountableProducts A] in
/-- Strict compatibility of the evaluated constant-tower map.
Source: Stacks Tag 0941 (blueprint: lem-sp-roos-nilpotent-exact-augmentation). -/
lemma constantTowerCompatible
    (i : ((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ⟶ V) (n : ℕ) :
    constantTowerComponents i (n + 1) ≫ V.asFunctor.map (homOfLE n.le_succ).op =
      constantTowerComponents i n := by
  ext k
  change (i.f k).app (op (n + 1)) ≫ (V.X k).map (homOfLE n.le_succ).op =
    (i.f k).app (op n)
  have h := (i.f k).naturality (homOfLE n.le_succ).op
  change 𝟙 (P.X k) ≫ (i.f k).app (op n) = _ at h
  simpa only [Category.id_comp] using h.symm

/-- The zero-homotopy Roos augmentation of a strict constant-tower map.
Source: Stacks Tag 0941 (blueprint: lem-sp-roos-nilpotent-exact-augmentation). -/
noncomputable def constantTowerRoosAugmentation
    (i : ((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ⟶ V) : P ⟶ roosF.obj V :=
  roosAugment (constantTowerComponents i) (constantTowerCompatible i)
end Construction

/-- An extension of a constant tower by a uniformly nilpotent tower has its specified
Roos augmentation a quasi-isomorphism, and every total derived limit of the quotient
is zero. The nilpotence is imposed on the product shift in each degree, with one exponent.
Source: Stacks Project, Tag 0941, proof of lemma-derived-limit-is-ok, and
Bhatt--Scholze, Lemma 3.4.12, finite geometric-sum calculation
(blueprint: lem-sp-roos-nilpotent-exact-augmentation).

Proof: Write s for the product shift of Z. The finite sum 1+s+...+s^(a-1)
inverts 1-s in every degree, by the two geometric-sum identities. The inverses
commute with the differential, so the shifted cone Roos(Z) is contractible.
Products are exact, hence applying the product functor and the two cone coordinates
to the given short exact sequence gives a short exact sequence of Roos complexes.
The constant-tower diagonal P -> Roos(const P) is a homotopy equivalence: the
finite partial sums B(z)_0=0, B(z)_j=-sum_(i<j) z_i satisfy (1-s)B=1 and
B(1-s)=1-diagonal*pr_0; (-Bu,0) is the contracting homotopy of the complement.
The long exact cohomology sequence and the acyclic quotient therefore show that
the composite P -> Roos(V) is a quasi-isomorphism. Its product coordinates are
exactly constantTowerComponents i and its shifted component is zero, so it is
the stated augmentation. The Grothendieck hypothesis supplies K-injective
resolutions. Compute total right derived limit on these resolutions and use exact
countable products to identify it with this Roos cone (Tag 0941). Thus the
contracted quotient has zero derived limit. Uniqueness of right derived functors
transports this vanishing to every RF and unit η in the statement. This argument
works for unbounded complexes, including zero objects and exponent one. -/
theorem roosNilpotentExactAugmentation
    {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A]
    [IsGrothendieckAbelian.{g} A]
    [HasExactLimitsOfShape (Discrete ℕ) A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (P : CochainComplex A ℤ) (V Z : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (i : ((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ⟶ V) (p : V ⟶ Z) (hi : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hi).ShortExact) (a : ℕ) (ha : 1 ≤ a)
    (hnil : ∀ k : ℤ,
      (End.of (towerProductShift (K := fun n : ℕ ↦ (Z.X k).obj (op n))
        (fun n : ℕ ↦
        (Z.X k).map (homOfLE n.le_succ).op))) ^ a = 0) :
    QuasiIso (constantTowerRoosAugmentation i) ∧
      ∀ (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
        (η : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF),
        RF.IsRightDerivedFunctor η
          (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)) →
        IsZero (RF.obj (DerivedCategory.Q.{w}.obj Z)) := by sorry

end CategoryTheory
