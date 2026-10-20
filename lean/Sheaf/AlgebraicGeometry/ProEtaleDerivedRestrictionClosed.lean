/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.KFlat

/-! # Closed monoidal derived restriction on the pro-etale site

This is the native constant-coefficient form of the restriction theorem for derived internal
Hom. The normalization specifies the tensor comparison before any dualizing object is chosen.

Source: Stacks Project, Tag 08JB, `sites-cohomology.tex`,
`lemma-restriction-RHom-to-U`; the native constant-coefficient slice construction.
(blueprint: lem-weil-proetale-derived-restriction-closed-monoidal).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u z

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The existing native derived tensor, with its plain bifunctor signature exposed.
Source: blueprint order 2124, proof step 4 (blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionNativeTensor
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u}) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  MonoidalCategory.curriedTensor _

/-- The type of derived tensor comparisons for ordinary pro-etale inverse image.
Source: blueprint order 2124, proof step 4; Stacks 08JB
(blueprint: lem-weil-delta-restriction). -/
abbrev DeltaRestrictionTensorComparison
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {W Y : Scheme.{u}} (j : W ⟶ Y) :=
  Functor.curry.obj
      ((upperStar A j).mapDerivedCategory.prod
        (upperStar A j).mapDerivedCategory ⋙
          Functor.uncurry.obj (deltaRestrictionNativeTensor A W)) ≅
      Functor.curry.obj (Functor.uncurry.obj
        (deltaRestrictionNativeTensor A Y) ⋙
          (upperStar A j).mapDerivedCategory)

/-- The comparison square with the ordinary homotopy tensor map and localization.
It fixes the derived comparison on every K-flat model and hence everywhere.
Source: blueprint order 2124, proof step 4; Stacks 08JB
(blueprint: lem-weil-delta-restriction). -/
def IsNormalizedDeltaRestrictionTensor
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {W Y : Scheme.{u}} (j : W ⟶ Y)
    (e : DeltaRestrictionTensorComparison A j) : Prop :=
  ∀ P Q : HomotopyCategory
      (Sheaf (Scheme.ProEt.topology Y) A) (.up ℤ),
      (upperStar A j).mapDerivedCategory.map
          (Functor.LaxMonoidal.μ
            (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology Y) A)) P Q) ≫
        (upperStar A j).mapDerivedCategoryFactorsh.hom.app (P ⊗ Q) ≫
        (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology W) A)).map
          (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
            (upperStar A j)).app P).app Q) =
      (e.inv.app
        ((DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology Y)
          A)).obj P)).app
          ((DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology Y)
            A)).obj Q) ≫
        ((upperStar A j).mapDerivedCategoryFactorsh.hom.app P ⊗ₘ
          (upperStar A j).mapDerivedCategoryFactorsh.hom.app Q) ≫
        Functor.LaxMonoidal.μ
          (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology W) A))
          (((upperStar A j).mapHomotopyCategory (.up ℤ)).obj P)
          (((upperStar A j).mapHomotopyCategory (.up ℤ)).obj Q)


/-- Exact restriction along a weakly etale morphism is closed and braided monoidal on
unbounded derived categories. Any natural tensor comparison satisfying its homotopy
localization square is the tensor map of this monoidal structure.

Source: Stacks Project, Tag 08JB (restriction of derived internal Hom), and the
Koszul tensor construction in Tags 06YU and 0FPT; blueprint order 2124, restriction
and evaluation paragraphs
(blueprint: lem-weil-proetale-derived-restriction-closed-monoidal).

Proof: Identify the pro-etale site of W with the slice over W. The inverse-image functor
is exact slice restriction, is strong symmetric monoidal, and preserves flat sheaves.
Derive its ordinary tensor comparison on K-flat resolutions. The unit is the restriction
of the constant tensor-unit sheaf. Associativity and the unit identities descend from
complexes, and the Koszul interchange descends to give the braided identity. The stated
normalization determines every component: choose K-flat resolutions whose restrictions
are K-flat; the localization tensor maps and the exact-functor factor maps are then
invertible, so the displayed square determines the comparison there. Naturality transports
it to all derived objects. Thus the given comparison supplies the same tensor maps.

Slice restriction has an exact sum-extension left adjoint, hence preserves K-injective
complexes. Represent the second argument of internal Hom by a K-injective complex and
the first by a K-flat complex. On every object of the slice, restriction of their Hom
complex is the Hom complex of their restrictions, with differential
`d(f) = d_I f - (-1)^deg(f) f d_P`. Evaluation is the same local application map.
Consequently this isomorphism is precisely the closed comparison of the normalized
monoidal structure, rather than merely an isomorphism between the same objects. It is
natural in both arguments, and proves the final isomorphism assertion. No boundedness
or perfectness is used. The empty site gives the same conclusion in the zero category.
-/
theorem exists_normalizedRestrictionMonoidalClosed
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A] {W Y : Scheme.{u}} (j : W ⟶ Y) [WeaklyEtale j]
    (e : DeltaRestrictionTensorComparison A j)
    (he : IsNormalizedDeltaRestrictionTensor A j e) :
    letI := _root_.DerivedCategory.braidedCategory' (Sheaf (Scheme.ProEt.topology Y) A)
    letI := _root_.DerivedCategory.braidedCategory' (Sheaf (Scheme.ProEt.topology W) A)
    ∃ m : (upperStar A j).mapDerivedCategory.Monoidal,
      letI := m
      (∀ K L, Functor.LaxMonoidal.μ (upperStar A j).mapDerivedCategory K L =
        (e.hom.app K).app L) ∧
      (∀ K L, Functor.LaxMonoidal.μ (upperStar A j).mapDerivedCategory K L ≫
          (upperStar A j).mapDerivedCategory.map (β_ K L).hom =
        (β_ ((upperStar A j).mapDerivedCategory.obj K)
          ((upperStar A j).mapDerivedCategory.obj L)).hom ≫
            Functor.LaxMonoidal.μ (upperStar A j).mapDerivedCategory L K) ∧
      (∀ K, IsIso (Functor.LaxMonoidal.ihomComparison
        (upperStar A j).mapDerivedCategory K).natTrans) := by
  sorry

end AlgebraicGeometry.ProEtale
