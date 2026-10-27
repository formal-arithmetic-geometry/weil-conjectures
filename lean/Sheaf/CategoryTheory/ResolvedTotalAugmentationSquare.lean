/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

/-!
# Normalized derived augmentation squares

Source: Stacks Project, derived.tex, Tags 0141 (functorial resolutions and remark-match),
015J (finite total), 070J, 070Y and 070K (inverse derived unit)
(blueprint: lem-sfb-resolved-total-augmentation-square).

The auxiliary structures package canonical maps and their equations. Their data are
specified by the degree-zero inclusion, the summand formula for beta, and the inverse
of the existing derived unit. No arbitrary comparison replaces any of these maps.
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v' w w'

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
  [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D]
  (F : C ⥤ D) [F.Additive]

/-- Canonical total augmentations, finite-sum comparisons, and inverse derived units.
Source: Stacks Tags 0141, 015J, 070J and 070Y
(blueprint: lem-sfb-resolved-total-augmentation-square).
The three normalization fields specify all morphism data uniquely; `totalInjective` supplies
the finite-diagonal injectivity needed to apply the inverse unit to a total. -/
structure ResolvedTotalAugmentationData where
  augmentation : ∀ {A : CochainComplex C ℕ} {K : CosimplicialObject (CochainComplex C ℕ)},
    ((Functor.const SimplexCategory).obj A ⟶ K) →
      (A ⟶ (HomologicalComplex₂.total (AlternatingCofaceMapComplex.obj K) (ComplexShape.up ℕ)))
  augmentation_component : ∀ {A : CochainComplex C ℕ}
      {K : CosimplicialObject (CochainComplex C ℕ)}
      (b : (Functor.const SimplexCategory).obj A ⟶ K),
    ∀ r : ℕ, (augmentation b).f r = (b.app ⦋0⦌).f r ≫
      HomologicalComplex₂.ιTotal
        ((alternatingCofaceMapComplex _).obj K)
        (ComplexShape.up ℕ) 0 r r (zero_add r)
  beta : ∀ J : CosimplicialObject (CochainComplex C ℕ),
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((HomologicalComplex₂.total (AlternatingCofaceMapComplex.obj J) (ComplexShape.up ℕ))) ≅
      (alternatingCofaceMapComplex (CochainComplex D ℕ) ⋙
      HomologicalComplex₂.totalFunctor D (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ)).obj (J ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ))
  beta_summand : ∀ (J : CosimplicialObject (CochainComplex C ℕ))
      (n q r : ℕ) (h : n + q = r),
    F.map (HomologicalComplex₂.ιTotal
        ((alternatingCofaceMapComplex _).obj J)
        (ComplexShape.up ℕ) n q r h) ≫ (beta J).hom.f r =
      HomologicalComplex₂.ιTotal
        ((alternatingCofaceMapComplex _).obj
          (J ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ)))
        (ComplexShape.up ℕ) n q r h
  beta_naturality : ∀ {J J' : CosimplicialObject (CochainComplex C ℕ)} (g : J ⟶ J'),
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((alternatingCofaceMapComplex (CochainComplex C ℕ) ⋙
      HomologicalComplex₂.totalFunctor C (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ)).map g) ≫ (beta J').hom =
      (beta J).hom ≫ (alternatingCofaceMapComplex (CochainComplex D ℕ) ⋙
      HomologicalComplex₂.totalFunctor D (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ)).map
        (Functor.whiskerRight g (F.mapHomologicalComplex (ComplexShape.up ℕ)))
  rho : ∀ (E : CochainComplex C ℕ), (∀ q : ℕ, Injective (E.X q)) →
    (F.rightDerivedFunctor.obj ((ComplexShape.embeddingUpNat.extendFunctor C ⋙
      DerivedCategory.Q).obj E) ≅
      (ComplexShape.embeddingUpNat.extendFunctor D ⋙ DerivedCategory.Q).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj E))
  rho_inverse : ∀ (E : CochainComplex C ℕ) (hE : ∀ q : ℕ, Injective (E.X q)),
    (rho E hE).inv =
      DerivedCategory.Q.map (E.mapExtendIso ComplexShape.embeddingUpNat F).inv ≫
        F.rightDerivedFunctorUnitQ (E.extend ComplexShape.embeddingUpNat)
  totalInjective : ∀ (J : CosimplicialObject (CochainComplex C ℕ)),
    (∀ (n : SimplexCategory) (q : ℕ), Injective ((J.obj n).X q)) →
      ∀ r : ℕ, Injective (((HomologicalComplex₂.total (AlternatingCofaceMapComplex.obj J)
        (ComplexShape.up ℕ))).X r)

namespace ResolvedTotalAugmentationData

variable {F}

/-- The normalized source comparison c_v = rho_B RF(Qv), in diagrammatic order.
Source: Stacks Tags 070Y/070K (blueprint: lem-sfb-resolved-total-augmentation-square). -/
noncomputable def sourceComparison (S : ResolvedTotalAugmentationData F)
    {A B : CochainComplex C ℕ} (v : A ⟶ B) (hB : ∀ q : ℕ, Injective (B.X q)) :
    F.rightDerivedFunctor.obj ((ComplexShape.embeddingUpNat.extendFunctor C ⋙
      DerivedCategory.Q).obj A) ⟶
      (ComplexShape.embeddingUpNat.extendFunctor D ⋙ DerivedCategory.Q).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj B) :=
  F.rightDerivedFunctor.map ((ComplexShape.embeddingUpNat.extendFunctor C ⋙
    DerivedCategory.Q).map v) ≫ (S.rho B hB).hom

/-- The normalized total comparison chi_u = Q(beta_J) rho_T(J) RF(QT(u)).
Source: Stacks Tags 015J and 070Y/070K
(blueprint: lem-sfb-resolved-total-augmentation-square). -/
noncomputable def totalComparison (S : ResolvedTotalAugmentationData F)
    {K J : CosimplicialObject (CochainComplex C ℕ)} (u : K ⟶ J)
    (hJ : ∀ (n : SimplexCategory) (q : ℕ), Injective ((J.obj n).X q)) :
    F.rightDerivedFunctor.obj ((ComplexShape.embeddingUpNat.extendFunctor C ⋙ DerivedCategory.Q).obj
        ((HomologicalComplex₂.total (AlternatingCofaceMapComplex.obj K) (ComplexShape.up ℕ)))) ⟶
      (ComplexShape.embeddingUpNat.extendFunctor D ⋙ DerivedCategory.Q).obj
        ((alternatingCofaceMapComplex (CochainComplex D ℕ) ⋙
      HomologicalComplex₂.totalFunctor D (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ)).obj
        (J ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ))) :=
  F.rightDerivedFunctor.map ((ComplexShape.embeddingUpNat.extendFunctor C ⋙ DerivedCategory.Q).map
      ((alternatingCofaceMapComplex (CochainComplex C ℕ) ⋙
      HomologicalComplex₂.totalFunctor C (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ)).map u)) ≫
    (S.rho _ (S.totalInjective J hJ)).hom ≫
      (ComplexShape.embeddingUpNat.extendFunctor D ⋙ DerivedCategory.Q).map (S.beta J).hom

/-- The mapped total augmentation beta_J F(a_J), with no chosen replacement map.
Source: Stacks Tag 015J (blueprint: lem-sfb-resolved-total-augmentation-square). -/
noncomputable def mappedAugmentation (S : ResolvedTotalAugmentationData F)
    {B : CochainComplex C ℕ} {J : CosimplicialObject (CochainComplex C ℕ)}
    (c : (Functor.const SimplexCategory).obj B ⟶ J) :
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj B ⟶
      (alternatingCofaceMapComplex (CochainComplex D ℕ) ⋙
      HomologicalComplex₂.totalFunctor D (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ)).obj (J ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ)) :=
  (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (S.augmentation c) ≫ (S.beta J).hom

end ResolvedTotalAugmentationData

/-- All augmentation equations, for every compatible choice of replacements and lifts.
Source: Stacks Tags 0141, 015J and 070Y/070K
(blueprint: lem-sfb-resolved-total-augmentation-square).
The strict naturality field includes a_J v = T(u) a. The remaining fields retain
whole-derived-object equalities, including their source and column normalizations. -/
structure ResolvedTotalAugmentationSquare extends ResolvedTotalAugmentationData F where
  augmentation_naturality : ∀ {A A' : CochainComplex C ℕ}
      {K K' : CosimplicialObject (CochainComplex C ℕ)}
      (b : (Functor.const SimplexCategory).obj A ⟶ K)
      (b' : (Functor.const SimplexCategory).obj A' ⟶ K') (h : A ⟶ A') (f : K ⟶ K'),
    (∀ n : SimplexCategory, b.app n ≫ f.app n = h ≫ b'.app n) →
      augmentation b ≫ (alternatingCofaceMapComplex (CochainComplex C ℕ) ⋙
      HomologicalComplex₂.totalFunctor C (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ)).map f = h ≫ augmentation b'
  mapped_component : ∀ {B : CochainComplex C ℕ}
      {J : CosimplicialObject (CochainComplex C ℕ)}
      (c : (Functor.const SimplexCategory).obj B ⟶ J) (r : ℕ),
    (toResolvedTotalAugmentationData.mappedAugmentation c).f r =
      F.map ((c.app ⦋0⦌).f r) ≫ HomologicalComplex₂.ιTotal
        ((alternatingCofaceMapComplex _).obj
          (J ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ)))
        (ComplexShape.up ℕ) 0 r r (zero_add r)
  comparison_isIso : ∀ {A B : CochainComplex C ℕ}
      {K J : CosimplicialObject (CochainComplex C ℕ)} (v : A ⟶ B) (u : K ⟶ J)
      (hB : ∀ q : ℕ, Injective (B.X q))
      (hJ : ∀ (n : SimplexCategory) (q : ℕ), Injective ((J.obj n).X q)),
    QuasiIso v → (∀ n : SimplexCategory, QuasiIso (u.app n)) →
      IsIso (toResolvedTotalAugmentationData.sourceComparison v hB) ∧
        IsIso (toResolvedTotalAugmentationData.totalComparison u hJ)
  square : ∀ {A B : CochainComplex C ℕ}
      {K J : CosimplicialObject (CochainComplex C ℕ)}
      (b : (Functor.const SimplexCategory).obj A ⟶ K)
      (c : (Functor.const SimplexCategory).obj B ⟶ J) (v : A ⟶ B) (u : K ⟶ J)
      (hB : ∀ q : ℕ, Injective (B.X q))
      (hJ : ∀ (n : SimplexCategory) (q : ℕ), Injective ((J.obj n).X q)),
    QuasiIso v → (∀ n : SimplexCategory, QuasiIso (u.app n)) →
    (∀ n : SimplexCategory, b.app n ≫ u.app n = v ≫ c.app n) →
      F.rightDerivedFunctor.map ((ComplexShape.embeddingUpNat.extendFunctor C ⋙
        DerivedCategory.Q).map (augmentation b)) ≫
          toResolvedTotalAugmentationData.totalComparison u hJ =
        toResolvedTotalAugmentationData.sourceComparison v hB ≫
          (ComplexShape.embeddingUpNat.extendFunctor D ⋙ DerivedCategory.Q).map
            (toResolvedTotalAugmentationData.mappedAugmentation c)
  columns : ∀ {A B : CochainComplex C ℕ}
      {K J : CosimplicialObject (CochainComplex C ℕ)}
      (b : (Functor.const SimplexCategory).obj A ⟶ K)
      (c : (Functor.const SimplexCategory).obj B ⟶ J) (v : A ⟶ B) (u : K ⟶ J)
      (hB : ∀ q : ℕ, Injective (B.X q))
      (hJ : ∀ (n : SimplexCategory) (q : ℕ), Injective ((J.obj n).X q)),
    QuasiIso v → (∀ n : SimplexCategory, QuasiIso (u.app n)) →
    (∀ n : SimplexCategory, b.app n ≫ u.app n = v ≫ c.app n) →
      ∀ n : SimplexCategory,
        F.rightDerivedFunctor.map ((ComplexShape.embeddingUpNat.extendFunctor C ⋙
          DerivedCategory.Q).map (b.app n)) ≫
            toResolvedTotalAugmentationData.sourceComparison (u.app n) (hJ n) =
          toResolvedTotalAugmentationData.sourceComparison v hB ≫
            (ComplexShape.embeddingUpNat.extendFunctor D ⋙ DerivedCategory.Q).map
              ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (c.app n))
  lifts : ∀ {A B A' B' : CochainComplex C ℕ}
      {K J K' J' : CosimplicialObject (CochainComplex C ℕ)}
      (b : (Functor.const SimplexCategory).obj A ⟶ K)
      (c : (Functor.const SimplexCategory).obj B ⟶ J)
      (b' : (Functor.const SimplexCategory).obj A' ⟶ K')
      (c' : (Functor.const SimplexCategory).obj B' ⟶ J')
      (v : A ⟶ B) (u : K ⟶ J) (v' : A' ⟶ B') (u' : K' ⟶ J')
      (h : A ⟶ A') (f : K ⟶ K') (ht : B ⟶ B') (g : J ⟶ J')
      (hB : ∀ q : ℕ, Injective (B.X q)) (hB' : ∀ q : ℕ, Injective (B'.X q))
      (hJ : ∀ (n : SimplexCategory) (q : ℕ), Injective ((J.obj n).X q))
      (hJ' : ∀ (n : SimplexCategory) (q : ℕ), Injective ((J'.obj n).X q)),
    QuasiIso v → QuasiIso v' →
    (∀ n : SimplexCategory, QuasiIso (u.app n)) →
    (∀ n : SimplexCategory, QuasiIso (u'.app n)) →
    (∀ n : SimplexCategory, b.app n ≫ u.app n = v ≫ c.app n) →
    (∀ n : SimplexCategory, b'.app n ≫ u'.app n = v' ≫ c'.app n) →
    (∀ n : SimplexCategory, b.app n ≫ f.app n = h ≫ b'.app n) →
    (∀ n : SimplexCategory, c.app n ≫ g.app n = ht ≫ c'.app n) →
    u ≫ g = f ≫ u' → v ≫ ht = h ≫ v' →
      toResolvedTotalAugmentationData.mappedAugmentation c ≫
          (alternatingCofaceMapComplex (CochainComplex D ℕ) ⋙
      HomologicalComplex₂.totalFunctor D (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ)).map
            (Functor.whiskerRight g (F.mapHomologicalComplex (ComplexShape.up ℕ))) =
        (F.mapHomologicalComplex (ComplexShape.up ℕ)).map ht ≫
          toResolvedTotalAugmentationData.mappedAugmentation c' ∧
      toResolvedTotalAugmentationData.sourceComparison v hB ≫
          (ComplexShape.embeddingUpNat.extendFunctor D ⋙ DerivedCategory.Q).map
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map ht) =
        F.rightDerivedFunctor.map ((ComplexShape.embeddingUpNat.extendFunctor C ⋙
          DerivedCategory.Q).map h) ≫
          toResolvedTotalAugmentationData.sourceComparison v' hB' ∧
      toResolvedTotalAugmentationData.totalComparison u hJ ≫
          (ComplexShape.embeddingUpNat.extendFunctor D ⋙ DerivedCategory.Q).map
            ((alternatingCofaceMapComplex (CochainComplex D ℕ) ⋙
      HomologicalComplex₂.totalFunctor D (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ)).map
            (Functor.whiskerRight g (F.mapHomologicalComplex (ComplexShape.up ℕ)))) =
        F.rightDerivedFunctor.map ((ComplexShape.embeddingUpNat.extendFunctor C ⋙
          DerivedCategory.Q).map
            ((alternatingCofaceMapComplex (CochainComplex C ℕ) ⋙
      HomologicalComplex₂.totalFunctor C (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ)).map f)) ≫
          toResolvedTotalAugmentationData.totalComparison u' hJ' ∧
      F.rightDerivedFunctor.map ((ComplexShape.embeddingUpNat.extendFunctor C ⋙
        DerivedCategory.Q).map (augmentation b)) ≫
          toResolvedTotalAugmentationData.totalComparison u hJ ≫
          (ComplexShape.embeddingUpNat.extendFunctor D ⋙ DerivedCategory.Q).map
            ((alternatingCofaceMapComplex (CochainComplex D ℕ) ⋙
      HomologicalComplex₂.totalFunctor D (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ)).map
            (Functor.whiskerRight g (F.mapHomologicalComplex (ComplexShape.up ℕ)))) =
        F.rightDerivedFunctor.map ((ComplexShape.embeddingUpNat.extendFunctor C ⋙
          DerivedCategory.Q).map h) ≫
          toResolvedTotalAugmentationData.sourceComparison v' hB' ≫
          (ComplexShape.embeddingUpNat.extendFunctor D ⋙ DerivedCategory.Q).map
            (toResolvedTotalAugmentationData.mappedAugmentation c')

/-- Normalized derived augmentation squares for every compatible injective replacement.
Source: Stacks Tags 0141, 015J, 070J, 070Y and 070K
(blueprint: lem-sfb-resolved-total-augmentation-square).

Proof:
1. Naturality of b along the two maps [0] -> [1] gives d^0 b_0 = b_1 = d^1 b_0.
   Their alternating difference is zero. The vertical sign in degree zero is +1,
   so the degree-zero inclusion composed with b_0 is a chain map. The same
   calculation gives a_J. The equation c_0 v = u_0 b_0 gives a_J v = T(u) a.
2. Apply lem-sfb-injective-finite-total-derived-comparison: finite diagonals give
   the summand-preserving beta and injective total terms; column quasi-isomorphisms
   give a total quasi-isomorphism. B, every J_n and T(J) are nonnegative injective
   complexes, hence K-injective (Tag 070J). The unit of def-sfb-right-derived-functor
   is invertible there (Tags 070Y/070K). Its inverse defines rho, c_v and chi_u.
3. Naturality at a_J gives RF(Qa_J) rho_T(J) = rho_B QF(a_J) in diagrammatic order.
   Substitute a_J v = T(u) a and compose with Q(beta_J) to obtain square.
4. The summand formula for beta gives precisely F(c_0) in cosimplicial degree zero,
   zero in every other summand. Unit naturality at c_n and u_n b_n = c_n v
   give the asserted column correspondence.
5. For compatible strict maps (h,f) and lifts (ht,g), degree-zero components give
   T(f) a = a' h and T(g) a_J = a'_J ht. Naturality of beta then gives
   T(Fg) beta_J F(a_J) = beta_J' F(a'_J) F(ht).
6. Unit naturality at ht and T(g), followed by gu = u'f and ht v = v'h, proves
   naturality of c_v and chi_u. Combine those equations with square and step 5
   for the localized augmentation square. Every calculation uses only the stated
   hypotheses, so the result holds for every compatible replacement and lift. -/
theorem resolved_total_augmentation_square
    [PreservesFiniteLimits F] : Nonempty (ResolvedTotalAugmentationSquare F) := by
  sorry

end CategoryTheory
