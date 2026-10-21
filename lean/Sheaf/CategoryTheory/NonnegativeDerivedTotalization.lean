/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
import Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality
import Sheaf.CategoryTheory.KInjectiveComputes
import Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution

/-!
# Derived totalization of nonnegative cosimplicial complexes

Source: Stacks Project, Derived Categories, Tags 0141, 070J and 015J, and the
strict cosimplicial extension in the node's eight-step proof
(blueprint: lem-sfb-nonnegative-derived-totalization).

Nonnegative complexes use natural indices, and are extended by zero before localization
in the unbounded derived category. The total uses the alternating cofaces and the existing
finite-diagonal total: its differential is delta + (-1)^n d. If the internal complex itself
is a total with resolution degree s, the contributing triples are n+q+s=r, all nonnegative.
The structure below records normalized comparisons for actual resolved diagrams, retaining
all cofaces and codegeneracies. It never totalizes a bare ordinary-derived-category diagram.
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v' w w'

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The alternating-coface finite total, before localization. Source: Stacks Tag 015J,
finite-total construction (blueprint: lem-sfb-nonnegative-derived-totalization). -/
noncomputable def nonnegativeCosimplicialTotal :
    CosimplicialObject (CochainComplex C ℕ) ⥤ CochainComplex C ℕ :=
  AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex C ℕ) ⋙
    HomologicalComplex₂.totalFunctor C (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ)

/-- Localization of a nonnegative complex in the unbounded derived category, by the
canonical extension by zero. Source: Stacks Tags 0141 and 015J
(blueprint: lem-sfb-nonnegative-derived-totalization). -/
noncomputable def nonnegativeComplexLocalization [HasDerivedCategory.{w} C] :
    CochainComplex C ℕ ⥤ DerivedCategory C :=
  ComplexShape.embeddingUpNat.extendFunctor C ⋙ DerivedCategory.Q

/-- A compatible nonnegative injective replacement retains every cosimplicial operator.
Source: Stacks Tag 0141, diagramwise resolution
(blueprint: lem-sfb-nonnegative-derived-totalization). -/
structure NonnegativeCosimplicialResolution
    (K : CosimplicialObject (CochainComplex C ℕ)) where
  diagram : CosimplicialObject (CochainComplex C ℕ)
  augmentation : K ⟶ diagram
  quasiIso : ∀ n : SimplexCategory, QuasiIso (augmentation.app n)
  injective : ∀ (n : SimplexCategory) (q : ℕ), Injective ((diagram.obj n).X q)

variable {C} {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
  [Abelian.HasKInjectiveResolutions C]

/-- The existing right-derived unit, transported along extension by zero. This pins the
normalization of all comparisons below. Source: Stacks Tags 070K and 015J
(blueprint: lem-sfb-nonnegative-derived-totalization). -/
noncomputable def nonnegativeRightDerivedUnit (F : C ⥤ D) [F.Additive]
    (A : CochainComplex C ℕ) :
    (nonnegativeComplexLocalization D).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj A) ⟶
      F.rightDerivedFunctor.obj ((nonnegativeComplexLocalization C).obj A) :=
  DerivedCategory.Q.map (A.mapExtendIso ComplexShape.embeddingUpNat F).inv ≫
    F.rightDerivedFunctorUnitQ (A.extend ComplexShape.embeddingUpNat)

/-- The specified degree-zero component of a strict augmentation into the total.
Source: Stacks Tag 015J, augmented finite-total construction
(blueprint: lem-sfb-nonnegative-derived-totalization). -/
def IsNonnegativeTotalAugmentation
    {A : CochainComplex C ℕ} {K : CosimplicialObject (CochainComplex C ℕ)}
    (b : (Functor.const SimplexCategory).obj A ⟶ K)
    (a : A ⟶ (nonnegativeCosimplicialTotal C).obj K) : Prop :=
  ∀ r : ℕ, a.f r = (b.app ⦋0⦌).f r ≫
    HomologicalComplex₂.ιTotal
      ((AlgebraicTopology.alternatingCofaceMapComplex _).obj K)
      (ComplexShape.up ℕ) 0 r r (zero_add r)

variable (F : C ⥤ D) [F.Additive]

/-- The whole-object comparison, with finite-sum normalization, naturality, independence,
and strict augmentation compatibility. Source: Stacks Tags 0141, 070J and 015J
(blueprint: lem-sfb-nonnegative-derived-totalization).

The source of chi is RF(QT(K)); its target is QT(FJ), with J an actual compatible
injective replacement. The normalization equation is precisely chi = Q(beta) rho RF(Qu).
The naturality field applies to arbitrary compatible strict maps between replacements,
including maps of augmented diagrams. Uniqueness pins independence of resolution choices:
between R and S the canonical identification is (chi K R).symm followed by chi K S,
and naturality identifies every compatible strict comparison with it. Every strict map
f : K ⟶ L has compatible replacements with a strict comparison g, so that naturality
applies to it.
-/
structure NonnegativeDerivedTotalizationComparison where
  replacement : ∀ K : CosimplicialObject (CochainComplex C ℕ),
    Nonempty (NonnegativeCosimplicialResolution C K)
  mapReplacement : ∀ {K L : CosimplicialObject (CochainComplex C ℕ)} (f : K ⟶ L),
    ∃ (R : NonnegativeCosimplicialResolution C K) (S : NonnegativeCosimplicialResolution C L)
      (g : R.diagram ⟶ S.diagram), R.augmentation ≫ g = f ≫ S.augmentation
  beta : ∀ J : CosimplicialObject (CochainComplex C ℕ),
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((nonnegativeCosimplicialTotal C).obj J) ≅
      (nonnegativeCosimplicialTotal D).obj (J ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ))
  beta_summand : ∀ (J : CosimplicialObject (CochainComplex C ℕ))
      (n q r : ℕ) (h : n + q = r),
    F.map (HomologicalComplex₂.ιTotal
        ((AlgebraicTopology.alternatingCofaceMapComplex _).obj J)
        (ComplexShape.up ℕ) n q r h) ≫ (beta J).hom.f r =
      HomologicalComplex₂.ιTotal
        ((AlgebraicTopology.alternatingCofaceMapComplex _).obj
          (J ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ)))
          (ComplexShape.up ℕ) n q r h
  chi : ∀ (K : CosimplicialObject (CochainComplex C ℕ))
      (R : NonnegativeCosimplicialResolution C K),
    F.rightDerivedFunctor.obj ((nonnegativeComplexLocalization C).obj
        ((nonnegativeCosimplicialTotal C).obj K)) ≅
      (nonnegativeComplexLocalization D).obj ((nonnegativeCosimplicialTotal D).obj
        (R.diagram ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ)))
  normalized : ∀ (K : CosimplicialObject (CochainComplex C ℕ))
      (R : NonnegativeCosimplicialResolution C K),
    (chi K R).hom ≫ (nonnegativeComplexLocalization D).map (beta R.diagram).inv ≫
        nonnegativeRightDerivedUnit F ((nonnegativeCosimplicialTotal C).obj R.diagram) =
      F.rightDerivedFunctor.map ((nonnegativeComplexLocalization C).map
        ((nonnegativeCosimplicialTotal C).map R.augmentation))
  naturality : ∀ {K L : CosimplicialObject (CochainComplex C ℕ)}
      (R : NonnegativeCosimplicialResolution C K)
      (S : NonnegativeCosimplicialResolution C L) (f : K ⟶ L) (g : R.diagram ⟶ S.diagram),
    R.augmentation ≫ g = f ≫ S.augmentation →
      F.rightDerivedFunctor.map ((nonnegativeComplexLocalization C).map
          ((nonnegativeCosimplicialTotal C).map f)) ≫ (chi L S).hom =
        (chi K R).hom ≫ (nonnegativeComplexLocalization D).map
          ((nonnegativeCosimplicialTotal D).map
            (Functor.whiskerRight g (F.mapHomologicalComplex (ComplexShape.up ℕ))))
  unique : ∀ (K : CosimplicialObject (CochainComplex C ℕ))
      (R : NonnegativeCosimplicialResolution C K)
      (e : F.rightDerivedFunctor.obj ((nonnegativeComplexLocalization C).obj
          ((nonnegativeCosimplicialTotal C).obj K)) ≅
        (nonnegativeComplexLocalization D).obj ((nonnegativeCosimplicialTotal D).obj
          (R.diagram ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ)))),
    e.hom ≫ (nonnegativeComplexLocalization D).map (beta R.diagram).inv ≫
        nonnegativeRightDerivedUnit F ((nonnegativeCosimplicialTotal C).obj R.diagram) =
      F.rightDerivedFunctor.map ((nonnegativeComplexLocalization C).map
        ((nonnegativeCosimplicialTotal C).map R.augmentation)) → e = chi K R
  column : ∀ (K : CosimplicialObject (CochainComplex C ℕ))
      (R : NonnegativeCosimplicialResolution C K),
    K ⋙ nonnegativeComplexLocalization C ⋙ F.rightDerivedFunctor ≅
      R.diagram ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        nonnegativeComplexLocalization D
  column_normalized : ∀ (K : CosimplicialObject (CochainComplex C ℕ))
      (R : NonnegativeCosimplicialResolution C K) (n : SimplexCategory),
    (column K R).hom.app n ≫ nonnegativeRightDerivedUnit F (R.diagram.obj n) =
      F.rightDerivedFunctor.map
        ((nonnegativeComplexLocalization C).map (R.augmentation.app n))
  augmentedReplacement : ∀ (A : CochainComplex C ℕ)
      (K : CosimplicialObject (CochainComplex C ℕ))
      (b : (Functor.const SimplexCategory).obj A ⟶ K),
    ∃ (I : CochainComplex C ℕ) (r : A ⟶ I)
      (R : NonnegativeCosimplicialResolution C K)
      (c : (Functor.const SimplexCategory).obj I ⟶ R.diagram),
      QuasiIso r ∧ (∀ q : ℕ, Injective (I.X q)) ∧
        ∀ n : SimplexCategory, b.app n ≫ R.augmentation.app n = r ≫ c.app n
  augmentation : ∀ (A I : CochainComplex C ℕ) (r : A ⟶ I)
      (K : CosimplicialObject (CochainComplex C ℕ))
      (R : NonnegativeCosimplicialResolution C K)
      (b : (Functor.const SimplexCategory).obj A ⟶ K)
      (c : (Functor.const SimplexCategory).obj I ⟶ R.diagram),
    QuasiIso r → (∀ q : ℕ, Injective (I.X q)) →
    (∀ n : SimplexCategory, b.app n ≫ R.augmentation.app n = r ≫ c.app n) →
    ∃ (a : A ⟶ (nonnegativeCosimplicialTotal C).obj K)
      (aI : I ⟶ (nonnegativeCosimplicialTotal C).obj R.diagram)
      (eA : F.rightDerivedFunctor.obj ((nonnegativeComplexLocalization C).obj A) ≅
        (nonnegativeComplexLocalization D).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I)),
      IsNonnegativeTotalAugmentation b a ∧ IsNonnegativeTotalAugmentation c aI ∧
      (eA.hom ≫ nonnegativeRightDerivedUnit F I =
        F.rightDerivedFunctor.map ((nonnegativeComplexLocalization C).map r)) ∧
      (F.rightDerivedFunctor.map ((nonnegativeComplexLocalization C).map a) ≫
          (chi K R).hom =
        eA.hom ≫ (nonnegativeComplexLocalization D).map
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map aI ≫ (beta R.diagram).hom))

/-- Right derivation commutes with coherent nonnegative cosimplicial totalization.
Source: Stacks Tags 0141, 070J and 015J, with the node's strict cosimplicial extension
(blueprint: lem-sfb-nonnegative-derived-totalization).

Proof:
1. Obtain functorial injective embeddings in C and the lower-bound-preserving resolution
   functor of lem-weil-pbc-functorial-bounded-injective-resolution. Apply it simultaneously
   to all columns and augmentation objects. Naturality retains every simplex operator.
2. Form the alternating-coface bicomplex. Cosimplicial identities give delta squared zero;
   the cofaces are chain maps. Columnwise quasi-isomorphisms induce a total quasi-isomorphism
   by lem-sc-first-quadrant-total-column-comparison, transposing and using the sign (-1)^(nq).
3. Every diagonal is finite. Its injective summands give an injective total term. The total
   and each column are bounded below and K-injective by lem-sp-kinjective-computes. With a
   further resolution index s, only the finitely many triples n+q+s=r occur, with differential
   delta + (-1)^n d_q + (-1)^(n+q) d_s.
4. Additivity gives beta from the finite-biproduct identifications. Its summand equation
   proves the chain-map identities, its inverse identities, and naturality.
5. Set chi = Q(beta) rho RF(QT(u)), with rho the inverse derived unit on T(J). Columnwise
   the same inverse-unit computation identifies QF(J_n) with RF(QK_n).
6. For f : K -> L the functorial resolution gives g = I(f) with g u_K = u_L f.
   Apply lem-sp-derived-injective-resolution-naturality to each commuting resolution square,
   then compose with beta naturality. This proves the displayed whole-object square.
7. Compare two resolutions using L -> I(L) <- I(K) -> I(M) <- M. All columns are homotopy
   equivalences, preserved by additive F. First-quadrant comparison makes their mapped
   totals quasi-isomorphisms. Normalized naturality identifies every leg with chi_S chi_R^-1;
   consequently every compatible comparison gives this same identification.
8. Resolve the augmentation too. Its degree-zero coface differential vanishes because
   d^0 b_0 = d^1 b_0. Thus a and aI are the specified chain maps. Their square commutes;
   normalized resolution naturality and the summand formula for beta give the augmentation
   equation. Maps of augmented diagrams preserve these squares and all normalizations. -/
theorem nonnegative_derived_totalization
    [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D]
    [PreservesFiniteLimits F] : Nonempty (NonnegativeDerivedTotalizationComparison F) := by
  sorry

end CategoryTheory
