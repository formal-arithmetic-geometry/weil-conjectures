/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleDirectImageFiniteness
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness
import Sheaf.AlgebraicGeometry.FiniteCoefficientRealizationDirectImage
import Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-!
# Finiteness of proper direct images

Source: Weil blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1304;
SGA 4 1/2, Theoreme de finitude, Theorem 1.1; Stacks Tags 095U and 0GL0
(blueprint: thm-weil-pbc-direct-image-finiteness-proper).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private noncomputable def realizationDerivedDirectImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientRealization X Λ).mapDerivedCategory ⋙
        finiteCoefficientDerivedDirectImage f Λ ≅
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor ⋙
        (finiteCoefficientRealization Y Λ).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (finiteCoefficientRealization X Λ).rightDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
    (Functor.rightDerivedFunctorCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (finiteCoefficientRealization_directImage f Λ).some ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _

private noncomputable def fixedHigherDirectImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (DerivedCategory.homologyFunctor _ q).obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj E))) ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).obj
        (Etale.higherDirectImage Λ f q E) :=
  (DerivedCategory.homologyFunctor _ q).mapIso
      ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.mapIso
        (((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategorySingleFunctor
          0).app E).symm ≪≫
        ((rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ)).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj E)).symm) ≪≫
    (((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategoryHomologyFunctorIso
      q).app _).symm

private noncomputable def finiteHigherDirectImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    finiteCoefficientHigherDirectImage f Λ q ((finiteCoefficientComparison X Λ).obj E) ≅
      (finiteCoefficientComparison Y Λ).obj (Etale.higherDirectImage Λ f q E) :=
  (DerivedCategory.homologyFunctor _ q).mapIso
      ((finiteCoefficientDerivedDirectImage f Λ).mapIso
        (((finiteCoefficientRealization X Λ).mapDerivedCategorySingleFunctor 0).app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj E)).symm ≪≫
        (realizationDerivedDirectImageIso f Λ).app
          ((DerivedCategory.singleFunctor _ 0).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj E))) ≪≫
    (((finiteCoefficientRealization Y Λ).mapDerivedCategoryHomologyFunctorIso q).app _).symm ≪≫
    (finiteCoefficientRealization Y Λ).mapIso (fixedHigherDirectImageIso f Λ E q)

/-- Proper direct-image finiteness for Lambda = A/I^n, with the specified bound 2e.
The coefficient hypotheses are those of the adic datum: Noetherianity of A, finite
generation of I, additive torsion of A/I, and finiteness and perfectness of every
positive quotient over A. The positive index n fixes Lambda. No completeness of A
is assumed. The conclusion uses the recorded finite-coefficient FIN predicate.
Source: blueprint order 1304; SGA 4 1/2, finitude 1.1; Stacks Tags 095U and 0GL0
(blueprint: thm-weil-pbc-direct-image-finiteness-proper).

Proof:
1. For a constructible pro-etale F, choose its constructible etale origin G using
   def-weil-pbc-constructible-direct-image-finiteness. The finite ring A/I^n is killed
   by the positive additive order of 1: N m = (N 1)m = 0. Thus G is torsion.
   The coefficient orders are invertible on Y by hypothesis. Apply
   lem-weil-pbc-etale-proper-direct-image-finiteness: all nonnegative higher direct
   images of G are constructible and those in degrees above 2e vanish.
2. Properness gives finite type and separatedness, hence quasi-compactness and a
   quasi-compact diagonal (a closed immersion), so f is quasi-separated, as in
   def-weil-pbc-scheme-conventions and def-weil-closed-immersion. Apply
   prop-weil-pbc-comparison-direct-image to G in degree zero. By
   prop-weil-pbc-site-comparison-finite-level, comparison inverse image is exact;
   it preserves kernels, images and their quotients, hence commutes with cohomology.
   Consequently R^q f_* F is isomorphic to the comparison pullback of R^q f_* G.
   The latter is of constructible etale origin and is zero for q > 2e.
   These are precisely the two clauses of FIN(f,Lambda;2e), uniformly in F. -/
theorem constructibleDirectImageFiniteness_of_isProper
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (htorsion : IsAddTorsion (A ⧸ I))
    [hfinite : ∀ m : ℕ+, Finite (A ⧸ I ^ (m : ℕ))]
    (hperfect : ∀ m : ℕ+,
      @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _)
        ((@DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) _ _
          (HasDerivedCategory.standard _) 0).obj (ModuleCat.of A (A ⧸ I ^ (m : ℕ)))))
    (n : ℕ+)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hXdim : ∃ k : ℕ, topologicalKrullDim X ≤ (k : WithBot ℕ∞))
    (hYdim : ∃ k : ℕ, topologicalKrullDim Y ≤ (k : WithBot ℕ∞))
    (hXorders : ∀ (a : A ⧸ I ^ (n : ℕ)) (x : X),
      IsUnit (addOrderOf a : X.presheaf.stalk x))
    (hYorders : ∀ (a : A ⧸ I ^ (n : ℕ)) (y : Y),
      IsUnit (addOrderOf a : Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsProper f] (e : ℕ)
    (hfib : ∀ y : Y,
      topologicalKrullDim ↥(pullback f (Y.algClosurePoint y)) ≤ (e : WithBot ℕ∞)) :
    ConstructibleDirectImageFiniteness A I hI htorsion hperfect n
      hYdim hYorders f (2 * e) := by
  classical
  have _ := hXorders
  let Λ := A ⧸ I ^ (n : ℕ)
  let : TopologicalSpace Λ := ⊥
  let : DiscreteTopology Λ := ⟨rfl⟩
  change (∀ (F : FiniteCoefficientModules X Λ),
    IsConstructibleFiniteCoefficientSheaf X Λ F → ∀ q : ℤ, 0 ≤ q →
      IsConstructibleFiniteCoefficientSheaf Y Λ (finiteCoefficientHigherDirectImage f Λ q F)) ∧
    (∀ (F : FiniteCoefficientModules X Λ), IsConstructibleFiniteCoefficientSheaf X Λ F →
      ∀ q : ℤ, ((2 * e : ℕ) : ℤ) < q → IsZero (finiteCoefficientHigherDirectImage f Λ q F))
  have transfer (F : FiniteCoefficientModules X Λ)
      (hF : IsConstructibleFiniteCoefficientSheaf X Λ F) :
      (∀ q : ℤ, 0 ≤ q → IsConstructibleFiniteCoefficientSheaf Y Λ
        (finiteCoefficientHigherDirectImage f Λ q F)) ∧
      (∀ q : ℤ, (2 * e : ℤ) < q → IsZero (finiteCoefficientHigherDirectImage f Λ q F)) := by
    obtain ⟨E, hE, ⟨i⟩⟩ := hF
    have hfin := Etale.proper_directImage_finiteness hXdim hYdim f e hfib Λ hYorders E hE
    have j (q : ℤ) : finiteCoefficientHigherDirectImage f Λ q F ≅
        (finiteCoefficientComparison Y Λ).obj (Etale.higherDirectImage Λ f q E) :=
      (DerivedCategory.homologyFunctor _ q).mapIso
        ((finiteCoefficientDerivedDirectImage f Λ).mapIso
          ((DerivedCategory.singleFunctor _ 0).mapIso i)) ≪≫ finiteHigherDirectImageIso f Λ E q
    exact ⟨fun q hq ↦ ⟨_, hfin.1 q hq, ⟨j q⟩⟩,
      fun q hq ↦ IsZero.of_iso
        (Functor.map_isZero (finiteCoefficientComparison Y Λ) (hfin.2 q hq)) (j q)⟩
  exact ⟨fun F hF ↦ (transfer F hF).1, fun F hF q hq ↦ (transfer F hF).2 q (by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hq)⟩

end AlgebraicGeometry.ProEtale
