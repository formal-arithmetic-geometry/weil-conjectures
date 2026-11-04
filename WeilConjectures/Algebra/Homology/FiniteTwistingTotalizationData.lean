/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Data.Int.Interval
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.Abelian.Filtration
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Data for finite twisting totalizations

Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations (routine),
lines 12-24, the assembly of successive mapping-cylinder replacements
(blueprint: def-trf-finite-twisting-totalization-data).

These records package the input twisting family and the totalization characterized by
its summand differential, tail coordinates and quotient projections. No totalization
is chosen from an existence theorem. Its existence is stated separately.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})

/-- The existing finite-biproduct structure of an abelian module-sheaf category.
Source: finite direct sums in the mapping-cylinder assembly, sk-i-additivity.proof.md,
Filtered operations (routine) (blueprint: def-trf-finite-twisting-totalization-data). -/
instance finiteTwistingModuleBiproducts : HasFiniteBiproducts
    (ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- A bounded-above family with strictly increasing degree-one twisting components
satisfying the Maurer--Cartan equations. Composition in Lean is left to right.
Source: mapping-cylinder assembly in sk-i-additivity.proof.md, Filtered operations
(routine), lines 12-24 (blueprint: def-trf-finite-twisting-totalization-data). -/
structure FiniteTwistingFamily (a b : ℤ) where
  /-- The complexes indexed by the closed weight interval. -/
  G : ↥(Finset.Icc a b) → CochainComplex (ringedSiteModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ
  /-- Each complex has an upper term bound; no common bound is supplied as input. -/
  bounded : ∀ p : ↥(Finset.Icc a b), ∃ N : ℤ, ∀ n : ℤ, N < n → IsZero ((G p).X n)
  /-- Graded degree-one maps, with no individual chain-map condition. -/
  τ : ∀ (p q : ↥(Finset.Icc a b)), p.val < q.val →
    ∀ n : ℤ, (G p).X n ⟶ (G q).X (n + 1)
  /-- The only compatibility imposed on the twisting components. -/
  maurerCartan : ∀ (p q : ↥(Finset.Icc a b)) (hpq : p.val < q.val) (n : ℤ),
    τ p q hpq n ≫ (G q).d (n + 1) (n + 1 + 1) +
      (G p).d n (n + 1) ≫ τ p q hpq (n + 1) +
      ∑ r : {r : ↥(Finset.Icc a b) // p.val < r.val ∧ r.val < q.val},
        τ p r.val r.property.1 n ≫ τ r.val q r.property.2 (n + 1) = 0

variable {R} {a b : ℤ}

/-- A realization of a finite twisting family by the specified filtered total complex.
The coordinates, differential and quotient equations fix the canonical realization
up to its unique coordinate-preserving isomorphism. The splitting is degreewise.
Source: mapping-cylinder assembly in sk-i-additivity.proof.md, Filtered operations
(routine), lines 12-24 (blueprint: def-trf-finite-twisting-totalization-data). -/
structure FiniteTwistingTotalization (D : FiniteTwistingFamily R a b) where
  /-- The resulting cochain complex, with its square-zero differential. -/
  P : CochainComplex (ringedSiteModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ
  /-- The existing notion of decreasing filtration, on the complex itself. -/
  F : DecreasingFiltration P
  /-- Coordinates identify every term with the finite direct sum of the given terms. -/
  coordinates : ∀ n : ℤ, P.X n ≅ ⨁ fun p : ↥(Finset.Icc a b) ↦ (D.G p).X n
  /-- The canonical identifications of the quotient complexes. -/
  gradedIso : ∀ p : ↥(Finset.Icc a b), F.gradedPiece p.val ≅ D.G p
  /-- The differential is characterized on every summand; the weights add no signs. -/
  differential : ∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
    biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫
        (coordinates n).inv ≫ P.d n (n + 1) =
      (D.G p).d n (n + 1) ≫
          biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X (n + 1)) p ≫
            (coordinates (n + 1)).inv +
        ∑ q : {q : ↥(Finset.Icc a b) // p.val < q.val},
          D.τ p q.val q.property n ≫
            biproduct.ι (fun t : ↥(Finset.Icc a b) ↦ (D.G t).X (n + 1)) q.val ≫
              (coordinates (n + 1)).inv
  /-- Finiteness in the dependency's existing sense. -/
  finite : F.IsFinite
  /-- The full tail. -/
  bottomWeight : F.step a = ⊤
  /-- The empty tail. -/
  topWeight : F.step (b + 1) = ⊥
  /-- Term coordinates for every tail, including empty tails. -/
  tailCoordinates : ∀ r n : ℤ,
    ((F.step r : CochainComplex _ ℤ).X n) ≅
      ⨁ fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦ (D.G p.val).X n
  /-- Each tail inclusion is the inclusion of precisely the prescribed summands. -/
  tailInclusion : ∀ r n : ℤ,
    (tailCoordinates r n).inv ≫ (F.step r).arrow.f n =
      biproduct.desc (fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦
        biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p.val ≫
          (coordinates n).inv)
  /-- Splitting as module sheaves in each degree, not as complexes. -/
  degreewiseSplit : ∀ r n : ℤ, ∃ s : P.X n ⟶ (F.step r : CochainComplex _ ℤ).X n,
    (F.step r).arrow.f n ≫ s = 𝟙 _
  /-- The grade isomorphism is induced by the summand projection. -/
  gradedProjection : ∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
    (F.complexQuotientπ p.val (p.val + 1) (Int.le_add_one le_rfl)).f n ≫
        (gradedIso p).hom.f n =
      (F.step p.val).arrow.f n ≫ (coordinates n).hom ≫
        biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p
  /-- There are no other nonzero grades. -/
  outside : ∀ p : ℤ, (p < a ∨ b < p) → IsZero (F.gradedPiece p)

end CochainComplex
