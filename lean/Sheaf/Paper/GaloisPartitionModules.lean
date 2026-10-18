/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Galois partitions and their weakly constructible module sheaves

Source: ILO, Travaux de Gabber, Expose XVII, Definitions 7.3.1--7.3.3
(blueprint: def-per-galois-partition-modules).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Finite locally closed strata with connected reduced scheme structures and connected
finite etale Galois covers. The intrinsic Galois predicate is equivalent to a finite group
acting simply transitively on geometric fibres, by FiniteEtale.isGalois_iff.
Source: ILO XVII, Definition 7.3.1 (blueprint: def-per-galois-partition-modules). -/
structure GaloisPartition (X : Scheme.{u}) extends
    toStratification : FiniteLocallyClosedStratification X where
  /-- Each stratum is nonempty and connected. -/
  connected : ∀ i, ConnectedSpace (domain i)
  /-- Each stratum has its reduced scheme structure. -/
  reduced : ∀ i, IsReduced (domain i)
  /-- A finite etale cover of each stratum. -/
  cover : ∀ i, (domain i).FiniteEtale
  /-- Its geometric fibres are torsors under its finite automorphism group. -/
  galois : ∀ i, @PreGaloisCategory.IsGalois _ _
    (@FiniteEtale.galoisCategory (domain i) (connected i)) (cover i)

/-- Finite successive extensions of local systems trivialized by one finite etale cover.
A chain of short exact sequences includes the zero-length filtration.
Source: ILO XVII, Definition 7.3.3 (blueprint: def-per-galois-partition-modules). -/
def GaloisPartition.FiniteExtensions {S : Scheme.{u}} (V : S.FiniteEtale)
    (A : Type (u + 1)) [CommRing A]
    (E : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) : Prop :=
  ∃ n : ℕ, ∃ H : Fin (n + 1) → Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A),
    IsZero (H 0) ∧ Nonempty (H (Fin.last n) ≅ E) ∧
    ∀ i : Fin n, ∃ T : ShortComplex (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)),
      T.ShortExact ∧ Nonempty (T.X₁ ≅ H i.castSucc) ∧
      Nonempty (T.X₂ ≅ H i.succ) ∧ IsLocallyConstantSheaf T.X₃ ∧
      Sheaf.IsConstant V.obj.left.smallEtaleTopology
        ((Etale.upperStar (ModuleCat.{u + 1} A) V.obj.hom).obj T.X₃)

/-- The class W_P(A): on each stratum a filtered colimit of finite successive extensions
of local systems trivialized by its cover. No finite-generation condition is imposed.
The indexing category and its morphisms have size at most u+1, the size of module values.
Source: ILO XVII, Definition 7.3.3 (blueprint: def-per-galois-partition-modules). -/
def GaloisPartition.modules {X : Scheme.{u}} (P : GaloisPartition X)
    (A : Type (u + 1)) [CommRing A] :
    ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  fun E ↦ ∀ i, ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I),
    ∃ D : I ⥤ Sheaf (P.domain i).smallEtaleTopology (ModuleCat.{u + 1} A),
      (∀ j, GaloisPartition.FiniteExtensions (P.cover i) A (D.obj j)) ∧
      ∃ c : Cocone D, Nonempty (IsColimit c) ∧
        Nonempty (c.pt ≅ (Etale.upperStar (ModuleCat.{u + 1} A) (P.immersion i)).obj E)

/-- Refinement means inclusion of the weakly constructible classes for the ground ring.
This is the source's definition, rather than a requirement of maps of covers.
Source: ILO XVII, Definition 7.3.3 (blueprint: def-per-galois-partition-modules). -/
def GaloisPartition.Refines {X : Scheme.{u}} (Q P : GaloisPartition X)
    (Λ : Type (u + 1)) [CommRing Λ] : Prop :=
  P.modules Λ ≤ Q.modules Λ

/-- Bounded objects whose cohomology sheaves belong to W_P(A).
Source: ILO XVII, Definition 7.3.3 (blueprint: def-per-galois-partition-modules). -/
def GaloisPartition.boundedDerived {X : Scheme.{u}} (P : GaloisPartition X)
    (A : Type (u + 1)) [CommRing A] : ObjectProperty (Etale.DerivedCategoryModule A X) :=
  fun K ↦ (∀ q : ℤ, P.modules A ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)

end AlgebraicGeometry.Scheme
