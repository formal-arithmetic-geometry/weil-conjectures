/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Constructible direct-image finiteness with a specified bound

Source: Weil conjectures blueprint, sec-proper-base-change/sk-thm-properbasechange,
order 1301; Stacks Project, Section 09AI (the comparison context)
(blueprint: def-weil-pbc-constructible-direct-image-finiteness).

The coefficient assumptions of the adic datum are written explicitly; its completed
coefficient ring and derived reduction tower do not enter this finite-level predicate.
The bound is a parameter. Existence of a bound is a separate existential predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- A finite-coefficient module sheaf is constructible precisely when it is isomorphic,
linearly over the specified coefficient ring sheaf, to the comparison inverse image of
a constructible etale module sheaf. The etale predicate uses finite constructible strata
and finite locally constant module values. Source: blueprint order 1301; Stacks 09AI
(blueprint: def-weil-pbc-constructible-direct-image-finiteness). -/
def IsConstructibleFiniteCoefficientSheaf (V : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (F : FiniteCoefficientModules V Λ) : Prop :=
  ∃ E : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ),
    Scheme.IsConstructibleEtaleModuleSheaf E ∧
      Nonempty (F ≅ (finiteCoefficientComparison V Λ).obj E)

/-- The higher direct image is cohomology of ordinary uncompleted derived direct image
of the sheaf in degree zero. Source: blueprint order 1301; Stacks Section 07A5
(blueprint: def-weil-pbc-constructible-direct-image-finiteness). -/
noncomputable def finiteCoefficientHigherDirectImage {S T : Scheme.{u}} (f : S ⟶ T)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (q : ℤ) (F : FiniteCoefficientModules S Λ) : FiniteCoefficientModules T Λ :=
  (DerivedCategory.homologyFunctor (FiniteCoefficientModules T Λ) q).obj
    ((finiteCoefficientDerivedDirectImage f Λ).obj
      ((DerivedCategory.singleFunctor (FiniteCoefficientModules S Λ) 0).obj F))

/-- FIN at the positive quotient level n of the adic coefficient datum, with the fixed
nonnegative bound c. The ambient assumptions are binders, not clauses of FIN: A is
commutative Noetherian, I is finitely generated, A/I is additively torsion, all positive
quotients are finite and perfect over A, and T is Noetherian of finite dimension with
all additive orders of the chosen quotient invertible in its local rings.
The coefficient quotient is given its discrete topology in the body.

FIN has exactly two clauses: all nonnegative higher direct images of every constructible
sheaf are constructible, and all higher direct images above c vanish. The bound is
independent of F. No assertion that FIN holds for all morphisms is included.
Source: blueprint order 1301 (blueprint: def-weil-pbc-constructible-direct-image-finiteness). -/
def ConstructibleDirectImageFiniteness
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (_hI : I.FG) (_htorsion : IsAddTorsion (A ⧸ I))
    [hfinite : ∀ m : ℕ+, Finite (A ⧸ I ^ (m : ℕ))]
    (_hperfect : ∀ m : ℕ+,
      @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _)
        ((@DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) _ _
          (HasDerivedCategory.standard _) 0).obj (ModuleCat.of A (A ⧸ I ^ (m : ℕ)))))
    (n : ℕ+) {S T : Scheme.{u}} [IsNoetherian T]
    (_hdim : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (_horder : ∀ (a : A ⧸ I ^ (n : ℕ)) (t : T),
      IsUnit (addOrderOf a : T.presheaf.stalk t))
    (f : S ⟶ T) (c : ℕ) : Prop :=
  letI : TopologicalSpace (A ⧸ I ^ (n : ℕ)) := ⊥
  letI : DiscreteTopology (A ⧸ I ^ (n : ℕ)) := ⟨rfl⟩
  (∀ (F : FiniteCoefficientModules S (A ⧸ I ^ (n : ℕ))),
    IsConstructibleFiniteCoefficientSheaf S (A ⧸ I ^ (n : ℕ)) F →
      ∀ q : ℤ, 0 ≤ q → IsConstructibleFiniteCoefficientSheaf T (A ⧸ I ^ (n : ℕ))
        (finiteCoefficientHigherDirectImage f (A ⧸ I ^ (n : ℕ)) q F)) ∧
  (∀ (F : FiniteCoefficientModules S (A ⧸ I ^ (n : ℕ))),
    IsConstructibleFiniteCoefficientSheaf S (A ⧸ I ^ (n : ℕ)) F →
      ∀ q : ℤ, (c : ℤ) < q →
        IsZero (finiteCoefficientHigherDirectImage f (A ⧸ I ^ (n : ℕ)) q F))

end AlgebraicGeometry.ProEtale
