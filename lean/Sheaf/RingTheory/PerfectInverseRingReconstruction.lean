/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Perfect reconstruction over infinitesimal inverse systems of rings

Source: Stacks Project, More on Algebra, Tag 0CQG, lemma-Rlim-perfect-gives-perfect,
alternative (2) with every level perfect.
(blueprint: lem-sfb-perfect-inverse-ring-reconstruction).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- The derived inverse limit of a compatible tower of perfect complexes over a surjective
locally nilpotent tower of rings is perfect, and its projection adjuncts are isomorphisms.
Source: Stacks Project, More on Algebra, Tag 0CQG, lemma-Rlim-perfect-gives-perfect,
alternative (2) with every level perfect.
(blueprint: lem-sfb-perfect-inverse-ring-reconstruction).

The index `0` denotes the source's level `1`. The compatible-tuple property `hlim`
presents the inverse-limit ring, without choosing an isomorphic model. The left adjoints
`L` and `M` represent derived scalar extension, uniquely determined up to adjunction-compatible
isomorphism. The equation `hχ` normalizes the comparison of successive restrictions on
cochain representatives. It is the canonical comparison, not an arbitrary identification.

Proof: apply lem-sfb-nil-ring-perfect-derived-limit to the surjective tower with elementwise
nilpotent kernels to the supplied tower and Roos triangle. Its perfectness conclusion gives
`IsPerfectRingComplex E`; its projection conclusion is exactly the displayed adjunct for
`pE ≫ Pi.π _ n`. Both towers are restricted to the same `D(A)` and the supplied
Roos triangle is the one used by that theorem. Its additional naturality and transition
compatibility conclusions are not needed. -/
theorem perfect_inverse_ring_reconstruction
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (hsurj : ∀ n, Function.Surjective (φ n))
    (hnil : ∀ n x, φ n x = 0 → IsNilpotent x)
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (hlim : ∀ x : ∀ n, R n, (∀ n, φ n (x (n + 1)) = x n) →
      ∃! a : A, ∀ n, q n a = x n)
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [∀ n, HasDerivedCategory.{w} (ModuleCat.{u} (R n))]
    (L : ∀ n, DerivedCategory (ModuleCat.{u} (R (n + 1))) ⥤
      DerivedCategory (ModuleCat.{u} (R n)))
    (adjφ : ∀ n, L n ⊣ (ModuleCat.restrictScalars (φ n)).mapDerivedCategory)
    (M : ∀ n, DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (R n)))
    (adjq : ∀ n, M n ⊣ (ModuleCat.restrictScalars (q n)).mapDerivedCategory)
    (χ : ∀ n, (ModuleCat.restrictScalars (q n)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory)
    (hχ : ∀ n (C : CochainComplex (ModuleCat.{u} (R n)) ℤ),
      (χ n).hom.app (Q.obj C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map
          ((ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj C) =
      (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.hom.app C ≫
        Q.map ((NatIso.mapHomologicalComplex
          (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n))
          (.up ℤ)).hom.app C))
    (Eₙ : ∀ n, DerivedCategory (ModuleCat.{u} (R n)))
    (t : ∀ n, Eₙ (n + 1) ⟶
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.obj (Eₙ n))
    (hred : ∀ n, IsIso (((adjφ n).homEquiv (Eₙ (n + 1)) (Eₙ n)).symm (t n)))
    (hperfect : ∀ n, IsPerfectRingComplex (Eₙ n))
    [HasProduct (fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))]
    (E : DerivedCategory (ModuleCat.{u} A))
    (pE : E ⟶ ∏ᶜ fun n ↦
      (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))
    (δ : (∏ᶜ fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n)) ⟶
      E⟦(1 : ℤ)⟧)
    (hE : IsDerivedLimitTriangle
      (fun n ↦ (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
        (χ n).inv.app (Eₙ n)) E pE δ) :
    IsPerfectRingComplex E ∧
    (∀ n, IsIso (((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n))) := by
  sorry

end DerivedCategory
