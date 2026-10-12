/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.ModelCategory.Injective
import Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource

/-! # Augmented comparison of Cartan–Eilenberg resolutions

Source: Stacks Project, Tags 015H, 015I and 015K
(blueprint: lem-weil-pbc-ce-augmented-comparison).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An exact additive functor admits an augmented bicomplex comparison.
This statement concerns the comparison itself; it does not form total complexes.
Source: Stacks Project, Tags 015H, 015I and 015K
(blueprint: lem-weil-pbc-ce-augmented-comparison).

Proof: in every complex degree p use the exact sequences
0 → Bᵖ → Zᵖ → Hᵖ → 0 and 0 → Zᵖ → Kᵖ → Bᵖ⁺¹ → 0, and their
resolution-column analogues. Exactness of F preserves these sequences and the
augmented column exactness. For the target, the stated injectivity conditions
make the boundary, cycle, cohomology and original columns injective resolutions;
the sequences are degreewise short exact by abelian homology theory.
Choose a common lower bound for I and J. Below that bound all boundary columns
are zero. Induct on p starting with the zero map on the lowest boundary column.
Given its comparison map, lift the cohomology augmentation map through the source
augmentation into the target injective cohomology column by the lifting property
of monomorphic quasi-isomorphisms against bounded-below injective complexes
(lem-weil-pbc-lift-along-injective-quasi-iso, Stacks Tag 013P(2)). Apply
exists_horseshoe_morphism_lift_exact_source to the boundary/cycle/cohomology
sequence to get a cycle comparison compatible with both endpoint maps.
Lift the next boundary augmentation map by the same lifting property. Apply
the exact-source horseshoe lift to the cycle/original/next-boundary sequence
with these chosen endpoint maps to obtain the original column comparison.
Retain the next-boundary map for the next induction step, choosing each map
only once. The horizontal differential factors through the next-boundary and
next-cycle columns. The endpoint equations from the two horseshoe lifts make
the original column comparisons commute with this factorization. Each is already
a chain map in the resolution degree. They therefore assemble into a bicomplex
map. Their degree-zero augmentation equations are exactly the displayed identity,
using singleObjXSelf to identify the source single-degree components. -/
theorem exists_cartanEilenberg_augmented_comparison
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (u : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (hIbelow : ∃ i : ℤ, ∀ p : ℤ, p < i → IsZero (I.X p))
    (hIcol : ∀ p : ℤ, QuasiIso (eI.f p))
    (hIres : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eI p) ∧
      QuasiIso (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eI p))
    (J : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eJ : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ J)
    (hJbelow : ∃ i : ℤ, ∀ p : ℤ, p < i → IsZero (J.X p))
    (hJcol : ∀ p : ℤ, QuasiIso (eJ.f p))
    (hJinj : ∀ (p : ℤ) (q : ℕ), Injective ((J.X p).X q))
    (hJinj' : ∀ (p : ℤ) (q : ℕ),
      Injective ((J.cycles p).X q) ∧
      Injective ((image (J.d (p - 1) p)).X q) ∧
      Injective ((J.homology p).X q))
    (hJres : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eJ p) ∧
      QuasiIso (image.map (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p) (eJ.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eJ p)) :
    let FI : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ) :=
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I
    ∃ φ : FI ⟶ J, ∀ p : ℤ,
      F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).inv ≫
          (eI.f p).f 0) ≫ (φ.f p).f 0 =
        u.f p ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X p)).inv ≫
          (eJ.f p).f 0 := by sorry

end CategoryTheory
