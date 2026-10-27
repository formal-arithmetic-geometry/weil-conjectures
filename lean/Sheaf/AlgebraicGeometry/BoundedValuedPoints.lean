/-
Copyright (c) 2026 Q89. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q89
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap

/-!
# Bounded sets of valued-field points

Source: BLR, Néron Models, 1.1 Definition 2
(blueprint: def-sfb-bounded-valued-points).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- All the extension-field points are bounded in finite affine coordinates.
For a discrete valuation ring `A`, a common nonzero denominator is equivalent to
integer lower bounds on the valuations of the finitely many coordinates. Zero coordinates
are included automatically. The charts, their algebra structures, generators and subsets
are all quantified explicitly; the subsets cover the points, not necessarily every chart's
entire point set. Source: BLR 1.1 Definition 2
(blueprint: def-sfb-bounded-valued-points). -/
def HasBoundedValuedPoints
    (K F A : Type u) [Field K] [Field F] [CommRing A] [Algebra A F]
    (j : Spec (.of F) ⟶ Spec (.of K)) (X : Over (Spec (.of K))) : Prop :=
  ∃ (n : ℕ) (U : Fin n → X.left.Opens) (B : Fin n → CommAlgCat K)
    (e : ∀ i, Spec (.of (B i)) ≅ (U i).toScheme)
    (m : Fin n → ℕ) (b : ∀ i, Fin (m i) → B i)
    (C : ∀ i, Set (Spec (.of F) ⟶ Spec (.of (B i)))),
    (⋃ i, (U i : Set X.left)) = Set.univ ∧
    (∀ i, (e i).hom ≫ (U i).ι ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (B i)))) ∧
    (∀ i, Algebra.adjoin K (Set.range (b i)) = ⊤) ∧
    (∀ i, ∀ x ∈ C i,
      x ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B i))) = j) ∧
    (∀ x : Over.mk j ⟶ X, ∃ i, ∃ y ∈ C i, y ≫ (e i).hom ≫ (U i).ι = x.left) ∧
    ∃ d : A, d ≠ 0 ∧ ∀ i, ∀ x ∈ C i, ∀ l : Fin (m i),
      ∃ a : A, algebraMap A F a =
        algebraMap A F d * (Spec.preimage x).hom (b i l)

/-- Boundedness after the strict henselization at the chosen geometric point.
The fraction field is specified by its universal localization property, and the field
extension map is required to agree with the canonical map out of `R`.
Source: BLR 1.1 Definition 2 and 4.3 Proposition 4
(blueprint: def-sfb-bounded-valued-points). -/
def HasBoundedStrictHenselianPoints
    (R E : Type u) [CommRing R] [Field E] [Algebra R E]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of R)) (G : Over (Spec (.of E))) : Prop :=
  ∃ (F : Type u) (_ : Field F) (j : E →+* F)
    (_ : Algebra (Scheme.strictHenselizationRing t) F),
    IsFractionRing (Scheme.strictHenselizationRing t) F ∧
    j.comp (algebraMap R E) =
      (algebraMap (Scheme.strictHenselizationRing t) F).comp
        (Spec.preimage (Scheme.strictHenselizationStructuralMap t)).hom ∧
    HasBoundedValuedPoints E F (Scheme.strictHenselizationRing t)
      (Spec.map (CommRingCat.ofHom j)) G

end AlgebraicGeometry
