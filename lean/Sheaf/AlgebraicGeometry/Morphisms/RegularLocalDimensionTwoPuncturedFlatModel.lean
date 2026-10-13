/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Sheaf.RingTheory.Depth

/-!
# A finite flat model in regular local dimension two

Source: Stacks Project, Tag 0BMA, `pione-lemma-purity-regular`, dimension-two paragraph.
(blueprint: lem-sbc-regular-local-dimension-two-punctured-flat-model)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A punctured finite etale cover has a finite flat model with depth-two boundary stalks.

Source: Stacks Project, Tag 0BMA, `pione-lemma-purity-regular`, dimension-two case,
and Tag 0BM9, `pione-lemma-reformulate-purity-normal`.
(blueprint: lem-sbc-regular-local-dimension-two-punctured-flat-model)

Proof: Regularity makes A a normal domain. By 0BM9, B = Gamma(Y, O_Y) is
finite and normal over A, and Spec B restricts to Y over U. If Y is empty use
the zero algebra. Otherwise B is a finite product of normal domains. For each
factor, going down over the normal base and integrality give dimension two
at every maximal ideal lying over the closed point of A. Serre's S2 condition
therefore gives depth at least two at those localizations. They are
Cohen-Macaulay, and the finite closed fibre has dimension zero. Miracle
flatness over the regular local base makes each of these maximal localizations
flat over A. Since B is finite over the local ring A, all its maximal ideals
lie over that closed point, and the local criterion for flatness makes B flat.
Take F = Spec B with its structure map r. It is finite and flat. Every point
outside the inverse image of U lies over the closed point, hence corresponds
to one of the just-considered maximal ideals, proving the stalk depth bound.
The identification in 0BM9 is over U and gives the stated morphism equality.
Finite products preserve flatness and finiteness; for the zero algebra the
boundary depth assertion is vacuous. This proves all clauses without using
purity or asserting that r is etale. -/
theorem exists_finite_flat_model_of_regular_local_dimension_two
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2)
    (U : (Spec (.of A)).Opens)
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} (q : Y ⟶ U.toScheme) [IsFinite q] [Etale q] :
    ∃ (F : Scheme.{u}) (r : F ⟶ Spec (.of A)), IsLocallyNoetherian F ∧
      IsFinite r ∧ Flat r ∧
      (∀ x : F, x ∉ r ⁻¹ᵁ U →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk x) (F.presheaf.stalk x)) ∧
      ∃ e : Y ≅ (r ⁻¹ᵁ U).toScheme, e.hom ≫ r ∣_ U = q := by sorry

end AlgebraicGeometry.Scheme
