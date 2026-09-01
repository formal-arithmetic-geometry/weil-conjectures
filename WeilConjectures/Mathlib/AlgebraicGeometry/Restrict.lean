/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Restrictions of morphisms of schemes along open immersions

We record:

- `AlgebraicGeometry.morphismRestrictArrowIso` — transport of a morphism restriction along
  compatible open immersions;
- `AlgebraicGeometry.mem_opensRange_homOfLE` / `AlgebraicGeometry.homOfLE_preimage_opensRange`
  — membership and preimage formulas for the ranges of inclusions of opens;
- `AlgebraicGeometry.Scheme.divBasicOpen` — the quotient `a / b` of two global sections, as a
  section over the basic open `X_b`, where `b` is invertible.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y Z Z' : Scheme.{u}}

/-- If `e ≫ f = q ≫ j` with `e`, `j` open immersions and `f ⁻¹ᵁ (range j) = range e`, then
the restriction `f ∣_ j.opensRange` is isomorphic to `q` in the arrow category. -/
noncomputable def morphismRestrictArrowIso (f : X ⟶ Y) {e : Z ⟶ X} {j : Z' ⟶ Y}
    (q : Z ⟶ Z') [IsOpenImmersion e] [IsOpenImmersion j]
    (w : e ≫ f = q ≫ j) (h : f ⁻¹ᵁ j.opensRange = e.opensRange) :
    Arrow.mk (f ∣_ j.opensRange) ≅ Arrow.mk q := by
  have hα : Set.range ⇑(f ⁻¹ᵁ j.opensRange).ι = Set.range ⇑e := by
    rw [Scheme.Opens.range_ι, h]; rfl
  have hβ : Set.range ⇑j.opensRange.ι = Set.range ⇑j := by
    rw [Scheme.Opens.range_ι]; rfl
  refine Arrow.isoMk' (f ∣_ j.opensRange) q
    (IsOpenImmersion.isoOfRangeEq (f ⁻¹ᵁ j.opensRange).ι e hα)
    (IsOpenImmersion.isoOfRangeEq j.opensRange.ι j hβ) ?_
  rw [← cancel_mono j, Category.assoc, Category.assoc, ← w,
    IsOpenImmersion.isoOfRangeEq_hom_fac_assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, morphismRestrict_ι]

/-- Membership in the range of the inclusion of a smaller open. -/
lemma mem_opensRange_homOfLE {X : Scheme.{u}} {U V : X.Opens} (hUV : U ≤ V)
    (x : V.toScheme) : x ∈ (X.homOfLE hUV).opensRange ↔ x.1 ∈ U := by
  rw [Scheme.opensRange_homOfLE]
  exact Iff.rfl

/-- Preimages of ranges of inclusions of opens. -/
lemma homOfLE_preimage_opensRange {X : Scheme.{u}} {U V W : X.Opens} (hWU : W ≤ U)
    (hUV : U ≤ V) :
    X.homOfLE hUV ⁻¹ᵁ (X.homOfLE (hWU.trans hUV)).opensRange =
      (X.homOfLE hWU).opensRange := by
  rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage,
    Scheme.homOfLE_ι]

section BasicOpen

variable (X : Scheme.{u})

/-- The restriction of a global section `b` to the basic open `X_b` is a unit. -/
lemma Scheme.isUnit_ι_appTop_basicOpen (b : Γ(X, ⊤)) :
    IsUnit ((X.basicOpen b).ι.appTop b) := by
  refine Scheme.isUnit_of_basicOpen_eq_top _ ?_
  rw [← Scheme.preimage_basicOpen_top, Scheme.Opens.ι_preimage_self]

/-- The quotient `a / b` of two global sections of `X`, as a section over the basic open
`X_b`, where `b` becomes invertible. -/
noncomputable def Scheme.divBasicOpen (a b : Γ(X, ⊤)) : Γ((X.basicOpen b : Scheme.{u}), ⊤) :=
  Ring.inverse ((X.basicOpen b).ι.appTop b) * (X.basicOpen b).ι.appTop a

@[simp]
lemma Scheme.divBasicOpen_mul_self (a b : Γ(X, ⊤)) :
    X.divBasicOpen a b * (X.basicOpen b).ι.appTop b = (X.basicOpen b).ι.appTop a := by
  rw [Scheme.divBasicOpen, mul_right_comm,
    Ring.inverse_mul_cancel _ (X.isUnit_ι_appTop_basicOpen b), one_mul]

/-- `a / b` is the unique section over `X_b` whose product with `b` is `a`. -/
lemma Scheme.eq_divBasicOpen {a b : Γ(X, ⊤)} {v : Γ((X.basicOpen b : Scheme.{u}), ⊤)}
    (h : v * (X.basicOpen b).ι.appTop b = (X.basicOpen b).ι.appTop a) :
    v = X.divBasicOpen a b :=
  (X.isUnit_ι_appTop_basicOpen b).mul_right_cancel (h.trans (X.divBasicOpen_mul_self a b).symm)

end BasicOpen

end AlgebraicGeometry
