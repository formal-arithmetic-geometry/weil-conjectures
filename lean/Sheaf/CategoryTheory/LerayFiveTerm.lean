/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.CategoryTheory.ExactCoupleConvergence
import Mathlib.Algebra.Homology.ExactSequence

/-!
# Five-term exact sequence of a first-quadrant spectral sequence

Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term).

The bottom edge `E₂^{p,0} → Hᵖ` and the left edge `H^q → E₂^{0,q}` are constructed
from the convergence data: the quotient `E₂ → E_∞` (resp. inclusion `E_∞ → E₂`), the
canonical comparison `E_∞^{p,q} ≅ grᵖ H^{p+q}` of weak convergence, and the inclusion
`grᵖ Hᵖ = Fᵖ Hᵖ ⊆ Hᵖ` (resp. the quotient `H^q = F⁰ H^q → gr⁰ H^q`).
-/

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A page system is first-quadrant when all page terms with a negative index vanish.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term). -/
def IsFirstQuadrant (X : BigradedExactCouple C 0) : Prop :=
  ∀ (r : ℕ) (p q : ℤ), p < 0 ∨ q < 0 → IsZero (X.page r p q)

/-- On the bottom row of a first-quadrant spectral sequence every outgoing differential
lands in a zero term, so every finite cycle object, hence the limiting one, is everything.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term). -/
theorem limitCycles_bottom_eq_top (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (hquadrant : X.IsFirstQuadrant) (p : ℤ) : L.Z p 0 = ⊤ := by
  sorry

/-- On the left column of a first-quadrant spectral sequence every incoming differential
starts at a zero term, so every finite boundary object, hence the limiting one, is zero;
thus the limiting boundaries map to zero in the initial page.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term). -/
theorem limitBoundaries_left_comp_eq_zero (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (hquadrant : X.IsFirstQuadrant) (q : ℤ) :
    Subobject.ofLE (L.B 0 q) (L.Z 0 q) (limitBoundary_le_cycle X L 0 q) ≫
      (L.Z 0 q).arrow = 0 := by
  sorry

/-- For a convergent first-quadrant spectral sequence, `F^{p+1} Hⁿ = 0` for `p ≥ n`, so the
inclusion `F^{p+1} Hⁿ ⊆ Fᵖ Hⁿ` is zero: the graded pieces `grᵖ Hⁿ ≅ E_∞^{p,n-p}` vanish for
`p > n`, so the steps from `n+1` on agree, and separation makes them zero.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term). -/
theorem imageFiltration_ofLE_eq_zero (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) (hquadrant : X.IsFirstQuadrant)
    (hconverges : X.ConvergesTo L A) (n p : ℤ) (hp : n ≤ p) :
    Subobject.ofLE ((X.imageFiltration n (A n)).step (p + 1))
      ((X.imageFiltration n (A n)).step p)
      ((X.imageFiltration n (A n)).antitone_step (by omega)) ≫ 𝟙 _ = 0 := by
  sorry

/-- For a convergent first-quadrant spectral sequence, `F⁰ Hⁿ = Hⁿ`: the graded pieces
`grᵖ Hⁿ ≅ E_∞^{p,n-p}` vanish for `p < 0`, so the steps up to `0` agree, and exhaustiveness
makes them everything.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term). -/
theorem imageFiltration_zero_eq_top (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) (hquadrant : X.IsFirstQuadrant)
    (hconverges : X.ConvergesTo L A) (n : ℤ) :
    (X.imageFiltration n (A n)).step 0 = ⊤ := by
  sorry

/-- The canonical comparison `E_∞^{p,q} ≅ grᵖ H^{p+q}` of a weakly convergent couple,
the unique isomorphism compatible with the two canonical maps out of `D^{p,q}`.
Source: blueprint def-sp-convergence; Stacks Tag 012U (blueprint: lem-pqf-leray-five-term). -/
noncomputable def infinityGradedIso (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) (hconverges : X.ConvergesTo L A) (p q : ℤ) :
    X.pageInfinity L p q ≅ (X.imageFiltration (p + q) (A (p + q))).gradedPiece p :=
  Classical.choose (X.weakConvergence_comparison L A hconverges.2.1.1 p q).exists

/-- The bottom edge map `E₂^{p,0} → E_∞^{p,0} ≅ grᵖ Hᵖ = Fᵖ Hᵖ ⊆ Hᵖ` of a convergent
first-quadrant spectral sequence.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term). -/
noncomputable def bottomEdge (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) (hquadrant : X.IsFirstQuadrant)
    (hconverges : X.ConvergesTo L A) (p : ℤ) : X.page 2 p 0 ⟶ (A p).obj :=
  (L.Z p 0).factorThru (𝟙 (X.E p 0))
      (by rw [X.limitCycles_bottom_eq_top L hquadrant p]; exact Subobject.top_factors _) ≫
    cokernel.π (Subobject.ofLE (L.B p 0) (L.Z p 0) (limitBoundary_le_cycle X L p 0)) ≫
    (X.infinityGradedIso L A hconverges p 0).hom ≫
    cokernel.desc _ (𝟙 _)
      (X.imageFiltration_ofLE_eq_zero L A hquadrant hconverges (p + 0) p (by omega)) ≫
    ((X.imageFiltration (p + 0) (A (p + 0))).step p).arrow ≫
    eqToHom (by rw [add_zero])

/-- The left edge map `H^q = F⁰ H^q → gr⁰ H^q ≅ E_∞^{0,q} ⊆ E₂^{0,q}` of a convergent
first-quadrant spectral sequence.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term). -/
noncomputable def leftEdge (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) (hquadrant : X.IsFirstQuadrant)
    (hconverges : X.ConvergesTo L A) (q : ℤ) : (A q).obj ⟶ X.page 2 0 q :=
  eqToHom (by rw [zero_add]) ≫
    ((X.imageFiltration (0 + q) (A (0 + q))).step 0).factorThru (𝟙 _)
      (by rw [X.imageFiltration_zero_eq_top L A hquadrant hconverges];
          exact Subobject.top_factors _) ≫
    cokernel.π _ ≫
    (X.infinityGradedIso L A hconverges 0 q).inv ≫
    cokernel.desc _ (L.Z 0 q).arrow (X.limitBoundaries_left_comp_eq_zero L hquadrant q)

/--
The canonical low-degree edge maps of a convergent first-quadrant spectral sequence
form the five-term exact sequence
`0 → E₂^{1,0} → H¹ → E₂^{0,1} → E₂^{2,0} → H²`: the bottom edge in total degree 1,
the left edge in total degree 1, the page-two differential (the transgression), and the
bottom edge in total degree 2.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term).
Proof: in the first quadrant the entries (1,0), (0,1), (2,0) see only the differential
d₂ : E₂^{0,1} → E₂^{2,0} (d_r out of (1,0), (2,0) and into (0,1) start or end in zero
terms, and d_r for r ≥ 3 out of (0,1) lands in a zero term), so E_∞^{1,0} = E₂^{1,0},
E_∞^{0,1} = ker d₂ and E_∞^{2,0} = coker d₂ (uses def-sp-convergence). Convergence and the
vanishing of grᵖ outside 0..n give F⁰Hⁿ = Hⁿ and F^{n+1}Hⁿ = 0 (def-sp-filtration), so
0 → F¹H¹ = E_∞^{1,0} → H¹ → gr⁰H¹ = E_∞^{0,1} → 0 is exact and F²H² = E_∞^{2,0} ⊆ H².
Hence the degree-1 bottom edge is injective with image F¹H¹ = the kernel of the left edge,
whose image is ker d₂; and the kernel of the degree-2 bottom edge is the kernel of
E₂^{2,0} → E_∞^{2,0}, the image of d₂.
-/
theorem lerayFiveTerm (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (A : ∀ n : ℤ, AlphaColimit X n)
    (hquadrant : X.IsFirstQuadrant)
    (hconverges : X.ConvergesTo L A) :
    (ComposableArrows.mk₅ (0 : (0 : C) ⟶ X.page 2 1 0)
      (X.bottomEdge L A hquadrant hconverges 1)
      (X.leftEdge L A hquadrant hconverges 1)
      (X.pageDifferential 2 0 1)
      (X.bottomEdge L A hquadrant hconverges 2)).Exact := by
  sorry

end CategoryTheory.BigradedExactCouple
