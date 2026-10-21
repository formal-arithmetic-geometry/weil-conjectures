/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
module

public import Sheaf.Paper.WeilCompactSupportCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Paper.ConstructibleTruncations
import Sheaf.Paper.IsomorphismDerivedPullback
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.CategoryTheory.ExactCouple
import WeilConjectures.CategoryTheory.DerivedCoupleExact
import WeilConjectures.CategoryTheory.HalfPlaneConvergence
import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.FieldShriekCompositionQcqs
import Sheaf.Paper.FieldShriekLowerBound
import Sheaf.Paper.SfConstructibleHeart
import Sheaf.Paper.SfWeilSheafComplex
import Sheaf.Paper.WeilShriekShiftCompatibility
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-! # Finite compact-support Leray filtrations of constructible Weil sheaves

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-l-dl-general-composition, lem-zl-composition-weight-bound.proof.md,
first paragraph and the subquotient assertion of the second paragraph
(blueprint: lem-zl-compact-support-leray-filtration).

The higher images belong to the existing common-stage Weil heart, with their
canonical actions. Compactifications are universally quantified presentations of
the same operation, identified by zlWeilHigherShriek_compactification_independent.

## Main statements

- `exists_compactSupportLerayFiltration`.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- The compact-support Leray abutment has a finite increasing filtration in the
actual constructible common-stage Weil heart. Each successive quotient is a
quotient of a subobject of one E₂ term in total degree n.

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-l-dl-general-composition, lem-zl-composition-weight-bound.proof.md,
first paragraph and the subquotient assertion of the second paragraph
(blueprint: lem-zl-compact-support-leray-filtration).

Proof, following the seven steps of the DAG node:
1. The underlying common-stage heart is abelian. Frobenius is an exact
   autoequivalence by prop-constructible-truncations and
   lem-weil-isomorphism-derived-pullback. Kernel and cokernel universal properties
   induce the Weil structures; exactness is detected in the underlying heart.
2. Put K = Rh!F and T = Rg! in the underlying common-stage triangulated categories.
   lem-zl-field-shriek-lower-bound supplies bounded constructibility, triangulated
   exactness and preservation of lower bounds. The source is finite type and
   quasi-separated by composition with h; the hypotheses pass to geometric fibres
   by lem-sfb-finite-type-composition-base-change,
   lem-pod-separated-finite-type-base-change and
   lem-weil-pbc-qcqs-morphism-permanence. lem-fix-weil-operations gives the natural
   Weil structures, with no mixedness or weight assumption.
3. Apply T and cohomology to the truncation triangles K_(b-1) → K_b → H^b(K)[-b].
   With D^(a,b) = H^(a+b)(T K_b) and E^(a,b) = H^(a+b)(T(H^b(K)[-b])), the
   inclusion, projection and boundary have bidegrees (-1,1), (0,0) and (2,-1).
   The long exact cohomology sequences give def-sp-exact-couple at type zero.
   The unique truncation comparisons make the triangle Frobenius-equivariant;
   lem-zl-weil-shriek-shift-compatibility includes the boundary comparison.
4. Shift compatibility identifies E₂^(a,b) with R^a g! R^b h!F in the Weil heart.
   Preservation of lower bounds gives first-quadrant vanishing. Iterate by
   lem-sp-derived-couple-exact; every kernel, image and quotient remains equivariant.
5. thm-sp-half-plane-convergence gives the finite decreasing filtration of
   H^n(T τ≤n K), stabilizing on the diagonal by page n+2. The triangle from τ≤n K
   to K has third term τ≥(n+1)K. Lower-bound preservation makes its image have
   zero cohomology in degrees n-1 and n. Its long exact sequence therefore gives
   the canonical Weil isomorphism H^n(T τ≤n K) ≅ H^n(TK).
6. In def-sp-convergence, the stabilized term is Z_(n+2)/B_(n+2), with Z_(n+2)
   a subobject of E₂. Its inclusion is mono and its quotient projection is epi.
   This gives a single subobject of the initial page for each graded piece.
7. lem-zl-field-shriek-composition-qcqs and equivariance from lem-fix-weil-operations
   identify the abutment with R^n(gh)!F. Reverse the decreasing filtration, taking
   m = n+1 and G_j = F^(n+1-j). At j = 1,...,m put a = n+1-j and b = j-1.
   They are nonnegative and sum to n. Compose the cycle quotient with the
   graded-piece isomorphism to get the stated epi. Every arrow is a Weil morphism.
-/
theorem exists_compactSupportLerayFiltration
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ Z₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [QuasiSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) [IsSeparated h₀.left]
    [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    (g₀ : Z₀ ⟶ Y₀) [IsSeparated g₀.left]
    [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    (ch : Compactification h₀.left) (cg : Compactification g₀.left)
    (cgh : Compactification (h₀ ≫ g₀).left)
    (F : zlSourceWeilHeart D l hl Ω h₀) (n : ℕ) :
    ∃ (m : ℕ) (G : Fin (m + 1) → sfCommonStageWeilSheaf D l hl Y₀ Ω)
      (φ : ∀ i : Fin m, G i.castSucc ⟶ G i.succ),
      (∀ i : Fin m, Mono (φ i)) ∧ IsZero (G 0) ∧
      Nonempty (G (Fin.last m) ≅ zlCompositeHigherShriek D l hl Ω h₀ g₀ cgh n F) ∧
      ∀ i : Fin m, ∃ a b : ℕ, a + b = n ∧
        ∃ (S : sfCommonStageWeilSheaf D l hl Y₀ Ω)
          (ι : S ⟶ zlWeilHigherShriek D l hl Ω g₀ cg a
            (zlSourceHigherShriek D l hl Ω h₀ ch b F))
          (π : S ⟶ cokernel (φ i)), Mono ι ∧ Epi π := by
  sorry

end WeilConjectures
