/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.DiagonalProjectiveAction
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
import Sheaf.AlgebraicGeometry.RelativelyVeryAmple
import Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Diagonal projective embeddings for relative split-torus actions

Source: Thomason, Equivariant resolution, linearization, and Hilbert's fourteenth
problem over arbitrary base schemes (1987), Theorem 3.3 and Corollary 3.4(3), p.32;
finite Laurent-coefficient enlargement as detailed in the DAG node.
(blueprint: lem-sfb-relative-torus-diagonal-projective-embedding).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

open DiagonalProjectiveAction

/-- A normal quasi-projective split-torus scheme over a Noetherian ring admits a diagonal
projective equivariant immersion. Empty or disconnected X and a nonreduced base
are allowed; normality is imposed on the local rings of X alone.
Source: Thomason (1987), Theorem 3.3 and Corollary 3.4(3), p.32, with the split-torus
finite-weight enlargement in the node; Stacks Tags 01VR, 01VU, 02NP and 02KH.
(blueprint: lem-sfb-relative-torus-diagonal-projective-embedding).

Proof:
1. Pull back O(1) along the given projective immersion. Quotient geometry
   (lem-trf-projective-bundle-quotient-geometry) makes it relatively very ample
   (def-trf-relatively-very-ample). Apply lem-sfb-relative-normal-line-power-linearization
   to obtain a linearized positive power. Normality of the base is not needed.
2. By lem-trf-relative-ample-very-ample, a sufficiently large multiple of this power
   remains relatively very ample. Tensor its linearization using def-pur-sheaf-tensor-product.
   By lem-sfb-very-ample-affine-finite-sections, finitely many generating sections give an
   immersion. Finite type over the affine base supplies the finite system.
3. Apply lem-sfb-relative-linearized-line-sections-coaction. Expand each selected section
   into its finitely many Laurent coefficients. Coassociativity makes every coefficient
   a weight section, and the counit recovers the old section as their sum. Thus these
   coefficients still generate the line. Append a zero section of weight zero if needed.
   The Laurent monomials are an A-basis, so this works with torsion and nilpotents.
4. Quotient geometry classifies the new quotient by a map into finite projective space.
   Send each old basis vector to the sum of the new basis vectors for its coefficients.
   Composing quotients recovers the old immersion system. Apply
   lem-trf-projective-quotient-comparison to this comparison over the single base open S;
   it says the new classifying map is an immersion, without claiming closedness.
5. Negate the section weights. The normalized coaction gives
   v_j(gx) = g^(-u_j) theta_(g,x)(v_j(x)) as pulled-back sections on every test scheme.
   Quotient classification identifies the common line isomorphism, so the projective
   action is exactly z_j ↦ t^(-u_j) z_j, fixing A. This proves the displayed morphism
   equality and hence its pullback after every base change. The group laws follow on
   generators. Rank zero has only zero weights. The nonempty zero-section list handles
   empty X, even over the zero ring; no connected component is selected. -/
theorem exists_relative_torus_diagonal_projective_embedding
    (A : Type u) [CommRing A] [IsNoetherianRing A] (r : ℕ)
    (X : CategoryTheory.Mod (Over (Spec (.of A))) (torus A r).X)
    [IsSeparated X.X.hom] [LocallyOfFiniteType X.X.hom] [QuasiCompact X.X.hom]
    (hnormal : ∀ p : X.X.left,
      IsDomain (X.X.left.presheaf.stalk p) ∧
        IsIntegrallyClosed (X.X.left.presheaf.stalk p))
    (hquasiprojective : ∃ (N : ℕ) (i : X.X ⟶ space A N), IsImmersion i.left) :
    ∃ (n : ℕ) (w : ULift.{u} (Fin (n + 1)) → Fin r → ℤ)
      (a : ModObj (torus A r).X (space A n)) (j : X.X ⟶ space A n),
      IsDiagonal A r n w a ∧ IsImmersion j.left ∧
        X.mod.smul ≫ j = ((torus A r).X ◁ j) ≫ a.smul := by
  sorry

end AlgebraicGeometry
