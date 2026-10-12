/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Sheaf.CategoryTheory.ImageFiltration
import Sheaf.CategoryTheory.DerivedCoupleExact
import Sheaf.CategoryTheory.HalfPlaneSharpBounds
import Sheaf.CategoryTheory.ExactCouple
import Sheaf.CategoryTheory.Filtration

/-! Canonical finite-page quotient comparisons. -/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Stable finite pages are canonical graded quotients of incoming-alpha images.
Source: Stacks Tags 011R, 011T and 012F, blueprint steps 5--6.
(blueprint: lem-sp-abutment-finite-page-comparison)

Proof: For p>=0 put R=max(p+3,q-a+2),
u=p-R+2 and v=q+R-2. The alpha iterate from (0,p+q) to (u,v) is invertible:
all intervening negative-first-index E terms vanish. Iterating the derived-D
image construction identifies D_(R-2)(u,v) with the incoming p-fold alpha image
under this isomorphism. The induced lift is invertible, and its equation follows
by induction from the given recursive inclusions. The incoming derived alpha
image corresponds to the next filtration step. The target of the derived f map
is zero by the D lower bound. Derived-couple exactness consequently makes g a
cokernel of the next step, inducing psi with the stated quotient equation.
Transport the two adjacent steps along c, giving cStep and the induced graded
isomorphism grc. Stabilization at R identifies cycles and boundaries with L;
the quotient universal property gives stable with its projection equation.
Finally set Theta=grc.symm followed by psi and stable. These arguments also
apply when q<a: both quotient objects vanish, and the same universal properties
supply all maps and equations. -/
theorem abutment_finite_page_comparison
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0) (a : ℤ)
    (hDzero : ∀ p q : ℤ, q < a → IsZero (X.D p q))
    (hEzero : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q))
    (inc : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).D p q ⟶ X.D p q)
    (hinc0 : ∀ p q : ℤ, inc 0 p q = 𝟙 _)
    (hinc : ∀ (r : ℕ) (p q : ℤ), inc (r + 1) p q =
      (X.pageCouple r).derivedDInclusion p q ≫ inc r p q)
    (L : X.LimitSubobjects)
    (hL : ∀ p q : ℤ,
      L.Z p q = X.cycleBoundaryTower.Z
        ((max 2 (max (q - a + 2) (p + 1))).toNat - 2) p q ∧
      L.B p q = X.cycleBoundaryTower.B
        ((max 2 (max (q - a + 2) (p + 1))).toNat - 2) p q)
    (H : ℤ → B) (c : ∀ n : ℤ, X.D 0 n ⟶ H n)
    (hiso : ∀ n : ℤ, IsIso (c n))
    (FA : ∀ n : ℤ, DecreasingFiltration (X.D 0 n))
    (FH : ∀ n : ℤ, DecreasingFiltration (H n))
    (hFA : ∀ n p : ℤ, 0 ≤ p → (FA n).step p =
      imageSubobject (X.incomingAlphaIter p.toNat 0 n))
    (hFH : ∀ n : ℤ, FH n = (FA n).image (c n)) :
        (∀ (p q : ℤ) (hp : 0 ≤ p),
          ∃ (lambda : X.D 0 (p + q) ⟶
              X.D (p - max (p + 3) (q - a + 2) + 2) (q + max (p + 3) (q - a + 2) - 2))
            (lift : ((FA (p + q)).step p : B) ⟶
              (X.pageCouple ((max (p + 3) (q - a + 2)).toNat - 2)).D
                (p - max (p + 3) (q - a + 2) + 2)
                (q + max (p + 3) (q - a + 2) - 2))
            (psi : (FA (p + q)).gradedPiece p ≅
              X.page (max (p + 3) (q - a + 2)).toNat p q)
            (grc : (FA (p + q)).gradedPiece p ≅ (FH (p + q)).gradedPiece p)
            (stable : X.page (max (p + 3) (q - a + 2)).toNat p q ≅
              X.pageInfinity L p q)
            (Theta : (FH (p + q)).gradedPiece p ≅ X.pageInfinity L p q)
            (cStep : ((FA (p + q)).step p : B) ⟶ ((FH (p + q)).step p : B))
            (hZ : X.cycleBoundaryTower.Z
                ((max (p + 3) (q - a + 2)).toNat - 2) p q = L.Z p q),
            IsIso lambda ∧
            lambda = X.alphaIter
              (-(p - max (p + 3) (q - a + 2) + 2)).toNat 0 (p + q) ≫
                eqToHom (by congr 1 <;> omega) ∧
            IsIso lift ∧
            lift ≫ inc ((max (p + 3) (q - a + 2)).toNat - 2)
                (p - max (p + 3) (q - a + 2) + 2)
                (q + max (p + 3) (q - a + 2) - 2) =
              ((FA (p + q)).step p).arrow ≫ lambda ∧
            cStep ≫ ((FH (p + q)).step p).arrow =
              ((FA (p + q)).step p).arrow ≫ c (p + q) ∧
            cStep ≫ cokernel.π (Subobject.ofLE ((FH (p + q)).step (p + 1))
                ((FH (p + q)).step p) ((FH (p + q)).antitone_step (by omega))) =
              cokernel.π (Subobject.ofLE ((FA (p + q)).step (p + 1))
                ((FA (p + q)).step p) ((FA (p + q)).antitone_step (by omega))) ≫ grc.hom ∧
            X.cycleBoundaryTower.projection
                ((max (p + 3) (q - a + 2)).toNat - 2) p q ≫ stable.hom =
              eqToHom (congrArg (fun S : Subobject (X.E p q) ↦ (S : B)) hZ) ≫
                cokernel.π (Subobject.ofLE (L.B p q) (L.Z p q)
                  (X.limitBoundary_le_cycle L p q)) ∧
            cokernel.π (Subobject.ofLE ((FA (p + q)).step (p + 1))
                ((FA (p + q)).step p) ((FA (p + q)).antitone_step (by omega))) ≫
              psi.hom = lift ≫
              (X.pageCouple ((max (p + 3) (q - a + 2)).toNat - 2)).g
                (p - max (p + 3) (q - a + 2) + 2)
                (q + max (p + 3) (q - a + 2) - 2) ≫
              eqToHom (by unfold BigradedExactCouple.page; congr 1 <;> omega) ∧
            Theta = grc.symm ≪≫ psi ≪≫ stable) := by sorry

end CategoryTheory
