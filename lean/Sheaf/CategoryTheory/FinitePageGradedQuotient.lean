/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence

/-!
# The graded quotient induced by derived g

Source: blueprint thm-sp-truncation-e2, steps 5--6; Stacks Tags 011R, 011S and 0AMJ.
(blueprint: lem-sp-finite-page-graded-quotient)
-/

@[expose] public section

universe u₂ v₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Once the image lift is fixed, derived g induces the finite-page graded isomorphism.
Source: blueprint thm-sp-truncation-e2, proof steps 5--6; Stacks Tags 011R, 011S and 0AMJ.
(blueprint: lem-sp-finite-page-graded-quotient)

Proof: Write R=max(p+3,q-a+2), r=R-2, u=p-r and v=q+r. The inclusion inc r is
monomorphic and its image is the incoming r-fold alpha image, by induction on its
specified recurrence and pageCouple_image. The next inclusion inc (r+1) factors
as the incoming derived-alpha image inclusion followed by inc r. Splitting the
incoming (r+1)-fold alpha iterate at first index zero identifies its image with
the image of F(p+1).arrow followed by lambda. Since lift followed by inc r is
F(p).arrow followed by lambda and both inc r and lambda are monomorphic, this
identifies the inclusion F(p+1) into F(p), under lift, with the incoming derived
alpha image. Exactness of the r-th couple identifies that image with ker(g).
The target of derived f after g is zero: derived D(p+2,q-1) embeds into D(p+2,q-1)
as the incoming r-fold image with source D(p+R,q-R+1). This source is zero since
R>=q-a+2. Thus f=0 and exactness at derived E makes g epimorphic. Composing
with lift and the index transport preserves epimorphicity and the indicated
kernel. The abelian cokernel property gives the unique isomorphism from
F(p)/F(p+1) to page R(p,q) whose composite with the projection is lift followed
by g and index transport. At p=0 the argument uses the identity incoming iterate;
when q<a its epimorphic quotient has zero target, with the same universal property.
No choice of an arbitrary isomorphism is used: its hom is fixed by the epimorphic
cokernel projection and the displayed equation. -/
theorem finitePage_graded_quotient
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0) (a : ℤ)
    (hDzero : ∀ p q : ℤ, q < a → IsZero (X.D p q))
    (inc : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).D p q ⟶ X.D p q)
    (hinc0 : ∀ p q : ℤ, inc 0 p q = 𝟙 _)
    (hinc : ∀ (r : ℕ) (p q : ℤ), inc (r + 1) p q =
      (X.pageCouple r).derivedDInclusion p q ≫ inc r p q)
    (p q : ℤ) (hp : 0 ≤ p)
    (F : DecreasingFiltration (X.D 0 (p + q)))
    (hF : ∀ i : ℤ, 0 ≤ i → F.step i =
      imageSubobject (X.incomingAlphaIter i.toNat 0 (p + q)))
    (lambda : X.D 0 (p + q) ⟶
      X.D (p - max (p + 3) (q - a + 2) + 2) (q + max (p + 3) (q - a + 2) - 2))
    (hlambda : lambda = X.alphaIter
      (-(p - max (p + 3) (q - a + 2) + 2)).toNat 0 (p + q) ≫
        eqToHom (by congr 1 <;> omega))
    [IsIso lambda]
    (lift : (F.step p : B) ⟶
        (X.pageCouple ((max (p + 3) (q - a + 2)).toNat - 2)).D
          (p - max (p + 3) (q - a + 2) + 2)
          (q + max (p + 3) (q - a + 2) - 2))
    (hlift : IsIso lift)
    (hliftinc : lift ≫ inc ((max (p + 3) (q - a + 2)).toNat - 2)
      (p - max (p + 3) (q - a + 2) + 2)
      (q + max (p + 3) (q - a + 2) - 2) = (F.step p).arrow ≫ lambda) :
    ∃ (psi : F.gradedPiece p ≅ X.page (max (p + 3) (q - a + 2)).toNat p q),
      cokernel.π (Subobject.ofLE (F.step (p + 1)) (F.step p)
          (F.antitone_step (by omega))) ≫ psi.hom = lift ≫
        (X.pageCouple ((max (p + 3) (q - a + 2)).toNat - 2)).g
          (p - max (p + 3) (q - a + 2) + 2)
          (q + max (p + 3) (q - a + 2) - 2) ≫
        eqToHom (by unfold BigradedExactCouple.page; congr 1 <;> omega) := by sorry

end CategoryTheory
