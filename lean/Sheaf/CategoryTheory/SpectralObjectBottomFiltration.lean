/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
public import Sheaf.CategoryTheory.Filtration

/-! # Bottom edge factorization for a first-quadrant spectral object

Source: Stacks Project, Tags 012K, 015J and 015N; image filtration of the abutment.
(blueprint: lem-sc-spectral-object-bottom-filtration)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits ComposableArrows

namespace CategoryTheory

/-- Compare the graded pieces and bottom edge of the image filtration from a first-quadrant
spectral object, after any specified isomorphism of its abutment. The filtration
and its bounds are constructed separately; this theorem supplies only the
graded comparisons and their compatibility with the iterated bottom projection.

Source: Stacks Project, Tags 012K, 015J and 015N.
(blueprint: lem-sc-spectral-object-bottom-filtration)

Proof: Let T^p H^n be the image of H^n(bottom,n+1-p) -> H^n(bottom,top),
transported by h. First-quadrant vanishing gives T^0 = top and T^(n+1) = bottom.
The short exact sequence of opcycles identifies its successive cokernels with
stable spectral-object terms; the spectral-object page comparison identifies these
with page p+q+2. For r > max(p,q+1) the two adjacent differentials vanish, so
both cycle inclusion and homology projection are isomorphisms. Iterating them
identifies every later page with page p+q+2. On the bottom row the outgoing
map vanishes for every r >= 2. The cycle inclusion is therefore invertible,
which uniquely determines t by ht; induction from hb2 and hbt determines b.
At (p,0), the opcycles projection followed by inclusion into the abutment is
exactly the spectral-object bottomEdge. Successive page comparisons identify
this projection with b at page p+2. The denominator T^(p+1) H^p is zero,
so its cokernel projection is invertible. Define k as g^(-1) followed by that
inverse projection. The quotient identity follows by cancellation, and the
opcycles identity gives the displayed factorization. All isomorphisms and
filtration steps are transported through h, so the assertion holds for every
specified abutment isomorphism. In degree zero b is the identity and T^1=0.
-/
theorem exists_spectral_object_bottom_filtration
    {C : Type u} [Category.{v} C] [Abelian C]
    (Y : Abelian.SpectralObject C EInt) [Y.IsFirstQuadrant]
    (H : ℕ → C)
    (h : ∀ n : ℕ, (Y.H n).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≅ H n)
    (T : ∀ n : ℕ, DecreasingFiltration (H n))
    (hT : ∀ (n : ℕ) (i : ℤ), (T n).step i =
      (Subobject.«exists» (h n).hom).obj (Y.imageFiltration n ((n : ℤ) + 1 - i)))
    (t : ∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
      (Y.E₂SpectralSequenceNat.page r hr).X (p, 0) ⟶
        (Y.E₂SpectralSequenceNat.page (r + 1) (by omega)).X (p, 0))
    (ht : ∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
      (Y.E₂SpectralSequenceNat.page r hr).iCycles (p, 0) ≫ t p r hr =
        (Y.E₂SpectralSequenceNat.page r hr).homologyπ (p, 0) ≫
          (Y.E₂SpectralSequenceNat.iso r (r + 1) (p, 0) rfl hr).hom)
    (b : ∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
      (Y.E₂SpectralSequenceNat.page 2).X (p, 0) ⟶
        (Y.E₂SpectralSequenceNat.page r hr).X (p, 0))
    (hb2 : ∀ p, b p 2 (by omega) = 𝟙 _)
    (hbt : ∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
      b p (r + 1) (by omega) = b p r hr ≫ t p r hr) :
    ∃ g : ∀ p q : ℕ, (T (p + q)).gradedPiece p ≅
        Y.E₂SpectralSequenceNat.pageInfinity (p, q),
      ∃ k : ∀ p : ℕ, Y.E₂SpectralSequenceNat.pageInfinity (p, 0) ≅
          ((T p).step p : C),
        (∀ p, cokernel.π (Subobject.ofLE ((T p).step (p + 1))
          ((T p).step p) ((T p).antitone_step (by omega))) ≫
            (g p 0).hom = (k p).inv) ∧
        (∀ p : ℕ, (Y.E₂SpectralSequenceNatPageTwoXIso p 0).hom ≫
          Y.bottomEdge p ≫ (h p).hom =
            b p (p + 2) (by omega) ≫ (k p).hom ≫ ((T p).step p).arrow) := by sorry

end CategoryTheory
