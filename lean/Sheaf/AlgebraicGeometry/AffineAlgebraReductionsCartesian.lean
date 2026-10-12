/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf

import Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec

/-! # Recovering a finite system from compatible affine algebra reductions

Source: Stacks Project, Lemma 09ZT, final sentence, and Morphisms, Lemma 01S8
(blueprint: lem-weil-pbc-affine-algebra-reductions-cartesian).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option autoImplicit false

set_option hygiene false in
local notation "𝒪⁎" g:max => Under.mk (⟨(g).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (g).base).obj (Scheme.sheaf _))

/-- Compatible quotient maps from an affine structure algebra give compatible
cartesian morphisms of the reduction schemes into its realization.
Source: Stacks Project, Lemma 09ZT, final sentence; Morphisms, Lemmas 01S8 and 01SA.

Proof: For each affine U in X, identify Y over U with Spec B(U) using α, and Yn over
j_n inverse U with Spec O_Yn(r_n inverse U). The ring map b_n(U) induces a morphism
to Y over U, because b_n is an O_X-algebra morphism. Naturality of b_n glues these
local morphisms to u_n : Yn to Y. The surjectivity and kernel formulas identify its
source on each chart with Spec of B(U)/ker(j_n.app U)B(U), the base change of Y to Xn.
Thus the square is cartesian, detected on the affine cover. The displayed compatibility
of b_n(U) with gn sharp implies gn followed by u_(n+1) equals u_n on every chart,
hence globally. Empty charts and zero rings give empty spectra and pose no exception.
(blueprint: lem-weil-pbc-affine-algebra-reductions-cartesian). -/
theorem affine_algebra_reductions_cartesian
    {X Y : Scheme.{u}} (Xn Yn : ℕ → Scheme.{u})
    (j : ∀ n, Xn n ⟶ X) [∀ n, IsClosedImmersion (j n)]
    (fnY : ∀ n, Yn n ⟶ Xn n) [∀ n, IsAffineHom (fnY n)]
    (gn : ∀ n, Yn n ⟶ Yn (n + 1))
    (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ j (n + 1)) = fnY n ≫ j n)
    (g : Y ⟶ X) [IsAffineHom g]
    (B : X.CommAlgebraSheaf) (α : B ≅ 𝒪⁎g)
    (b : ∀ n, B ⟶ 𝒪⁎(fnY n ≫ j n))
    (hb : ∀ (n : ℕ) (U : X.Opens), IsAffineOpen U →
      Function.Surjective ((b n).right.hom.app (op U)).hom ∧
      RingHom.ker ((b n).right.hom.app (op U)).hom =
        (RingHom.ker ((j n).app U).hom).map (B.hom.hom.app (op U)).hom)
    (hcompat : ∀ (n : ℕ) (U : X.Opens),
      (b (n + 1)).right.hom.app (op U) ≫
        (gn n).appLE ((fnY (n + 1) ≫ j (n + 1)) ⁻¹ᵁ U)
          ((fnY n ≫ j n) ⁻¹ᵁ U)
          (by rw [← Scheme.Hom.comp_preimage, hw n]) =
        (b n).right.hom.app (op U)) :
    ∃ u : ∀ n, Yn n ⟶ Y,
      (∀ n, IsPullback (u n) (fnY n) g (j n)) ∧
      (∀ n, gn n ≫ u (n + 1) = u n) := by sorry

end AlgebraicGeometry
