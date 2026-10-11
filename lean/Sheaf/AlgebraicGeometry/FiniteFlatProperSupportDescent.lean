/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase

/-!
# Descent of bounded flat complexes with proper support

Source: Stacks Project, Limits of Schemes, Tags 01ZR, 05LY and 081G;
Cohomology of Schemes, Lemma 30.26.7 (Tag 0CYS)
(blueprint: lem-pc-finite-flat-proper-support-descent).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A bounded complex of finitely presented modules flat over the limit base and with
termwise proper support descends with all these properties to a later stage.
Source: Stacks Project, Tags 01ZR, 05LY, 081G and 0CYS
(blueprint: lem-pc-finite-flat-proper-support-descent).

The ring diagram gives the affine inverse system contravariantly. Its limit is the cone
point `c.pt`, with `IsAffine c.pt` expressing `S = Spec R` without fixing coordinates.
Affine stages are quasi-compact and quasi-separated; their transition maps are affine.
Finite presentation of `f` comprises local finite presentation, quasi-compactness and
quasi-separatedness. Finite presentation of each module implies quasi-coherence.
The family of isomorphisms in the conclusion commutes with every differential, hence
is an isomorphism of complexes after tensor base change (`def-pc-base-change`).

Proof:
1. Apply `lem-pc-flat-bounded-complex-descent` (Tags 01ZR and 05LY) to descend the
   bounded complex, its finitely presented flat terms and its differentials to a stage,
   together with an isomorphism of its base change with `G`.
2. Apply `lem-pc-proper-support-descent` (Tag 081G and Lemma 30.26.7, Tag 0CYS) to
   each nonzero term of this chosen complex. Each term is finitely presented and its
   limit pullback has proper support by the given isomorphism and `hG_support`.
3. There are only finitely many nonzero terms, so directedness gives one later stage
   where all terms have proper support. Zero terms have empty, hence proper, support.
   Base-changing the whole complex preserves differentials, boundedness, finite
   presentation, flatness and the identification with `G`. -/
theorem finite_flat_proper_support_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (G : CochainComplex (pullback f (c.π.app (op i))).Modules ℤ)
    (hG_bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hG_fp : ∀ n : ℤ, (G.X n).IsFinitePresentation)
    (hG_flat : ∀ n : ℤ, (G.X n).IsFlatOver (pullback.snd f (c.π.app (op i))))
    (hG_support : ∀ n : ℤ,
      Scheme.Modules.HasSupportProperOver (pullback.snd f (c.π.app (op i))) (G.X n)) :
    ∃ (j : I) (hij : i ≤ j)
      (Gj : CochainComplex (pullback f (Spec.map (R.map (homOfLE hij)))).Modules ℤ),
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Gj.X n)) ∧
      (∀ n : ℤ, (Gj.X n).IsFinitePresentation) ∧
      (∀ n : ℤ, (Gj.X n).IsFlatOver (pullback.snd f (Spec.map (R.map (homOfLE hij))))) ∧
      (∀ n : ℤ, Scheme.Modules.HasSupportProperOver
        (pullback.snd f (Spec.map (R.map (homOfLE hij)))) (Gj.X n)) ∧
      ∃ e : ∀ n : ℤ,
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (Gj.X n) ≅ G.X n,
        ∀ n m : ℤ,
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map (Gj.d n m) ≫
              (e m).hom = (e n).hom ≫ G.d n m := by
  sorry

end AlgebraicGeometry
