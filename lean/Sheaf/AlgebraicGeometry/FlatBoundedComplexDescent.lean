/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import Sheaf.AlgebraicGeometry.BaseChangeConventions

/-!
# Descent of bounded finitely presented flat complexes

Source: Stacks Project, `literature/stacks-project/limits.tex`, Lemmas 32.10.2
and 32.10.4 (Tags 01ZR and 05LY) (blueprint: lem-pc-flat-bounded-complex-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A bounded complex of finitely presented modules flat over the limit base descends to a
bounded complex of finitely presented modules flat over some stage.

Source: Stacks Project, `limits.tex`, Lemmas 32.10.2 and 32.10.4, Tags 01ZR
and 05LY (blueprint: lem-pc-flat-bounded-complex-descent).

The ring functor presents the affine inverse system `S_k = Spec R_k` contravariantly; the
limit cone `c` is `S = Spec R` (`IsAffine c.pt`), and `X = X_i ×_{S_i} S`,
`X_j = X_i ×_{S_i} S_j`. The base change of a module on `X_j` to `X` is `moduleBaseChange`
along the cone projection `S → S_j` over `S_i` (def-pc-base-change); the isomorphism of
complexes is a family of termwise isomorphisms commuting with the differentials.

Proof:
1. Apply bounded finite-presentation descent (`lem-pc-fp-complex-descent`, Tag 01ZR) to the
   finitely many terms of `G`, its differentials and their relations: after increasing the
   stage, this gives a bounded complex `H_j` of finitely presented modules on `X_j` whose
   base change to `X` is isomorphic to `G`.
2. Each term `H_j^r` is finitely presented with flat pullback to `X`; eventual flatness
   descent (`lem-pc-flat-module-descent`, Tag 05LY) gives `j_r ≥ j` beyond which its pullback
   is flat over the stage; zero terms are already flat. Directedness gives one stage `j'`
   above the finitely many `j_r`; base-changing `H_j` to `j'` keeps differentials,
   boundedness, finite presentation and the identification with `G`.
3. Rename `j'` as `j` and the base-changed complex as `G_j`. -/
theorem flat_bounded_complex_descent
    {I : Type u} [PartialOrder I] [IsDirectedOrder I]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (G : CochainComplex (pullback f (c.π.app (op i))).Modules ℤ)
    (hG_bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hG_fp : ∀ n : ℤ, (G.X n).IsFinitePresentation)
    (hG_flat : ∀ n : ℤ, (G.X n).IsFlatOver (pullback.snd f (c.π.app (op i)))) :
    ∃ (j : I) (hij : i ≤ j)
      (Gj : CochainComplex (pullback f (Spec.map (R.map (homOfLE hij)))).Modules ℤ),
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Gj.X n)) ∧
      (∀ n : ℤ, (Gj.X n).IsFinitePresentation) ∧
      (∀ n : ℤ, (Gj.X n).IsFlatOver (pullback.snd f (Spec.map (R.map (homOfLE hij))))) ∧
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
