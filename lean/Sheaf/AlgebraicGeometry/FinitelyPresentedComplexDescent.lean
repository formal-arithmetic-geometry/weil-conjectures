/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.AlgebraicGeometry.BaseChangeConventions

/-!
# Descent of bounded finitely presented complexes

Source: Stacks Project, Limits of Schemes, Lemma 32.10.2 (Tag 01ZR), in the
Noetherian approximation setting of Lemma 32.10.4 (Tag 05LY)
(blueprint: lem-pc-fp-complex-descent).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A bounded complex of finitely presented quasi-coherent modules on the limit base change
of a finitely presented scheme descends to some later stage.
Source: Stacks Project, Limits of Schemes, Tag 01ZR; Noetherian approximation setting of
Tag 05LY (blueprint: lem-pc-fp-complex-descent).

The functor `R` presents the inverse system of affine schemes contravariantly. Affine
schemes are quasi-compact and quasi-separated, and the transition maps between spectra
are affine. `c` is its limit cone; `IsAffine c.pt` expresses `S = Spec R` without choosing
a coordinate ring. Finite presentation of `f` includes quasi-separatedness as specified
by `def-pc-morphism-conventions`. A cochain complex includes the equations `d ≫ d = 0`.
The isomorphism of complexes is expressed by termwise isomorphisms commuting with all
differentials. Module base change is `moduleBaseChange`, hence tensor pullback, not the
restriction-of-scalars functor `Scheme.Modules.pullback`.

Proof:
1. Boundedness leaves finitely many terms, differentials, and equations that consecutive
   differentials compose to zero; these form finite module-and-map data.
2. Apply part (1) of `lem-pc-fp-module-map-descent` to these terms, choosing a common later
   stage by directedness. Apply part (2) to the differentials between these fixed models,
   transported using their pullback isomorphisms. Choose another common stage, keeping
   one model for each term shared by consecutive differentials.
3. Apply `lem-pc-fp-relation-descent` to the finitely many equations `d ≫ d = 0`. They hold
   after passing to one further stage, since their pullbacks are the zero composites of G.
4. Extend by zero outside the finite interval. The terms and maps form the bounded complex
   H; the termwise pullback isomorphisms commute with the differentials by step 2 and
   therefore give an isomorphism of complexes. -/
theorem exists_finitelyPresented_complex_of_limit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (G : CochainComplex (pullback f (c.π.app (op i))).Modules ℤ)
    (hG_bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hG_fp : ∀ n : ℤ, (G.X n).IsFinitePresentation)
    (hG_qc : ∀ n : ℤ, (G.X n).IsQuasicoherent) :
    ∃ (j : I) (hij : i ≤ j)
      (H : CochainComplex (pullback f (Spec.map (R.map (homOfLE hij)))).Modules ℤ),
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (H.X n)) ∧
      (∀ n : ℤ, (H.X n).IsFinitePresentation) ∧
      (∀ n : ℤ, (H.X n).IsQuasicoherent) ∧
      ∃ e : ∀ n : ℤ,
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (H.X n) ≅ G.X n,
        ∀ n m : ℤ,
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map (H.d n m) ≫
              (e m).hom = (e n).hom ≫ G.d n m := by
  sorry

end AlgebraicGeometry
