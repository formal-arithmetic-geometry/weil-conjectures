/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Lifting maps into a tensor colimit

Source: Stacks Project, Algebra, Tag 05LI, proof of (3).
(blueprint: lem-pc-fp-restricted-hom-colimit).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace ModuleCat

/-- A map from a finitely presented stage module into a tensor colimit lifts as
an uncurried map at a later stage. The target module need not be finitely presented.

Source: Stacks Project, Algebra, Tag 05LI, proof of (3),
label algebra-lemma-module-map-property-in-colimit.
(blueprint: lem-pc-fp-restricted-hom-colimit).

Proof: choose finite generators and finitely many generators of their relations
in M. Each generator image in A tensor N is a finite sum of pure tensors, whose
coefficients can be lifted to a common stage j above i. The relation combinations
of these lifted images vanish in the final tensor product. Tensor product
commutes with the directed colimit, so each such relation vanishes at some later
stage. Choose one upper bound for the finitely many relations. The lifted images
then define an Ai-linear map a into Aj tensor N. For any comparison e satisfying
the displayed pure-tensor equation, linearity forces the same comparison on all
pure tensors and their sums, giving the asserted equality. Empty presentations
and the zero target give the zero map. -/
theorem exists_stage_restricted_hom
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat) (i : I) (M N : ModuleCat.{max u v} (F.obj i))
    [Module.FinitePresentation (F.obj i) M]
    (h : M ⟶ (restrictScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj
      ((extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj N)) :
    ∃ (j : I) (hij : i ≤ j),
      let rij := CommRingCat.Hom.hom (F.map (homOfLE hij))
      let rj := CommRingCat.Hom.hom (colimit.ι F j)
      let ri := CommRingCat.Hom.hom (colimit.ι F i)
      ∃ (a : M ⟶ (restrictScalars rij).obj ((extendScalars rij).obj N)),
        ∀ (e : (extendScalars ri).obj N ≅
          (extendScalars rj).obj ((extendScalars rij).obj N)),
          (∀ n : N, e.hom ((1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj i, ri] n) =
            (1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj j, rj]
              ((1 : ↑(F.obj j)) ⊗ₜ[F.obj i, rij] n)) →
          ∀ m : M, e.hom (h m) =
            (1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj j, rj] (a m) := by sorry

end ModuleCat
