/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Finitely presented modules over a directed ring colimit

Source: Stacks Project, Algebra, Lemma 10.127.6 (Tag 05N7), used in Limits,
Lemma 32.10.2 (Tag 01ZR), affine case
(blueprint: lem-pc-fp-module-map-descent-affine).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace ModuleCat

/-- Over a directed colimit of commutative rings, finitely presented modules,
maps between their fixed base changes, and equalities of maps descend to a stage.

For objects, lift a finite presentation matrix coefficientwise. For a map, lift
the images of finitely many generators and witnesses for their relations; the
elementwise colimit criterion makes those relations hold at a later stage.
For equality, compare maps on finite generators, lift witnesses for their
differences in a presentation of the target, and pass to a common later stage.
These three steps use `lem-pc-filtered-colimit-commrings-elementwise`.
Source: Stacks Project, Algebra, Lemma 10.127.6 (Tag 05N7)
(blueprint: lem-pc-fp-module-map-descent-affine). -/
theorem finitePresentation_descent_directedColimit
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat) :
    (∀ (N : ModuleCat (colimit F : CommRingCat)),
      Module.FinitePresentation (colimit F : CommRingCat) N →
      ∃ (i : I) (M : ModuleCat (F.obj i)), Module.FinitePresentation (F.obj i) M ∧
        Nonempty ((extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj M ≅ N)) ∧
    (∀ (i : I) (M N : ModuleCat (F.obj i)),
      Module.FinitePresentation (F.obj i) M →
      Module.FinitePresentation (F.obj i) N →
      ∀ (f : (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj M ⟶
          (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj N),
        ∃ (j : I) (hij : i ≤ j),
          let rij := CommRingCat.Hom.hom (F.map (homOfLE hij))
          let rj := CommRingCat.Hom.hom (colimit.ι F j)
          let ri := CommRingCat.Hom.hom (colimit.ι F i)
          ∃ (g : (extendScalars rij).obj M ⟶ (extendScalars rij).obj N)
            (eM : (extendScalars ri).obj M ≅
              (extendScalars rj).obj ((extendScalars rij).obj M))
            (eN : (extendScalars ri).obj N ≅
              (extendScalars rj).obj ((extendScalars rij).obj N)),
            (∀ m : M,
              eM.hom ((1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj i, ri] m) =
                (1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj j, rj]
                  ((1 : ↑(F.obj j)) ⊗ₜ[F.obj i, rij] m)) ∧
            (∀ n : N,
              eN.hom ((1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj i, ri] n) =
                (1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj j, rj]
                  ((1 : ↑(F.obj j)) ⊗ₜ[F.obj i, rij] n)) ∧
            f ≫ eN.hom = eM.hom ≫ (extendScalars rj).map g) ∧
    (∀ (i : I) (M N : ModuleCat (F.obj i)),
      Module.FinitePresentation (F.obj i) M →
      Module.FinitePresentation (F.obj i) N →
      ∀ (f g : M ⟶ N),
        (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).map f =
          (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).map g →
        ∃ (j : I) (hij : i ≤ j),
          (extendScalars (CommRingCat.Hom.hom (F.map (homOfLE hij)))).map f =
            (extendScalars (CommRingCat.Hom.hom (F.map (homOfLE hij)))).map g) :=
  sorry

end ModuleCat
