/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.Paper.DirectedColimitBaseChangeElementwise

/-! # Descent of a finite presentation along a directed ring diagram
Source: Stacks Project, Algebra, Tags 00QX and 00R1, the presentation-matrix construction.
(blueprint: lem-weil-pbc-finite-presentation-module-diagram).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

/-- Descend a finite presentation to a cofinal directed restriction of a given ring diagram.
The finite-type assumption permits the stage modules to live in any universe `v`.

Source: Stacks Project, Algebra, Tag 00QX, presentation-matrix paragraph, in its
non-local form used in Tag 00R1.
(blueprint: lem-weil-pbc-finite-presentation-module-diagram)

Proof:
1. Choose a finite free presentation of M. Represent each matrix entry in a stage
   of B using the elementwise ring-colimit theorem, and take a common upper bound i₀.
   Empty matrices cause no problem: choose any index, using nonemptiness.
2. Let J be the upper tail above i₀, and F its inclusion. This tail is nonempty and
   directed. Every original index admits a map to an index in J, so the fully faithful
   inclusion F is final. Restriction therefore preserves the ring colimit.
3. For j in J form the quotient of the finite free B(Fj)-module by the image of the
   lifted presentation matrix. Entrywise ring maps descend to additive quotient maps;
   they respect scalar actions. Functoriality and cocone naturality hold on quotient
   representatives. The classes of the standard basis finitely generate each quotient.
   A finite-type integer algebra is countable; so are its finite powers and quotients.
   Transport each quotient to a small model in Type v, and transport all maps and actions.
4. Tensor right exactness and the finite-product tensor equivalence identify base
   change of these quotients with the corresponding later quotient and with M.
   The equivalences send y tensor x to y times the induced image of x.
5. Apply directedColimitBaseChangeElementwise at i₀ and transport its representative
   and eventual-zero criteria along the equivalences in step 4 and the ring-colimit
   comparison with S. Thus every element of M comes from a stage; two representatives
   with equal images become equal at a common later stage, by applying eventual zero
   to their difference after moving to a common stage. For any additive cocone to X,
   define M → X by the value of a representative. Eventual equality makes this
   independent of the representative. Move two representatives to a common stage to
   prove additivity. It factors every cocone leg, and representatives prove uniqueness.
   This constructs IsColimit directly, even when the index universe u exceeds v;
   it does not require a small-index filtered-colimit instance for AddCommGrpCat.{v}.
   All transports use actual quotient constructions, not arbitrary witnesses of an
   unproved existence theorem.
-/
theorem exists_finitePresentation_module_diagram
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (B : I ⥤ CommRingCat.{u}) (S : Type u) [CommRing S]
    (κ : B ⟶ (Functor.const I).obj (CommRingCat.of S))
    (hκ : Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ)))
    (hfinite : ∀ i, Algebra.FiniteType ℤ (B.obj i))
    (M : Type v) [AddCommGroup M] [Module S M] [Module.FinitePresentation S M] :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (F : J ⥤ I) (_ : F.Final)
      (D : J ⥤ AddCommGrpCat.{v})
      (ν : D ⟶ (Functor.const J).obj (AddCommGrpCat.of M))
      (_ : ∀ j, Module (B.obj (F.obj j)) (D.obj j)),
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)) ∧
      (∀ (i j : J) (h : i ≤ j) (y : B.obj (F.obj i)) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (B.map (F.map (homOfLE h))).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ j (y : B.obj (F.obj j)) (x : D.obj j),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app j)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app (F.obj j))) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app j)) x) ∧
      (∀ j, Module.Finite (B.obj (F.obj j)) (D.obj j)) ∧
      (∀ (i j : J) (h : i ≤ j),
        letI := (B.map (F.map (homOfLE h))).hom.toAlgebra
        ∃ e : B.obj (F.obj j) ⊗[B.obj (F.obj i)] D.obj i ≃ₗ[B.obj (F.obj j)] D.obj j,
          ∀ (y : B.obj (F.obj j)) (x : D.obj i),
            e (y ⊗ₜ[B.obj (F.obj i)] x) = y • (D.map (homOfLE h)).hom x) ∧
      (∀ j,
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app (F.obj j))).toAlgebra
        ∃ e : S ⊗[B.obj (F.obj j)] D.obj j ≃ₗ[S] M,
          ∀ (y : S) (x : D.obj j),
            e (y ⊗ₜ[B.obj (F.obj j)] x) =
              y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app j)) x) := by sorry

end Module
