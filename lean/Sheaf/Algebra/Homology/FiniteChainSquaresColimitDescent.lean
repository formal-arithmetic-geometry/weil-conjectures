/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: SHEAF group N4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder

import Sheaf.Algebra.FinitePresentationColimit

/-! # Eventual commutativity of finitely many chain squares

Source: Stacks Project, Tag 09RE, affine case (1), via Tag 05N7, equality clause.
(blueprint: lem-pc-finite-chain-squares-colimit-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Finitely many squares of a fixed graded map commute at a later stage if they
commute after extension to the colimit. No support bound or chain-map condition is
required outside the specified interval.

Source: Stacks Project, Tag 09RE, affine case (1), via Tag 05N7 (3).
Proof: For each integer n in [a,b], compare the two composites from the extended Pⁿ
to the extended Qⁿ⁺¹. Their scalar extensions are equal by hcomm and functoriality.
The two modules at the current stage are finitely presented, since extension of
scalars preserves finite presentation. The equality clause of Tag 05N7 makes this
square commute at a later stage. There are only finitely many n, so directedness
gives one stage j above i where all these equalities hold. Extend every vⁿ to j and
conjugate with the canonical associativity isomorphisms to obtain wⁿ. Naturality of
these isomorphisms identifies the square for w with the extension of the square for
v, hence proves the requested finite list of equations. The associativity coherence
of extension of scalars identifies the further extension of w with that of v in
every degree, including degrees outside [a,b]. This uses no descent of new maps.
For a preorder, use the same finite-presentation relation proof with directed upper
bounds and the filtered-ring elementwise criterion, or transport Tag 05N7 through
the antisymmetrization equivalence and lift its index back. If b < a there are no
equations: choose j = i, with the identity scalar-extension comparisons.
(blueprint: lem-pc-finite-chain-squares-colimit-descent) -/
theorem eventually_commuting_finite_chain_squares
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    (P Q : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (hP : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (P.X n))
    (hQ : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (Q.X n))
    (i : Set.Ici i₀)
    (v : ∀ n : ℤ,
      (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).obj (P.X n) ⟶
        (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).obj (Q.X n))
    (a b : ℤ)
    (hcomm : ∀ n : ℤ, a ≤ n → n ≤ b →
      (ModuleCat.extendScalars (colimit.ι F i.val).hom).map (v n) ≫
        (ModuleCat.extendScalars (colimit.ι F i.val).hom).map
          ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).map
            (Q.d n (n + 1))) =
      (ModuleCat.extendScalars (colimit.ι F i.val).hom).map
          ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).map
            (P.d n (n + 1))) ≫
        (ModuleCat.extendScalars (colimit.ι F i.val).hom).map (v (n + 1))) :
    let e (t : Set.Ici i₀) (C : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ) :=
      eqToIso (congrArg (fun r ↦
        ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj C)
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE t.property)).symm)) ≪≫
      (NatIso.mapHomologicalComplex
        (ModuleCat.extendScalarsComp (F.map (homOfLE t.property)).hom
          (colimit.ι F t.val).hom) (.up ℤ)).app C
    ∃ (j : Set.Ici i₀), i.val ≤ j.val ∧
      ∃ (w : ∀ n : ℤ,
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).obj (P.X n) ⟶
          (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).obj (Q.X n)),
        (∀ n : ℤ, a ≤ n → n ≤ b →
          w n ≫ (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).map
            (Q.d n (n + 1)) =
          (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).map
            (P.d n (n + 1)) ≫ w (n + 1)) ∧
        (∀ n : ℤ, (e j P).hom.f n ≫
          (ModuleCat.extendScalars (colimit.ι F j.val).hom).map (w n) ≫
            (e j Q).inv.f n =
          (e i P).hom.f n ≫
            (ModuleCat.extendScalars (colimit.ι F i.val).hom).map (v n) ≫
              (e i Q).inv.f n) := by sorry

end CochainComplex
