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

/-! # Descent of bounded families of graded maps

Source: Stacks Project, Tag 09RE, affine case (1), and Tag 05N7, map clause.
(blueprint: lem-pc-bounded-graded-map-colimit-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Descend the components of a graded map, without imposing chain-map equations.

Source: Stacks Project, Tag 09RE, affine case (1), via Tag 05N7 (2).
Proof: Only degrees in [a,b] need nonzero components. Each source and target term is
finitely presented, so the map clause of finite-presentation descent lifts each of these
finitely many components to a stage above i₀. Directedness gives a common upper stage;
extend each lifted map to that stage and conjugate by scalar-extension associativity.
The canonical comparison sends 1 tensor x to 1 tensor (1 tensor x), so its conjugation
agrees with the comparison in Tag 05N7. Outside the interval the source is zero, and
scalar extension preserves zero objects; put zero there. This also proves the required
comparison in those degrees. For a preorder, the presentation-matrix proof of Tag 05N7
uses only finitely many coefficients, relations and directed upper bounds, so works
without antisymmetry, using the filtered-ring elementwise criterion. Equivalently,
pass to the antisymmetrization, transport along its category equivalence, and lift the
resulting index to an upper bound with i₀. If b < a all source terms are zero, and the
zero family at i₀ suffices.
(blueprint: lem-pc-bounded-graded-map-colimit-descent) -/
theorem exists_bounded_graded_map_of_directed_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    (P Q : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (a b : ℤ) (hzero : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hP : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (P.X n))
    (hQ : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (Q.X n))
    (f : ∀ n : ℤ,
      (ModuleCat.extendScalars (colimit.ι F i₀).hom).obj (P.X n) ⟶
        (ModuleCat.extendScalars (colimit.ι F i₀).hom).obj (Q.X n)) :
    let e (t : Set.Ici i₀) (C : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ) :=
      eqToIso (congrArg (fun r ↦
        ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj C)
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE t.property)).symm)) ≪≫
      (NatIso.mapHomologicalComplex
        (ModuleCat.extendScalarsComp (F.map (homOfLE t.property)).hom
          (colimit.ι F t.val).hom) (.up ℤ)).app C
    ∃ (i : Set.Ici i₀)
      (v : ∀ n : ℤ,
        (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).obj (P.X n) ⟶
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).obj (Q.X n)),
      ∀ n : ℤ, (e i P).hom.f n ≫
        (ModuleCat.extendScalars (colimit.ι F i.val).hom).map (v n) ≫
          (e i Q).inv.f n = f n := by sorry

end CochainComplex
