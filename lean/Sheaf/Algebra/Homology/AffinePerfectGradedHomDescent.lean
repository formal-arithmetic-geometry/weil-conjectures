/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Module.FinitePresentation

import Sheaf.Algebra.FinitePresentationColimit

/-! # AffinePerfectGradedHomDescent

Source: Stacks Project, Tags 09RE and 05N7.
(blueprint: lem-pc-affine-perfect-graded-hom-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Descend a degree-minus-one graded family without imposing chain-map or homotopy equations.

Source: Stacks Project, Tag 09RE, affine case (1), finite number of finitely
presented source terms; Tag 05N7 (2).
Proof: In the finite interval supporting E₀, descend each component s(m,m-1)
using finite-presentation map descent. The source and target terms are finitely
presented by hypothesis. Directedness gives one common stage above i.
Transport all components to that stage by scalar-extension associativity, and
put zero outside the interval. Components of a different degree are not required.
The canonical comparison isomorphisms in map descent are uniquely determined
by their value on tensors 1 ⊗ x, and hence are precisely extendScalarsComp,
after the equality hc identifies the ring homomorphisms. Thus the transported
components have exactly the stated equality with s. On zero source terms this
is automatic, since scalar extension preserves zero objects. No relation with
any differential or prescribed chain map is asserted. For a preorder take the
quotient by mutual comparability, choose representatives, and use the equivalent
partial-order index category in finite-presentation descent. Ring maps between
equivalent indices are inverse isomorphisms. Transport back and take an upper
bound with i. An empty support interval gives the zero family at any stage above i.
(blueprint: lem-pc-affine-perfect-graded-hom-descent) -/
theorem affine_perfect_gradedHom_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E₀.X n))
    (hEfp : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (E₀.X n))
    (hKfp : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (K₀.X n))
    (i : Set.Ici i₀)
    (s : ∀ m n : ℤ, (ComplexShape.up ℤ).Rel n m →
      ((((ModuleCat.extendScalars (colimit.ι F i₀).hom).mapHomologicalComplex
      (.up ℤ)).obj E₀).X m ⟶ (((ModuleCat.extendScalars (colimit.ι F i₀).hom).mapHomologicalComplex
      (.up ℤ)).obj K₀).X n)) :
    ∃ (j : Set.Ici i₀) (hij : i ≤ j)
      (t : ∀ m n : ℤ, (ComplexShape.up ℤ).Rel n m →
        ((((ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj E₀).X m ⟶
          (((ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj K₀).X n)),
      let hc := congrArg CommRingCat.Hom.hom
        (colimit.w F (homOfLE j.property)).symm
      let L := eqToHom (congrArg (fun r ↦
          ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj E₀) hc) ≫
        (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp
          (F.map (homOfLE j.property)).hom (colimit.ι F j.val).hom) (.up ℤ)).hom.app E₀
      let R := (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp
          (F.map (homOfLE j.property)).hom (colimit.ι F j.val).hom) (.up ℤ)).inv.app K₀ ≫
        eqToHom (congrArg (fun r ↦
          ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj K₀) hc.symm)
      ∀ m n : ℤ, ∀ hmn : (ComplexShape.up ℤ).Rel n m,
        L.f m ≫ (ModuleCat.extendScalars (colimit.ι F j.val).hom).map (t m n hmn) ≫
          R.f n = s m n hmn := by sorry

end CochainComplex
