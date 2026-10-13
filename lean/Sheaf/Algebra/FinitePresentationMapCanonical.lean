/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: SHEAF group W3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder

/-! # Canonical descent of a single finitely presented module map

Source: Stacks Project, Algebra Tag 05N7 (2), used in Perfect Tag 09RE (1).
(blueprint: lem-pc-fp-module-map-canonical-preorder)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A single map over a directed ring colimit lifts at a stage above the initial one,
with the canonical scalar-extension comparison.

Source: Stacks Project, Algebra Tag 05N7 (2); Perfect Tag 09RE, affine case (1).
Proof: Choose finite generators and finite relations for M and N. Express the images
of the generators of M as finite linear combinations of the generators of N over the
colimit ring. Lift all these coefficients to a common stage above i₀, using the
filtered-ring elementwise criterion. Each relation of M maps to zero in N over the
colimit, so express it as a finite combination of the defining relations of N and
lift those coefficients too. The resulting finitely many coefficient equations
hold at a common later stage by the same criterion. They define a map at that stage.
The two canonical comparison maps send 1 tensor x to 1 tensor (1 tensor x), so the
lift has the asserted conjugated extension, by linearity and generation by pure
tensors. Only directedness and finite lists of coefficients and relations enter,
so this argument works for a preorder, including mutually comparable distinct indices.
If M or N is zero the same presentation argument applies, and the unique zero map
also gives the result.
(blueprint: lem-pc-fp-module-map-canonical-preorder) -/
theorem finitePresentation_map_directedColimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I) (M N : ModuleCat.{u} (F.obj i₀))
    (hM : Module.FinitePresentation (F.obj i₀) M)
    (hN : Module.FinitePresentation (F.obj i₀) N)
    (f : (extendScalars (colimit.ι F i₀).hom).obj M ⟶
      (extendScalars (colimit.ι F i₀).hom).obj N) :
    let e (i : Set.Ici i₀) (X : ModuleCat.{u} (F.obj i₀)) :=
      eqToIso (congrArg (fun r ↦ (extendScalars r).obj X)
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm)) ≪≫
      (extendScalarsComp (F.map (homOfLE i.property)).hom (colimit.ι F i.val).hom).app X
    ∃ i : Set.Ici i₀,
      ∃ g : (extendScalars (F.map (homOfLE i.property)).hom).obj M ⟶
        (extendScalars (F.map (homOfLE i.property)).hom).obj N,
        (e i M).hom ≫ (extendScalars (colimit.ι F i.val).hom).map g ≫ (e i N).inv = f := by
  sorry

end ModuleCat
