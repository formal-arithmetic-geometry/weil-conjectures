/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Sites.Torsor

/-! # Right torsors under arbitrary pro-étale group sheaves

Source: Stacks Project, Tag 03AH, with right translation in place of left translation
(blueprint: def-sfb-proetale-right-group-torsor).
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory Opposite
namespace CategoryTheory.Sheaf

/-- A right torsor for an arbitrary, possibly noncommutative pro-étale group sheaf.
Simple transitivity is imposed wherever a section exists, and local sections are
required by the covering sieve. Source: Stacks 03AH
(blueprint: def-sfb-proetale-right-group-torsor). -/
structure ProEtaleRightTorsor (X : AlgebraicGeometry.Scheme.{u})
    (H : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) GrpCat.{v}) where
  sheaf : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) (Type w)
  act (U : X.ProEtᵒᵖ) : sheaf.obj.obj U → H.obj.obj U → sheaf.obj.obj U
  act_one (U : X.ProEtᵒᵖ) (s : sheaf.obj.obj U) : act U s 1 = s
  act_mul (U : X.ProEtᵒᵖ) (s : sheaf.obj.obj U) (g h : H.obj.obj U) :
    act U (act U s g) h = act U s (g * h)
  natural {U V : X.ProEtᵒᵖ} (f : U ⟶ V) (s : sheaf.obj.obj U) (g : H.obj.obj U) :
    sheaf.obj.map f (act U s g) = act V (sheaf.obj.map f s) ((H.obj.map f).hom g)
  bijective (U : X.ProEtᵒᵖ) (s : sheaf.obj.obj U) : Function.Bijective (act U s)
  locally_nonempty (U : X.ProEt) :
    nonemptySieve sheaf.obj U ∈ AlgebraicGeometry.Scheme.ProEt.topology X U

/-- The unique right translation coefficient taking one section to another. This is
an actual inverse of the given bijective action, with no postponed existence choice.
Source: Stacks 03AH (blueprint: def-sfb-proetale-right-group-torsor). -/
noncomputable def ProEtaleRightTorsor.transition {X : AlgebraicGeometry.Scheme.{u}}
    {H : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) GrpCat.{v}}
    (P : ProEtaleRightTorsor.{u, v, w} X H) {U : X.ProEtᵒᵖ}
    (s t : P.sheaf.obj.obj U) : H.obj.obj U :=
  (Equiv.ofBijective (P.act U s) (P.bijective U s)).symm t

end CategoryTheory.Sheaf
