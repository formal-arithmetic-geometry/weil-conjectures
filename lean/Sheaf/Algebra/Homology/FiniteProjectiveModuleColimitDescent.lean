/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.Algebra.FinitePresentationColimit

/-! # Descent of one finite projective module

Source: Stacks Project, More on Algebra, Tag 0BC7, first paragraph of the proof.
(blueprint: lem-pc-finite-projective-module-colimit-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A single finite projective module over a directed ring colimit has a finite projective model.
Source: Stacks Project, More on Algebra, Tag 0BC7, first paragraph of the proof,
and Algebra, Tags 05N7 and 00NX.
(blueprint: lem-pc-finite-projective-module-colimit-descent).

Proof: Replace the directed preorder by its antisymmetrization, choosing representatives.
The resulting equivalence of indexing categories transports the diagram and its colimit.
A finite projective module is finitely presented. Apply the object clause of finite-presentation
colimit descent to obtain a finitely presented stage model. Choose a split surjection from a
finite free module onto the original module, using finite generation and projectivity. The
finite free module has the evident stage model with the same finite basis. Apply the map
clause to the section and retraction and pass to a common later stage. The canonical iterated
base-change isomorphisms identify these base-changed maps with the original splitting maps.
Their composite becomes the identity over the colimit. Apply the equality clause to make
this identity hold at a further stage. The stage model is then a summand of the finite free
module, hence finite and projective. Its colimit base change is the original module, by the
iterated base-change isomorphism. Finally lift the stage back along the equivalence of indexing
categories and transport the module isomorphism along the induced colimit ring isomorphism.
For a zero module one may take the zero stage module; for a singleton indexing category the
construction agrees with transport along the canonical colimit isomorphism. -/
theorem exists_finite_projective_module_model_of_directed_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (X : ModuleCat.{u} (colimit F : CommRingCat.{u}))
    (hfinite : Module.Finite (colimit F : CommRingCat.{u}) X)
    (hprojective : Module.Projective (colimit F : CommRingCat.{u}) X) :
    ∃ (i : I) (M : ModuleCat.{u} (F.obj i)),
      Module.Finite (F.obj i) M ∧ Module.Projective (F.obj i) M ∧
      Nonempty ((extendScalars (colimit.ι F i).hom).obj M ≅ X) := by sorry

end ModuleCat
