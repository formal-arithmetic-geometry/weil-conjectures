/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Generator.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Flatness of the sheafified free presheaf

Source: literature/stacks-project/sites-modules.tex, Lemma 03EV (blueprint:
lem-weil-pbc-free-sheaf-flat).

## Main statement

The sheaf associated to the free presheaf on a representable, with a flat
coefficient object, is flat.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace CategoryTheory.GrothendieckTopology

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A]

omit [MonoidalPreadditive A] in
/--
The sheafification of the free presheaf on a representable with flat
coefficient object is flat, expressed as preservation of finite limits by
left tensoring. This is Lemma 03EV of the Stacks Project, generalized to
Grothendieck abelian symmetric monoidal closed coefficient categories.
Source: Stacks Project, Modules on Sites, Lemmas 03EV, 03ES, 03ET and 0GMW;
the coefficient-category generalization is described in the module docstring of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`
(blueprint: lem-weil-pbc-free-sheaf-flat).

Proof: each value `Q(V) = ∐_{V ⟶ X} P` of the free presheaf `Q = Presheaf.freeYoneda X P`
is a coproduct of copies of the flat object `P`, hence flat
(`CategoryTheory.ObjectProperty.flat_coproduct`, blueprint `lem-weil-pbc-flat-coproduct`), and
the sheafification of a presheaf with flat values is flat
(`CategoryTheory.GrothendieckTopology.flat_presheafToSheaf_obj`, which rests on the exactness
and strong monoidality of sheafification, blueprint `lem-weil-pbc-sheaf-tensor-closed`).
-/
@[stacks 03EV]
lemma free_sheaf_flat (P : A) (hP : PreservesFiniteLimits (tensorLeft P))
    (X : C) :
    PreservesFiniteLimits (tensorLeft (Sheaf.freeYoneda J X P)) := by
  have hP' : ObjectProperty.flat P := (ObjectProperty.flat_iff_preservesFiniteLimits P).2 hP
  refine (flat_presheafToSheaf_obj A J _ fun V ↦ ?_).1.1
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{_, _, u + 1} A
    (ULift.{u + 1} (V.unop ⟶ X))
  exact ObjectProperty.prop_of_iso _
    (Sigma.whiskerEquiv (f := fun _ : ULift.{u + 1} (V.unop ⟶ X) ↦ P) Equiv.ulift
      fun _ ↦ Iso.refl P)
    (ObjectProperty.flat_coproduct _ fun _ ↦ hP')

end CategoryTheory.GrothendieckTopology
