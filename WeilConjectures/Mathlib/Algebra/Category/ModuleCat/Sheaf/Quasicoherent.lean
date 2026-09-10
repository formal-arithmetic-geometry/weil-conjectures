/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-!
# Coherent sheaves of modules

A sheaf of modules over a sheaf of rings on a site is *coherent* if it is quasi-coherent and of
finite type: `SheafOfModules.IsCoherent`.

## Design note

Over an arbitrary ringed site, the standard notion of coherence is stronger than the one used
here: a sheaf of modules `M` is coherent in the sense of [Stacks, 01BV] if it is of finite type
and if, for every object `U` and every finite family of sections of `M` over `U`, the kernel of
the induced map from a finite free module onto the subsheaf they generate is again of finite
type. That definition is the correct one in general — it is exactly what makes coherent sheaves
an abelian subcategory without any hypothesis on the base — but it is *not* implied by
quasi-coherence together with finite type, and it does not even hold for the structure sheaf
itself over a general base.

The two notions agree over a locally Noetherian scheme, and it is only there that this project
uses them: everything in sight is a scheme of finite type over a field. We therefore take the
weaker condition as the definition, and let the Noetherian hypotheses appear on the individual
statements that need them (stability under kernels, finite generation of the module of sections
over an affine, …) rather than baking a site-level Noetherian condition into the class.
Concretely, this means:

* `IsCoherent` is by construction stable under everything `IsQuasicoherent` and `IsFiniteType`
  are stable under, and `IsCoherent M` unfolds to `M.IsQuasicoherent ∧ M.IsFiniteType`
  (`SheafOfModules.isCoherent_iff`);
* over a locally Noetherian scheme, `IsCoherent` is the intended notion of coherence, and over
  a Noetherian affine scheme it says exactly that the module of sections is finitely generated;
* over a base which is not locally Noetherian, `IsCoherent` should be read as
  "quasi-coherent of finite type", and none of the theorems about coherent sheaves that need
  the Noetherian hypothesis are available for it.

## References

* [Stacks, 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks, 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

universe w u v₁ v₂ u₁ u₂

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

namespace SheafOfModules

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf of modules is coherent if it is quasi-coherent and of finite type.

Over a locally Noetherian scheme this is the usual notion of coherence; over a general base it
is weaker than the notion of [Stacks, 01BV]. See the module docstring for the design rationale. -/
class IsCoherent (M : SheafOfModules.{u} R) : Prop extends M.IsQuasicoherent, M.IsFiniteType

lemma isCoherent_iff (M : SheafOfModules.{u} R) :
    M.IsCoherent ↔ M.IsQuasicoherent ∧ M.IsFiniteType :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ⟨⟩⟩

variable (R) in
@[inherit_doc IsCoherent]
abbrev isCoherent : ObjectProperty (SheafOfModules.{u} R) :=
  IsCoherent

instance (M : (isCoherent R).FullSubcategory) : M.obj.IsCoherent :=
  M.property

instance (M : SheafOfModules.{u} R) [M.IsFinitePresentation] : M.IsCoherent where

section

variable [HasBinaryProducts C] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]

instance : (isCoherent R).IsClosedUnderIsomorphisms where
  of_iso e _ :=
    have := (isQuasicoherent R).prop_of_iso e inferInstance
    have := isFiniteType_of_iso e
    ⟨⟩

end

end SheafOfModules
