/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.Paper.AdicFiniteReductionData

/-! # Cocycle for normalized derived scalar extension comparisons

Source: Stacks Project, Tags 06YY and 09C2.
(blueprint: lem-sfb-adic-extension-comp-cocycle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

/-- The normalized comparison isomorphisms for three successive scalar extensions
obey the associativity cocycle.  This is the abstract tensor-balancing statement;
the quotient reduction cocycle is its specialization.

Source: Stacks Project, Tags 06YY and 09C2, normalized ordinary tensor balancing.
Proof: evaluate both composites on a K-flat resolution.  The defining
`adicFiniteExtendCompFormula` for each comparison identifies both maps with the
same ordinary tensor reassociation, and uniqueness of the normalized comparison
descends the equality through the derived localization.  Naturality then gives
the displayed equality at every object.
(blueprint: lem-sfb-adic-extension-comp-cocycle). -/
theorem adicFiniteExtensionComp_cocycle
    {D : Type w} [SmallCategory D] (T : GrothendieckTopology D)
    {A B C E : Type w} [CommRing A] [CommRing B] [CommRing C] [CommRing E]
    (f : A →+* B) (g : B →+* C) (h : C →+* E)
    {fg : A →+* C} (efg : fg = g.comp f)
    {gh : B →+* E} (egh : gh = h.comp g)
    {k : A →+* E} (ek₁ : k = h.comp fg) (ek₂ : k = gh.comp f)
    (N : ConstantCompletion.D (constant T A)) :
    (adicFiniteExtension T h).map
          ((adicFiniteExtensionComp T f g fg efg).app N).hom ≫
        ((adicFiniteExtensionComp T fg h k ek₁).app N).hom =
      ((adicFiniteExtensionComp T g h gh egh).app
          ((adicFiniteExtension T f).obj N)).hom ≫
        ((adicFiniteExtensionComp T f gh k ek₂).app N).hom := by
  sorry

end AlgebraicGeometry.Scheme
