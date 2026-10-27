/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.Paper.CompositionModelOrientationDefinitions

/-! # A step of the model orientation descent argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Naturality of the fixed eight-factor source comparison.
Source: thm-pur-composition-coherence.proof.md, Step 2
(blueprint: lem-pur-model-orientation-source-naturality).

Proof: apply naturality of each of the eight normalized factors: shift reassociation,
pullback composition and ordered power splitting, tensor associativity, Tate pullback,
monoidal pullback, the inverse shift reassociation, its pulled-back counterpart, and
the realization unit. Compose their squares in their recorded order. The normalization
uniquely identifies the resulting composites with compositionSourceFixed, and applying
the intrinsic realization functor gives the displayed equality. This works for all
objects and maps, so in particular on finite-Tor constructible objects. -/
theorem model_orientation_source_naturality (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} [Y.Over (Spec (.of P.field.k))]
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    (K L : Scheme.proEtaleDerivedCategory Z P.Ring) (a : K ⟶ L) :
    ((P.compositionShiftedPullback (f ≫ g) (d + e)).map a) ≫
        (P.compositionSourceIdentification f g d e L).hom =
      (P.compositionSourceIdentification f g d e K).hom ≫
        ((P.compositionShiftedPullback g e) ⋙ (P.compositionShiftedPullback f d)).map a :=
  by sorry

end WeilConjectures.PurityFiniteSetting
