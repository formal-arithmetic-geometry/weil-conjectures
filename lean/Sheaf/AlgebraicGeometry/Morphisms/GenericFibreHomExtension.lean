/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Full faithfulness of generic-fibre restriction for finite étale covers

Source: Stacks Project, Tag 0BQM.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Restriction to the generic fibre is fully faithful on finite étale covers of a
smooth family with geometrically connected fibres over an integral normal base.

Source: Stacks Project, Tag 0BQM, proof (full faithfulness over the generic point).
(blueprint: lem-sbc-finite-etale-generic-fibre-hom-extension)

Proof: Smoothness preserves normality, and the smooth geometrically connected fibres
are geometrically integral. If C is empty there is only one morphism between its covers.
Otherwise flatness and openness, together with integrality of the base and its generic
fibre, make C integral. Its generic point belongs to Cη, which is also normal integral.
Restrict fη to the generic point of C. Full faithfulness in 0BQM extends this uniquely
between the finite étale C-schemes X and Y. Restrict that extension back to Cη. Its
restriction to the generic point agrees with fη; faithfulness of 0BQM for Cη makes them
equal. The pullback comparison maps identify this equality with the displayed equation.
The same faithfulness on C proves uniqueness of f. Finite étale covers need not be
connected: the finite étale category in 0BQM includes all their components. -/
theorem finiteEtale_genericFibre_hom_extension {S C : Scheme.{u}}
    [IsIntegral S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [Smooth c] [GeometricallyConnected c]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    {X Y Xη Yη : Scheme.{u}} (πX : X ⟶ C) (πY : Y ⟶ C)
    [IsFinite πX] [Etale πX] [IsFinite πY] [Etale πY]
    (πXη : Xη ⟶ Cη) (πYη : Yη ⟶ Cη) (ψX : Xη ⟶ X) (ψY : Yη ⟶ Y)
    (hX : IsPullback ψX πXη πX j) (hY : IsPullback ψY πYη πY j)
    (fη : Xη ⟶ Yη) (hfη : fη ≫ πYη = πXη) :
    ∃! f : X ⟶ Y, f ≫ πY = πX ∧ ψX ≫ f = fη ≫ ψY := by sorry

end AlgebraicGeometry.Scheme
