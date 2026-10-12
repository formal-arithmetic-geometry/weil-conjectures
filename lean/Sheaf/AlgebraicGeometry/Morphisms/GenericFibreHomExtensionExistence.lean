/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
/-!
# Existence of extensions of generic-fibre morphisms

Source: Stacks Project, Tag 0BQM, full faithfulness in the proof.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Existence part of finite étale generic-fibre hom extension.
Source: Stacks Project, Tag 0BQM, full faithfulness argument.
(blueprint: lem-sbc-finite-etale-generic-fibre-hom-extension-existence)

Proof: If C is empty then X and Y are empty, and there is a unique morphism
between them. Otherwise smoothness over the normal base makes C normal (034F).
Its nonempty smooth geometrically connected fibres are geometrically integral
(056T: geometric regularity implies geometric normality and reducedness; a
connected normal scheme over a field is integral). Smoothness is open (01UA),
so the image of C contains the generic point of S. Flatness makes the generic
fibre dense, and its integrality makes C irreducible and hence integral.
The generic point of C belongs to Cη, which is normal integral as well.
Restrict fη to that point. Fullness of finite étale restriction for the normal
integral C (0BQM) extends the resulting morphism to f over C. The pullback
universal property gives a restriction of f to Cη. It and fη agree at the
common generic point; faithfulness for the normal integral Cη (0BQM) makes
them equal. Composing with ψY gives the required compatibility equation.
No connectedness of X or Y is used: 0BQM is a result about all finite étale
covers. Uniqueness of f is not asserted by this lemma. -/
theorem finiteEtale_genericFibre_hom_extension_exists {S C : Scheme.{u}}
    [IsIntegral S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [Smooth c] [GeometricallyConnected c]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    {X Y Xη Yη : Scheme.{u}} (πX : X ⟶ C) (πY : Y ⟶ C)
    [IsFinite πX] [Etale πX] [IsFinite πY] [Etale πY]
    (πXη : Xη ⟶ Cη) (πYη : Yη ⟶ Cη) (ψX : Xη ⟶ X) (ψY : Yη ⟶ Y)
    (hX : IsPullback ψX πXη πX j) (hY : IsPullback ψY πYη πY j)
    (fη : Xη ⟶ Yη) (hfη : fη ≫ πYη = πXη) :
    ∃ f : X ⟶ Y, f ≫ πY = πX ∧ ψX ≫ f = fη ≫ ψY := by sorry
end AlgebraicGeometry.Scheme
