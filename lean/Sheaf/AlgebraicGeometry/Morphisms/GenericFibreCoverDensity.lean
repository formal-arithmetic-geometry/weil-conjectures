/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
/-!
# Reducedness and density for generic restrictions of smooth covers

Source: Stacks Project, Tags 033B and 01UA.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- The generic restriction of an étale cover of a smooth scheme over an integral
base is dominant, and the cover is reduced.

Source: Stacks Project, Tag 033B (smooth algebras over reduced rings),
and Tag 01UA (flat morphisms locally of finite presentation are open).
(blueprint: lem-sbc-finite-etale-generic-fibre-cover-density)

Proof: The composite X → C → S is smooth, hence flat with geometrically reduced
fibres. On affine charts its ring maps are smooth over reduced rings, so the
source rings are reduced by 033B; localizing gives reduced stalks and hence X.
For density take any nonempty open subset of X. The smooth composite maps it
to a nonempty open of S by 01UA, which contains the generic point since S is
integral. A point over that generic point lifts to the generic fibre: the
spectrum of S's generic stalk is the one-point spectrum of its function field,
and the cartesian pullback has a point over every compatible pair of points.
Pasting the two given squares identifies this fibre with Xη. Hence every
nonempty open of X meets the image of ψX. This proves dominance, including
when X is empty, where the empty image is dense. -/
theorem genericFibre_cover_reduced_and_dominant {S C : Scheme.{u}} [IsIntegral S]
    (c : C ⟶ S) [Smooth c]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    {X Xη : Scheme.{u}} (πX : X ⟶ C) [Etale πX]
    (πXη : Xη ⟶ Cη) (ψX : Xη ⟶ X)
    (hX : IsPullback ψX πXη πX j) : IsReduced X ∧ IsDominant ψX := by sorry
end AlgebraicGeometry.Scheme
