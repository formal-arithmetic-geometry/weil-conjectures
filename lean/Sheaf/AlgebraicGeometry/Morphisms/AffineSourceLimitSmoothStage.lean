/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.RingTheory.SmoothAlgebraFilteredColimitDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Eventual smoothness for an affine source model

Source: Stacks Project, Tag 0C0C, affine-local reduction using Tags 0CAQ and 01ZM.
(blueprint: lem-sbc-affine-source-limit-smooth-stage)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Eventual smoothness for a single affine source chart.

Source: Stacks Project, Tag 0C0C, with Situation 081D and Tags 0CAQ, 01ZM(2)-(3).
Proof: cover the Noetherian base stage by finitely many affine opens. Their inverse
images in the affine source are quasi-compact opens, so take finite affine covers
of these inverse images. Restrict the diagram to Over i and then to each base open.
Affine transitions imply affine limit projections, so every pulled-back chart is
affine. Global sections of each limit chart are the filtered colimit of the stage
chart rings. The assumed smoothness makes the limit chart algebra smooth. Tag 0CAQ
provides a smooth finitely presented model over a later base chart. Both this model
and the original chart are finitely presented over the common base. Descend the
comparison isomorphism and its inverse by 01ZM(2), and their two inverse identities
by 01ZM(3). Thus the original chart is smooth at a later stage. Take one common
refinement for the finitely many charts. Smoothness is stable under base change
and local on source and target, hence the affine source model is smooth there.
Empty sources and charts are allowed: the zero algebra is smooth, and the finite
common-refinement argument also works for an empty cover.
(blueprint: lem-sbc-affine-source-limit-smooth-stage) -/
theorem exists_smooth_stage_of_affine_source_limit {I : Type u} [SmallCategory I]
    [IsCofiltered I] {S : Scheme.{u}}
    (X : I ⥤ Scheme.{u}) (α : (Functor.const I).obj S ⟶ X)
    (hα : IsLimit (Cone.mk S α))
    (hXa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f))
    (hN : ∀ i, IsNoetherian (X.obj i))
    (hqs : ∀ i, QuasiSeparatedSpace (X.obj i))
    {i : I} {P : Scheme.{u}} [IsAffine P] (p : P ⟶ X.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [Smooth (pullback.snd p (α.app i))] :
    ∃ j : Over i, Smooth (pullback.snd p (X.map j.hom)) := by sorry

end AlgebraicGeometry.Scheme
