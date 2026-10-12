/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Eventual smoothness of a finitely presented model over affine transition limits

Source: Stacks Project, Tag 0C0C.
(blueprint: lem-sbc-affine-limit-smooth-stage)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- A finitely presented model whose limit base change is smooth becomes smooth later.

Source: Stacks Project, Tag 0C0C, with Situation 081D; affine descent via 0CAQ
and comparison via 01ZM(2)-(3).
Proof: restrict the diagram to Over i, whose limit is still S. Cover X_i by finitely
many affine opens and their inverse images in P by finitely many affine opens.
These covers pull back to every later stage and to the limit. On each chart the
limit algebra is the filtered colimit of the stage algebras. Smooth algebra descent
(0CAQ) gives a smooth finitely presented algebra over a later base chart. Descend
the comparison isomorphism to the original chart model and its inverse by 01ZM(2),
then their inverse equations by 01ZM(3). The original chart model is therefore
smooth at a later stage. Choose one common stage for the finitely many charts;
smoothness is preserved by further base change and is local on source and target.
Consequently the whole later model is smooth. Empty charts use the zero algebra
and require no additional nonemptiness assumption.
(blueprint: lem-sbc-affine-limit-smooth-stage) -/
theorem exists_smooth_stage_of_affine_limit {I : Type u} [SmallCategory I]
    [IsCofiltered I] {S C : Scheme.{u}}
    (X : I ⥤ Scheme.{u}) (α : (Functor.const I).obj S ⟶ X)
    (hα : IsLimit (Cone.mk S α))
    (hXa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f))
    (hN : ∀ i, IsNoetherian (X.obj i))
    (hqs : ∀ i, QuasiSeparatedSpace (X.obj i))
    {i : I} {P : Scheme.{u}} (p : P ⟶ X.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (c : C ⟶ S) [Smooth c] (a : C ⟶ P)
    (H : IsPullback a c p (α.app i)) :
    ∃ j : Over i, Smooth (pullback.snd p (X.map j.hom)) := by sorry

end AlgebraicGeometry.Scheme
