/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedLiftArrowComplex

/-! # Normalizing the closed-lift augmentation to actual arrows

Source: Steps 1--2 of `lem-sp-proetale-closed-lift-kernel-overlap-presentation`.
(blueprint: lem-sp-proetale-closed-lift-arrow-normalization).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Test relations and actual-arrow summands generate the full augmentation source.
This assertion concerns the source of the augmentation, not its relation kernel;
it does not identify the relations among the actual arrows.

Source: Steps 1--2 of `lem-sp-proetale-closed-lift-kernel-overlap-presentation`.
(blueprint: lem-sp-proetale-closed-lift-arrow-normalization).

Proof: fix an indexed summand A[U] and its map f to A[P]. Local surjectivity
of the free-presheaf sheafification unit represents f on a covering of U by
finite linear combinations of arrows to P. Refine by affine charts. Since U
is affine, its quasi-compactness bounds this by finitely many charts. Their
disjoint union V is a pro-etale covering of U. The induced map of representable
set sheaves is epic, so projectivity of evaluation on U lifts the identity to
a section U to V. Pulling back the finitely many summands gives a finite clopen
partition of U. On each piece W, f is an actual finite linear combination of
arrows. Each W is affine, and specialization into the closed fibre restricts
to W because W is clopen. Evaluation on W preserves epimorphisms: sheaf sections
on U are the product of sections on W and its clopen complement; for any epi,
base change it over the complemented subterminal W and adjoin the identity over
the complement, apply projectivity on U, and restrict the resulting lift.
Thus W is a closed-lift test, including when W is empty.

For each W subtract from the original summand inclusion, restricted along W to U,
the corresponding linear combination of actual-arrow summand inclusions. Its
composite with the augmentation is zero. The kernel lift is a map from A[W]
to ker(e), so it indexes a summand in d. Consequently each original generator
lies locally in the image of [d followed by kernel inclusion, b]. To check
this last map is epic, take two morphisms out of its target that agree after
it. Precomposing with any original summand and then restricting to the clopen
cover gives equal morphisms by the displayed subtraction equation. Free Yoneda
and separatedness give equality on the whole summand; the coproduct universal
property gives equality on the source. This includes the zero ring and empty
objects and uses no properness hypothesis. -/
theorem closedLiftArrow_normalization (A : Type u) [CommRing A]
    {X Z : Scheme.{u}} (z : Z ⟶ X) (P : X.ProEt) :
    let Q := (ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P
    let e := closedLiftGeneratorAugmentation A z Q
    let d := closedLiftGeneratorAugmentation A z (kernel e.hom)
    Epi (biprod.desc (d.hom ≫ kernel.ι e.hom) (closedLiftArrowAugmentation A z P)) := by
  sorry

end AlgebraicGeometry.Scheme
