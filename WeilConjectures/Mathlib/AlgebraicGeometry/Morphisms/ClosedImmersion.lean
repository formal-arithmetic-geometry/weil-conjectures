/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Complements on closed immersions

Two unrelated groups of small results.

The first is about **open immersions that are universally closed**. An open immersion whose
underlying map is closed — for instance a proper one — is also a closed immersion, and its
range is a clopen subset of the target. Such a morphism is what is classically called a
*clopen immersion*: it identifies the source with a connected-component union of the target.

The second completes the API of `AlgebraicGeometry.IsClosedImmersion.lift`, the comparison
morphism into a closed subscheme whose ideal sheaf is contained in another. Mathlib supplies
its defining factorization (`lift_fac`) and an invertibility criterion (`isIso_lift`) but not
the two remaining clauses of the universal property: that the lift is itself a closed
immersion when both morphisms are, and that it is the *unique* morphism over the target.
Together with `Scheme.Hom.toImage_imageι` these give the universal property of the
scheme-theoretic image in the form stated in the Nagata blueprint
(`lemma:nagata-scheme-image-universal`).

## Main results

- `AlgebraicGeometry.IsClosedImmersion.of_isOpenImmersion` — an open immersion with closed
  range is a closed immersion;
- `AlgebraicGeometry.Scheme.Hom.isClopen_range` — an open immersion that is universally
  closed has clopen range;
- `AlgebraicGeometry.IsClosedImmersion.isClosedImmersion_lift` — the lift of a closed
  immersion through a closed immersion is a closed immersion;
- `AlgebraicGeometry.IsClosedImmersion.eq_lift` — the lift is the unique morphism over the
  target;
- `AlgebraicGeometry.Scheme.Hom.toImage_lift` — a morphism factoring through a closed
  immersion `z` also factors through `z` after passing to its scheme-theoretic image, with
  `AlgebraicGeometry.Scheme.Hom.ker_le_ker_imageι_comp` supplying its hypothesis.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- An open immersion with closed range is a closed immersion. -/
lemma IsClosedImmersion.of_isOpenImmersion [IsOpenImmersion f] (hf : IsClosed (Set.range f)) :
    IsClosedImmersion f :=
  .of_isPreimmersion f hf

/-- An open immersion that is universally closed is a closed immersion. In particular this
applies to a proper open immersion. -/
lemma IsClosedImmersion.of_isOpenImmersion_of_universallyClosed
    [IsOpenImmersion f] [UniversallyClosed f] :
    IsClosedImmersion f :=
  .of_isOpenImmersion f f.isClosedMap.isClosed_range

/-- The range of an open immersion that is universally closed is clopen. -/
lemma Scheme.Hom.isClopen_range [IsOpenImmersion f] [UniversallyClosed f] :
    IsClopen (Set.range f) :=
  ⟨f.isClosedMap.isClosed_range, f.isOpenEmbedding.isOpen_range⟩

section Lift

variable {Z : Scheme.{u}}

/-- The lift of a closed immersion `g` through a closed immersion `f` is again a closed
immersion: it composes with `f` to give `g`, and `IsClosedImmersion.of_comp_isClosedImmersion`
applies. -/
instance IsClosedImmersion.isClosedImmersion_lift (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g] (H : f.ker ≤ g.ker) :
    IsClosedImmersion (IsClosedImmersion.lift f g H) :=
  have : IsClosedImmersion (IsClosedImmersion.lift f g H ≫ f) := by
    rw [IsClosedImmersion.lift_fac]; infer_instance
  .of_comp_isClosedImmersion _ f

/-- `IsClosedImmersion.lift f g H` is the **unique** morphism composing with `f` to give `g`,
since a closed immersion is a monomorphism. -/
lemma IsClosedImmersion.eq_lift (f : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion f]
    (H : f.ker ≤ g.ker) (c : Y ⟶ X) (hc : c ≫ f = g) :
    c = IsClosedImmersion.lift f g H := by
  rw [← cancel_mono f, hc, IsClosedImmersion.lift_fac]

/-- If `h ≫ z` factors through the closed immersion `z`, then so does its scheme-theoretic
image, compatibly: the comparison `IsClosedImmersion.lift z (h ≫ z).imageι` composed with the
factor `(h ≫ z).toImage` recovers `h`.

This is the third equality of the universal property of the scheme-theoretic image; the other
two are `Scheme.Hom.toImage_imageι` and `IsClosedImmersion.lift_fac`. -/
lemma Scheme.Hom.toImage_lift (h : X ⟶ Z) (z : Z ⟶ Y) [IsClosedImmersion z]
    (H : z.ker ≤ (h ≫ z).imageι.ker) :
    (h ≫ z).toImage ≫ IsClosedImmersion.lift z (h ≫ z).imageι H = h := by
  rw [← cancel_mono z, Category.assoc, IsClosedImmersion.lift_fac, Scheme.Hom.toImage_imageι]

/-- The hypothesis of `AlgebraicGeometry.Scheme.Hom.toImage_lift`: the ideal sheaf of a closed
immersion `z` is contained in that of the scheme-theoretic image of any morphism factoring
through `z`. -/
lemma Scheme.Hom.ker_le_ker_imageι_comp (h : X ⟶ Z) (z : Z ⟶ Y) :
    z.ker ≤ (h ≫ z).imageι.ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact Scheme.Hom.le_ker_comp h z

end Lift

end AlgebraicGeometry
