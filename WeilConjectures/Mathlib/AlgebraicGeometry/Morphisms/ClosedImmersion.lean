/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Complements on closed immersions

Three unrelated groups of small results.

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
(`lemma:nagata-scheme-image-universal`), and its packaging as a minimality statement:
the scheme-theoretic image is the smallest closed subscheme of the target through which
the morphism factors.

The third is an **affine descent criterion**: a morphism into a fibre product of affine
schemes is a closed immersion as soon as the target ring is generated, as a ring, by the
images of the two structure maps.  It is stated ring-theoretically, in terms of a
`Subring.closure`, so that it can be applied without providing algebra instances.

## Main results

- `AlgebraicGeometry.IsClosedImmersion.of_isOpenImmersion` — an open immersion with closed
  range is a closed immersion;
- `AlgebraicGeometry.Scheme.Hom.isClopen_range` — an open immersion that is universally
  closed has clopen range;
- `AlgebraicGeometry.isClosedImmersion_lift` — the lift of a closed immersion through a
  closed immersion is a closed immersion;
- `AlgebraicGeometry.IsClosedImmersion.eq_lift` — the lift is the unique morphism over the
  target;
- `AlgebraicGeometry.Scheme.Hom.toImage_lift` — a morphism factoring through a closed
  immersion `z` also factors through `z` after passing to its scheme-theoretic image, with
  `AlgebraicGeometry.Scheme.Hom.ker_le_ker_imageι_comp` supplying its hypothesis;
- `AlgebraicGeometry.Scheme.Hom.ker_le_ker_iff_existsUnique_fac` — a closed subscheme
  contains the scheme-theoretic image of `g` if and only if `g` factors through it, and
  then uniquely;
- `AlgebraicGeometry.isClosedImmersion_pullbackLift_spec` — a morphism
  `Spec W ⟶ Spec S ×_{Spec R} Spec T` is a closed immersion if `W` is generated as a ring
  by the images of `S` and `T`.
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
instance isClosedImmersion_lift (f : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion f]
    [IsClosedImmersion g] (H : f.ker ≤ g.ker) :
    IsClosedImmersion (IsClosedImmersion.lift f g H) :=
  have : IsClosedImmersion (IsClosedImmersion.lift f g H ≫ f) := by
    rw [IsClosedImmersion.lift_fac]
    infer_instance
  .of_comp_isClosedImmersion _ f

/-- `IsClosedImmersion.lift f g H` is the **unique** morphism composing with `f` to give `g`,
since a closed immersion is a monomorphism. -/
lemma IsClosedImmersion.eq_lift (f : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion f]
    (H : f.ker ≤ g.ker) (c : Y ⟶ X) (hc : c ≫ f = g) :
    c = IsClosedImmersion.lift f g H := by
  rw [← cancel_mono f, hc, IsClosedImmersion.lift_fac]

/-- If `g` factors as `h ≫ z` through the closed immersion `z`, then so does its
scheme-theoretic image, compatibly: the comparison `IsClosedImmersion.lift z g.imageι`
composed with the factor `g.toImage` recovers `h`.

This is the third equality of the universal property of the scheme-theoretic image; the other
two are `Scheme.Hom.toImage_imageι` and `IsClosedImmersion.lift_fac`. The factorization is
taken as a propositional hypothesis rather than by forcing the target to be syntactically
`h ≫ z`, so that the lemma rewrites at an arbitrary `g`. -/
lemma Scheme.Hom.toImage_lift {g : X ⟶ Y} (h : X ⟶ Z) (z : Z ⟶ Y) [IsClosedImmersion z]
    (w : h ≫ z = g) (H : z.ker ≤ g.imageι.ker) :
    g.toImage ≫ IsClosedImmersion.lift z g.imageι H = h := by
  rw [← cancel_mono z, Category.assoc, IsClosedImmersion.lift_fac, Scheme.Hom.toImage_imageι, w]

/-- The hypothesis of `AlgebraicGeometry.Scheme.Hom.toImage_lift`: the ideal sheaf of a closed
immersion `z` is contained in that of the scheme-theoretic image of any morphism factoring
through `z`. -/
lemma Scheme.Hom.ker_le_ker_imageι_comp (h : X ⟶ Z) (z : Z ⟶ Y) :
    z.ker ≤ (h ≫ z).imageι.ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact Scheme.Hom.le_ker_comp h z

/-- The scheme-theoretic image is the smallest closed subscheme of `Y` through which `g`
factors: a closed subscheme `z : Z ⟶ Y` contains the scheme-theoretic image of `g` (i.e.
`z.ker ≤ g.ker`) if and only if `g` factors through `z`, and the factorization is then
unique because `z` is a monomorphism. -/
theorem Scheme.Hom.ker_le_ker_iff_existsUnique_fac (g : X ⟶ Y) (z : Z ⟶ Y)
    [IsClosedImmersion z] : z.ker ≤ g.ker ↔ ∃! h : X ⟶ Z, h ≫ z = g := by
  refine ⟨fun H ↦ ?_, fun ⟨h, w, _⟩ ↦ ?_⟩
  · have hz : z.ker ≤ g.imageι.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
    have hfac : (g.toImage ≫ IsClosedImmersion.lift z g.imageι hz) ≫ z = g := by simp
    exact ⟨_, hfac, fun h' hh' ↦ by rw [← cancel_mono z, hh', hfac]⟩
  · rw [← w]
    exact Scheme.Hom.le_ker_comp h z

end Lift

section AffineDescent

open Limits

/-- **Affine descent of closed immersions along a pushout of rings**: if a ring `W`
receives maps `u : S →+* W` and `v : T →+* W` agreeing on `R` and is generated as a ring by
their images, then the induced morphism `Spec W ⟶ Spec S ×_{Spec R} Spec T` is a closed
immersion. -/
lemma isClosedImmersion_pullbackLift_spec {R S T W : Type u} [CommRing R] [CommRing S]
    [CommRing T] [CommRing W] (f : R →+* S) (g : R →+* T) (u : S →+* W) (v : T →+* W)
    (hcomm : u.comp f = v.comp g)
    (hgen : Subring.closure (Set.range u ∪ Set.range v) = ⊤) :
    IsClosedImmersion
      (pullback.lift (Spec.map (CommRingCat.ofHom u)) (Spec.map (CommRingCat.ofHom v))
        (by rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← CommRingCat.ofHom_comp, hcomm]) :
        Spec (.of W) ⟶
          pullback (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom g))) := by
  have hw : CommRingCat.ofHom f ≫ CommRingCat.ofHom u =
      CommRingCat.ofHom g ≫ CommRingCat.ofHom v := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomm]
  set d : pushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) ⟶ CommRingCat.of W :=
    pushout.desc (CommRingCat.ofHom u) (CommRingCat.ofHom v) hw with hd
  have hsurj : Function.Surjective d.hom := by
    rw [← RingHom.range_eq_top, eq_top_iff, ← hgen, Subring.closure_le]
    rintro z (⟨b, rfl⟩ | ⟨c, rfl⟩)
    · refine ⟨(pushout.inl (CommRingCat.ofHom f) (CommRingCat.ofHom g)).hom b, ?_⟩
      rw [hd, ← CommRingCat.comp_apply, pushout.inl_desc]
      rfl
    · refine ⟨(pushout.inr (CommRingCat.ofHom f) (CommRingCat.ofHom g)).hom c, ?_⟩
      rw [hd, ← CommRingCat.comp_apply, pushout.inr_desc]
      rfl
  have hsq := isPullback_SpecMap_pushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
  have heq : (pullback.lift (Spec.map (CommRingCat.ofHom u)) (Spec.map (CommRingCat.ofHom v))
      (by rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, hcomm]) :
      Spec (.of W) ⟶
        pullback (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom g))) =
      Spec.map d ≫ hsq.isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst, ← Spec.map_comp,
        hd, pushout.inl_desc]
    · rw [pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, ← Spec.map_comp,
        hd, pushout.inr_desc]
  rw [heq]
  have : IsClosedImmersion (Spec.map d) := IsClosedImmersion.spec_of_surjective d hsurj
  infer_instance

end AffineDescent

end AlgebraicGeometry
