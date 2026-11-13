/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import WeilConjectures.FieldTheory.FieldTensorUniqueMinimalPrime
import WeilConjectures.FieldTheory.CommonExtensionFields

/-!
# Testing geometric irreducibility of a subset

## References

* [Stacks Project, Tag 054P](https://stacks.math.columbia.edu/tag/054P)
* [Stacks Project, Tag 020J](https://stacks.math.columbia.edu/tag/020J)
* [Stacks Project, Tag 038I](https://stacks.math.columbia.edu/tag/038I)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

private theorem geometricallyIrreducible_field_specMap {k K : Type u}
    [Field k] [IsSepClosed k] [Field K] [Algebra k K] :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro E _ _
  exact (pullbackSpecIso k K E).hom.homeomorph.irreducibleSpace_iff.mpr
    (IsSepClosed.field_tensor_unique_minimalPrime k K E).2.1

/-- Irreducibility of the inverse image of a subset over a separably closed extension
implies irreducibility of its inverse image over every field extension. -/
theorem isIrreducible_preimage_of_isSepClosed_extension {k Ω : Type u}
    [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (A : Set X)
    (hgeom : IsIrreducible
      ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) ⁻¹' A)) :
    ∀ (E : Type u) (_ : Field E) (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of k)),
      IsIrreducible ((pullback.fst f z) ⁻¹' A) := by
  intro E _ z
  obtain ⟨φ, rfl⟩ := Spec.map_surjective z
  algebraize [φ.hom]
  obtain ⟨M, _, _, i, j, _, _⟩ := Field.exists_common_extension k Ω E
  let g := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let t := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let a := Spec.map (CommRingCat.ofHom i.toRingHom)
  let b := Spec.map (CommRingCat.ofHom j.toRingHom)
  have hab : a ≫ g = b ≫ t := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (i.commutes x).trans (j.commutes x).symm
  let p := pullback.fst (pullback.snd f t) b
  let q := pullback.snd (pullback.snd f t) b
  let r : pullback (pullback.snd f t) b ⟶ pullback f g :=
    pullback.lift (p ≫ pullback.fst f t) (q ≫ a) (by
      calc
        (p ≫ pullback.fst f t) ≫ f = (p ≫ pullback.snd f t) ≫ t := by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
        _ = (q ≫ b) ≫ t := by
          rw [show p ≫ pullback.snd f t = q ≫ b from pullback.condition]
        _ = (q ≫ a) ≫ g := by simp only [Category.assoc, hab])
  have outer : IsPullback (p ≫ pullback.fst f t) q f (a ≫ g) := by
    rw [hab]
    exact (IsPullback.of_hasPullback (pullback.snd f t) b).flip.paste_vert
      (IsPullback.of_hasPullback f t).flip |>.flip
  have top : IsPullback r q (pullback.snd f g) a := by
    apply IsPullback.flip
    apply IsPullback.of_bot (t := (IsPullback.of_hasPullback f g).flip)
    · simpa [r] using outer.flip
    · simp [r]
  have : GeometricallyIrreducible a := by
    algebraize [i.toRingHom]
    exact geometricallyIrreducible_field_specMap
  have : GeometricallyIrreducible r :=
    MorphismProperty.of_isPullback top.flip ‹_›
  have : UniversallyOpen a := by
    algebraize [i.toRingHom]
    infer_instance
  have : UniversallyOpen r := MorphismProperty.of_isPullback top.flip ‹_›
  have hr := r.isIrreducible_preimage r.isOpenMap hgeom
  have heq : r ⁻¹' ((pullback.fst f g) ⁻¹' A) =
      p ⁻¹' ((pullback.fst f t) ⁻¹' A) := by
    ext x
    simp only [Set.mem_preimage]
    have hcomp : r ≫ pullback.fst f g = p ≫ pullback.fst f t := by
      simp [r]
    change (r ≫ pullback.fst f g) x ∈ A ↔ (p ≫ pullback.fst f t) x ∈ A
    rw [hcomp]
  have : Surjective b := ⟨fun x ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have hp : Function.Surjective p := p.surjective
  change IsIrreducible (r ⁻¹' ((pullback.fst f g) ⁻¹' A)) at hr
  rw [heq] at hr
  have himage := hr.image p p.continuous.continuousOn
  rw [Set.image_preimage_eq _ hp] at himage
  exact himage

end AlgebraicGeometry
