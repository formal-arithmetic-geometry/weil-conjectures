/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Extension of scalars along a surjection

Source: Stacks Project, Tag 05WS; the quotient description is the pushout universal
property for commutative rings.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra

/-- Extension of scalars, constructed by pushout in commutative rings. -/
noncomputable def quotientBaseChange {A B : Type u} [CommRing A] [CommRing B]
    (π : A →+* B) : CommAlgCat.{u} A ⥤ CommAlgCat.{u} B :=
  (commAlgCatEquivUnder (CommRingCat.of A)).functor ⋙
    Under.pushout (CommRingCat.ofHom π) ⋙
      (commAlgCatEquivUnder (CommRingCat.of B)).inverse

noncomputable instance {A B : Type u} [CommRing A] [CommRing B] (π : A →+* B) :
    (quotientBaseChange π).IsLeftAdjoint := by
  unfold quotientBaseChange
  infer_instance

/-- Extension of scalars along a surjection has the explicit quotient as its vertex.
Source: Stacks Project, Tag 05WS (the ring pushout calculation).
(blueprint: lem-sbc-surjective-quotient-base-change)

Proof: Give Q = C/IC the B-action by descending A -> Q along π. This descent exists
because ker π = I and every element of I maps to zero in Q. Uniqueness of descent
follows from surjectivity of π. The maps C -> Q and B -> Q form a pushout: for maps
C -> T and B -> T agreeing on A, the map C -> T kills IC, and so factors uniquely
through Q. The factor respects the B-action since this can be checked after π.
The pushout used in quotientBaseChange is uniquely isomorphic to this explicit
pushout. Transport through the equivalence with commutative B-algebras yields the
claimed isomorphism. This argument includes I = 0 and does not assume C is local. -/
theorem quotientBaseChange_obj_iso
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A C]
    (π : A →+* B) (hπ : Function.Surjective π)
    (I : Ideal A) (hker : RingHom.ker π = I) :
    ∃ (_ : Algebra B (C ⧸ I.map (algebraMap A C))),
      Nonempty ((quotientBaseChange π).obj (CommAlgCat.of A C) ≅
        CommAlgCat.of B (C ⧸ I.map (algebraMap A C))) := by
  classical
  let J := I.map (algebraMap A C)
  let q := Ideal.Quotient.mk J
  have hk : RingHom.ker π ≤ RingHom.ker (q.comp (algebraMap A C)) := by
    rw [hker, ← RingHom.comap_ker, Ideal.mk_ker]
    exact Ideal.le_comap_map
  let β : B →+* (C ⧸ J) := π.liftOfSurjective hπ ⟨q.comp (algebraMap A C), hk⟩
  have hβ (a : A) : β (π a) = q (algebraMap A C a) :=
    π.liftOfSurjective_comp_apply hπ _ a
  let : Algebra B (C ⧸ J) := β.toAlgebra
  let s : PushoutCocone (CommRingCat.ofHom (algebraMap A C)) (CommRingCat.ofHom π) :=
    PushoutCocone.mk (CommRingCat.ofHom q) (CommRingCat.ofHom β) (by
      ext a
      exact (hβ a).symm)
  have hs : IsColimit s := PushoutCocone.isColimitAux' s fun t ↦ by
    have hkill : J ≤ RingHom.ker t.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change t.inl.hom (algebraMap A C a) = 0
      have hp : π a = 0 := RingHom.mem_ker.mp (hker.symm ▸ ha)
      have hw := congrArg (fun f ↦ f a) t.condition
      simpa [hp] using hw
    let g := Ideal.Quotient.lift J t.inl.hom hkill
    refine ⟨CommRingCat.ofHom g, ?_, ?_, ?_⟩
    · ext x
      change g (q x) = t.inl.hom x
      exact Ideal.Quotient.lift_mk J t.inl.hom hkill
    · ext b
      obtain ⟨a, rfl⟩ := hπ b
      change g (β (π a)) = t.inr.hom (π a)
      rw [hβ, Ideal.Quotient.lift_mk]
      exact congrArg (fun f ↦ f a) t.condition
    · intro m hm _
      ext x
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
      change m.hom (q c) = g (q c)
      rw [Ideal.Quotient.lift_mk]
      exact congrArg (fun f ↦ f c) hm
  have hp := IsPushout.of_isColimit hs
  let e := hp.isoPushout.symm
  let e' : (Under.pushout (CommRingCat.ofHom π)).obj
      ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj (CommAlgCat.of A C)) ≅
      CommRingCat.mkUnder (CommRingCat.of B) (C ⧸ J) := Under.isoMk e (by
        exact hp.inr_isoPushout_inv)
  exact ⟨β.toAlgebra,
    ⟨(commAlgCatEquivUnder (CommRingCat.of B)).inverse.mapIso e'⟩⟩

end Algebra
