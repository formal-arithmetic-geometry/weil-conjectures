/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Equivalence
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraFullyFaithful

/-! # Equivalence transport for invertible endofunctor fixed pairs

## References

* Stacks Project, Categories, Tag 02C3.
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v'

namespace CategoryTheory.Endofunctor.IsoAlgebra

/-- An equivalence commuting with two endofunctors transports their invertible fixed pairs.
The functor is `mapOfNatIso b.symm`, and its Hom bijection is the underlying equivalence's
map restricted to intertwining arrows. Every prescribed carrier isomorphism lifts after
uniquely transporting the structure and its inverse.

Stacks Project, Tag 02C3. -/
theorem fixedPair_equivalence_transport
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ C) (G : D ⥤ D) (J : C ≌ D) (b : F ⋙ J.functor ≅ J.functor ⋙ G) :
    (mapOfNatIso b.symm).IsEquivalence ∧
    (∀ K : IsoAlgebra F,
      ((mapOfNatIso b.symm).obj K).carrier = J.functor.obj K.carrier ∧
      ((mapOfNatIso b.symm).obj K).obj.str =
        b.inv.app K.carrier ≫ J.functor.map K.obj.str) ∧
    (∀ (K K' : IsoAlgebra F) (f : K ⟶ K'),
      ((mapOfNatIso b.symm).map f).hom.f = J.functor.map f.hom.f) ∧
    (∀ K K' : IsoAlgebra F, Function.Bijective
      ((mapOfNatIso b.symm).map : (K ⟶ K') →
        ((mapOfNatIso b.symm).obj K ⟶ (mapOfNatIso b.symm).obj K'))) ∧
    (∀ (K K' : IsoAlgebra F) (u : K.carrier ⟶ K'.carrier),
      ((b.inv.app K.carrier ≫ J.functor.map K.obj.str) ≫ J.functor.map u =
        G.map (J.functor.map u) ≫ b.inv.app K'.carrier ≫ J.functor.map K'.obj.str) ↔
      K.obj.str ≫ u = F.map u ≫ K'.obj.str) ∧
    (∀ (H : IsoAlgebra G) (K : C) (v : J.functor.obj K ≅ H.carrier),
      ∃ θ : F.obj K ≅ K,
        (∀ t : F.obj K ⟶ K,
          J.functor.map t =
            b.hom.app K ≫ G.map v.hom ≫ H.obj.str ≫ v.inv ↔ t = θ.hom) ∧
        (∀ t : K ⟶ F.obj K,
          J.functor.map t =
            v.hom ≫ H.str.inv ≫ G.map v.inv ≫ b.inv.app K ↔ t = θ.inv) ∧
        ∃ e : (mapOfNatIso b.symm).obj (mk K θ) ≅ H,
          e.hom.hom.f = v.hom ∧ e.inv.hom.f = v.inv) := by
  let hJ := J.fullyFaithfulFunctor
  let hT := fullyFaithfulMapOfNatIso b.symm hJ
  have hLift : ∀ (H : IsoAlgebra G) (K : C) (v : J.functor.obj K ≅ H.carrier),
      ∃ θ : F.obj K ≅ K,
        (∀ t : F.obj K ⟶ K,
          J.functor.map t =
            b.hom.app K ≫ G.map v.hom ≫ H.obj.str ≫ v.inv ↔ t = θ.hom) ∧
        (∀ t : K ⟶ F.obj K,
          J.functor.map t =
            v.hom ≫ H.str.inv ≫ G.map v.inv ≫ b.inv.app K ↔ t = θ.inv) ∧
        ∃ e : (mapOfNatIso b.symm).obj (mk K θ) ≅ H,
          e.hom.hom.f = v.hom ∧ e.inv.hom.f = v.inv := by
    intro H K v
    let w : J.functor.obj (F.obj K) ≅ J.functor.obj K :=
      b.app K ≪≫ G.mapIso v ≪≫ H.str ≪≫ v.symm
    let θ : F.obj K ≅ K := hJ.preimageIso w
    have hθ : J.functor.map θ.hom =
        b.hom.app K ≫ G.map v.hom ≫ H.obj.str ≫ v.inv := by
      simp [θ, w]
    have hθinv : J.functor.map θ.inv =
        v.hom ≫ H.str.inv ≫ G.map v.inv ≫ b.inv.app K := by
      simp [θ, w, Category.assoc]
    refine ⟨θ, ?_, ?_, ?_⟩
    · intro t
      rw [← hθ]
      exact ⟨hJ.map_injective, fun h ↦ congrArg J.functor.map h⟩
    · intro t
      rw [← hθinv]
      exact ⟨hJ.map_injective, fun h ↦ congrArg J.functor.map h⟩
    · have hv : G.map v.hom ≫ H.obj.str =
          ((mapOfNatIso b.symm).obj (mk K θ)).obj.str ≫ v.hom := by
        change G.map v.hom ≫ H.obj.str =
          (b.inv.app K ≫ J.functor.map θ.hom) ≫ v.hom
        rw [hθ]
        simp [Category.assoc]
      exact ⟨(Algebra.IsIsoStr G).isoMk (Algebra.isoMk v hv), rfl, rfl⟩
  have hEss : (mapOfNatIso b.symm).EssSurj := ⟨fun H ↦ by
    obtain ⟨θ, _, _, e, _, _⟩ :=
      hLift H (J.inverse.obj H.carrier) (J.counitIso.app H.carrier)
    exact ⟨mk _ θ, ⟨e⟩⟩⟩
  refine ⟨⟨hT.faithful, hT.full, hEss⟩, fun K ↦ ⟨rfl, rfl⟩,
    fun _ _ _ ↦ rfl, hT.map_bijective, ?_, hLift⟩
  intro K K' u
  have hn := b.inv.naturality u
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc (G.map (J.functor.map u)) (b.inv.app K'.carrier), hn]
  simp only [Category.assoc]
  rw [cancel_epi, ← J.functor.map_comp, ← J.functor.map_comp]
  exact ⟨hJ.map_injective, fun h ↦ congrArg J.functor.map h⟩

end CategoryTheory.Endofunctor.IsoAlgebra
