/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.SplitExists
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.PieceEqualizer

/-!
# Étale splitting of a finite morphism

Let `f : X ⟶ Y` be finite and `y : Spec Ω ⟶ Y` a geometric point with `Ω` algebraically
closed. There is a pointed étale neighbourhood `(V, v)` of `y` such that `V ×_Y X` decomposes
into open and closed pieces indexed by the geometric points of `X` over `y`, each piece finite
over `V`, and the geometric fibre of each piece over `v` a single point
(`AlgebraicGeometry.Scheme.Hom.SplitNbhd.exists_isFinite_and_geometricFiber_piece`).
The decomposition itself is a split neighbourhood
(`AlgebraicGeometry.Scheme.Hom.SplitNbhd`), whose existence is
`AlgebraicGeometry.Scheme.Hom.SplitNbhd.exists_hom`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  {y : Spec (.of Ω) ⟶ Y}

namespace SplitNbhd

variable {f}

/-- A geometric point of `U ×_Y X` lying over the marked point `u` of a pointed étale
neighbourhood `(U, u)` of `y` is one of the points `(u, t)`. -/
lemma exists_eq_basePt (c : Nbhd y) (x : Spec (.of Ω) ⟶ pullback c.1.hom f)
    (hx : x ≫ pullback.fst c.1.hom f = c.2.left) :
    ∃ t : GeometricFiber f y, x = basePt f c t := by
  refine ⟨⟨x ≫ pullback.snd c.1.hom f, ?_⟩, ?_⟩
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc, hx]
    exact CategoryTheory.Over.w c.2
  · exact pullback.hom_ext (by rw [basePt_fst, hx]) (by rw [basePt_snd])

/-- The points `(u, t)` of `U ×_Y X` are pairwise distinct. -/
lemma basePt_injective (c : Nbhd y) : Function.Injective (basePt f c) := fun t t' h ↦
  GeometricFiber.ext (by rw [← basePt_snd f c t, h, basePt_snd])

/-- The geometric points of `U ×_Y X` over the marked point `u` which lie in the `t`-th piece
of a split neighbourhood are exactly the point `(u, t)`. -/
lemma apply_default_mem_piece_iff (s : SplitNbhd f y) (t : GeometricFiber f y)
    (x : Spec (.of Ω) ⟶ pullback s.obj.1.hom f)
    (hx : x ≫ pullback.fst s.obj.1.hom f = s.obj.2.left) :
    x default ∈ s.piece t ↔ x = basePt f s.obj t := by
  obtain ⟨t', rfl⟩ := exists_eq_basePt s.obj x hx
  by_cases h : t' = t
  · subst h
    exact iff_of_true (s.mem t') rfl
  · exact iff_of_false (s.basePt_notMem_piece h) fun h' ↦ h (basePt_injective s.obj h')

/-- The `t`-th piece of a split neighbourhood `(U, u)` is finite over `U`, being an open and
closed subscheme of the finite `U`-scheme `U ×_Y X`. -/
lemma isFinite_piece [IsFinite f] (s : SplitNbhd f y) (t : GeometricFiber f y) :
    IsFinite ((s.piece t).ι ≫ pullback.fst s.obj.1.hom f) := by
  have : IsClosedImmersion (s.piece t).ι := .of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact (s.isClopen t).isClosed)
  infer_instance

variable (f y) in
/-- **Étale splitting of a finite morphism.** Let `f : X ⟶ Y` be finite and `y` a geometric
point of `Y` with algebraically closed field `Ω`. There is a pointed étale neighbourhood
`(V, v)` of `y` and a decomposition of `V ×_Y X` into pairwise disjoint open and closed pieces
covering it, indexed by the geometric points `t` of the finite geometric fibre of `f` over `y`
(so their number is the number of these geometric points), such that each piece is finite over
`V` and its geometric fibre over `v` is the single point `(v, t)`; in particular it is
connected.
(blueprint: `lem-fin-finite-splitting`) -/
theorem exists_isFinite_and_geometricFiber_piece [IsFinite f] [IsAlgClosed Ω] :
    ∃ s : SplitNbhd f y, ∀ t : GeometricFiber f y,
      IsFinite ((s.piece t).ι ≫ pullback.fst s.obj.1.hom f) ∧
        ∀ x : Spec (.of Ω) ⟶ pullback s.obj.1.hom f,
          x ≫ pullback.fst s.obj.1.hom f = s.obj.2.left →
            (x default ∈ s.piece t ↔ x = basePt f s.obj t) := by
  obtain ⟨s, -⟩ := exists_hom f y (IsCofiltered.nonempty (C := Nbhd y)).some
  exact ⟨s, fun t ↦ ⟨s.isFinite_piece t, s.apply_default_mem_piece_iff t⟩⟩

end SplitNbhd

end AlgebraicGeometry.Scheme.Hom
