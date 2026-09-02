/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.PieceRing
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.PieceEqualizer

/-!
# Pieces of split neighbourhoods are cofinal among the étale neighbourhoods of a point

Let `f : X ⟶ Y` be finite, `y : Spec Ω ⟶ Y` a geometric point with `Ω` algebraically closed
and `t` a geometric point of `X` over `y`. Every pointed étale neighbourhood `(V, v)` of `t`
receives a morphism from the `t`-th piece of some split neighbourhood of `y`
(`AlgebraicGeometry.Scheme.Hom.SplitNeighborhood.exists_pieceFunctor_obj_hom`): starting from
a split neighbourhood `Spec A'` given by an affine chart, the piece is `Spec B` for the finite
`A'`-algebra `B = F ⧸ (1 - e t)` with a unique point over `φ'`, the étale `Spec B`-scheme
`V ×_X Spec B` is `Spec C` for an étale `B`-algebra `C` near the point `(v, (u, t))`
(`AlgebraicGeometry.Etale.exists_algebraMap_hom_of_point`), and the ring-theoretic section
result `Algebra.exists_etale_algHom_tensor_comp_eq` produces an étale `A'`-algebra `A''` and a
`B`-algebra map `C ⟶ A'' ⊗[A'] B`, that is, a morphism from the `t`-th piece
`Spec (A'' ⊗[A'] B)` of the split neighbourhood pulled back to `Spec A''` to `V`.

Together with `AlgebraicGeometry.Scheme.Hom.SplitNeighborhood.exists_pieceFunctor_map_comp_eq`
this proves that the piece functor
`AlgebraicGeometry.Scheme.Hom.SplitNeighborhood.pieceFunctor` is initial
(`AlgebraicGeometry.Scheme.Hom.SplitNeighborhood.initial_pieceFunctor`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct RingHom

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] affineAlgebra Chart.algebra

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {y : Spec (.of Ω) ⟶ Y}

namespace SplitNeighborhood

/-- **Every pointed étale neighbourhood of `t` receives a morphism from a piece of a split
neighbourhood of `y`.** -/
theorem exists_pieceFunctor_obj_hom (t : GeometricFiber f y) (d : EtaleNeighborhood t.1) :
    ∃ s : SplitNeighborhood f y, Nonempty ((pieceFunctor t).obj s ⟶ d) := by
  classical
  obtain ⟨Y₀, hY₀, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y default) (U := ⊤) trivial
  obtain ⟨c₀⟩ := IsCofiltered.nonempty (C := EtaleNeighborhood y)
  obtain ⟨ch⟩ := Chart.nonempty y hy c₀
  have := ch.finite_fiber f hY₀
  have := Fintype.ofFinite (PointsOver ch.point (ch.Fiber f))
  obtain ⟨A', _, _, _, φ', hφ', e, he, hval⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_forall_tensor_eq (A := ch.ring)
      (B := ch.Fiber f) ch.point
  -- the étale neighbourhood `V` of `t`, pulled back to the piece `Spec B`, and its point
  set V : X.Etale := d.1
  set ζ := ch.pieceSpecToX f hY₀ hy A' φ' hφ' e t with hζ
  obtain ⟨pt, hpt₁, hpt₂⟩ : ∃ pt : Spec (.of Ω) ⟶ pullback V.hom ζ,
      pt ≫ pullback.fst _ _ = d.2.left ∧
        pt ≫ pullback.snd _ _ = ch.pieceSpecPt f hY₀ hy A' φ' hφ' e hval t :=
    ⟨pullback.lift d.2.left (ch.pieceSpecPt f hY₀ hy A' φ' hφ' e hval t) (by
      rw [hζ, Chart.pieceSpecPt_comp_pieceSpecToX]
      exact CategoryTheory.Over.w d.2), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  clear_value ζ
  -- the ring data: `B` finite over `A'` with a unique point, `C` étale over `B`
  let B := ch.PieceRing f hY₀ hy A' e t
  have : Module.Finite A' B := ch.finite_pieceRing f hY₀ hy A' e t
  obtain ⟨C, _, _, _, j, ψ₀, hj, hψ₀⟩ :=
    Etale.exists_algebraMap_hom_of_point (B := B) (pullback.snd V.hom ζ) pt
  let _ : Algebra A' C := ((algebraMap B C).comp (algebraMap A' B)).toAlgebra
  have : IsScalarTower A' B C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have := ch.subsingleton_pointsOver_pieceRing f hY₀ hy A' φ' hφ' e hval t
  -- the point of `C` given by `(v, (u, t))` lies over the point of `B`
  have hψ : ψ₀.comp (algebraMap B C) = (ch.piecePoint f hY₀ hy A' φ' hφ' e hval t).1 := by
    have key : Spec.map (CommRingCat.ofHom (ψ₀.comp (algebraMap B C))) =
        Spec.map (CommRingCat.ofHom (ch.piecePoint f hY₀ hy A' φ' hφ' e hval t).1) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, ← hj, ← Category.assoc, hψ₀, hpt₂]
      rfl
    have := congrArg CommRingCat.Hom.hom (Spec.map_injective key)
    simpa using this
  obtain ⟨ψ, hψ₁⟩ : ∃ ψ : PointsOver φ' C, ψ.1 = ψ₀ :=
    ⟨⟨ψ₀, by
      rw [RingHom.algebraMap_toAlgebra, ← RingHom.comp_assoc, hψ]
      exact (ch.piecePoint f hY₀ hy A' φ' hφ' e hval t).2⟩, rfl⟩
  obtain ⟨A'', _, _, _, φ'', hφ'', h, hh₁, hh₂⟩ :=
    Algebra.exists_etale_algHom_tensor_comp_eq (A := A') (B := B) (C := C) φ' ψ
  -- the split neighbourhood `Spec A''` and its `t`-th piece `Spec (A'' ⊗ B)`
  let s := (ch.split f hY₀ hy A' φ' hφ' e he hval).pullbackDec
    (ch.refineTwiceMap hY₀ A' φ' hφ' A'' φ'' hφ'')
  have := ch.isOpenImmersion_pieceEmb f hY₀ hy A' φ' hφ' e he t A'' φ'' hφ''
  obtain ⟨iso, hiso₁, hiso₂⟩ : ∃ iso : Spec (.of (ch.PieceRingBaseChange f hY₀ hy A' e t A'')) ≅
      (s.piece t).toScheme,
      iso.inv ≫ ch.pieceEmb f hY₀ hy A' φ' hφ' e t A'' φ'' hφ'' = (s.piece t).ι ∧
      iso.hom ≫ (s.piece t).ι = ch.pieceEmb f hY₀ hy A' φ' hφ' e t A'' φ'' hφ'' :=
    ⟨IsOpenImmersion.isoOfRangeEq (ch.pieceEmb f hY₀ hy A' φ' hφ' e t A'' φ'' hφ'') (s.piece t).ι
      (by
        rw [Scheme.Opens.range_ι]
        exact congrArg SetLike.coe
          (ch.opensRange_pieceEmb f hY₀ hy A' φ' hφ' e he hval t A'' φ'' hφ'')),
      IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩
  -- the morphism from the piece to `V`
  let ρ : (s.piece t).toScheme ⟶ V.left :=
    iso.inv ≫ Spec.map (CommRingCat.ofHom h.toRingHom) ≫ j ≫ pullback.fst V.hom ζ
  have hh₁' : h.toRingHom.comp (algebraMap B C) =
      (Algebra.TensorProduct.includeRight (R := A') (A := A'') (B := B)).toRingHom :=
    congrArg AlgHom.toRingHom hh₁
  have hSpec : Spec.map (CommRingCat.ofHom h.toRingHom) ≫ j ≫ pullback.snd V.hom ζ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A') (A := A'')
        (B := B)).toRingHom) := by
    rw [hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hh₁']
  have hρ : ρ ≫ V.hom = (s.piece t).ι ≫ pullback.snd _ f := by
    change (iso.inv ≫ Spec.map (CommRingCat.ofHom h.toRingHom) ≫ j ≫
      pullback.fst V.hom ζ) ≫ V.hom = _
    slice_lhs 4 5 => rw [pullback.condition]
    slice_lhs 2 4 => rw [hSpec]
    slice_lhs 2 3 => rw [hζ, ← ch.pieceEmb_comp_snd f hY₀ hy A' φ' hφ' e t A'' φ'' hφ'']
    slice_lhs 1 2 => rw [hiso₁]
    rfl
  -- the point `(u, t)` of the piece goes to `v`
  have hpiecePt : (s.piecePt t).left =
      Spec.map (CommRingCat.ofHom
        (ch.piecePointBaseChange f hY₀ hy A' φ' hφ' e hval t A'' φ'' hφ'').1) ≫ iso.hom := by
    apply (cancel_mono (s.piece t).ι).mp
    rw [piecePt_left_ι, Category.assoc, hiso₂]
    exact (ch.SpecMap_piecePointBaseChange_comp_pieceEmb f hY₀ hy A' φ' hφ' e hval t A''
      φ'' hφ'').symm
  have hq : (ch.piecePointBaseChange f hY₀ hy A' φ' hφ' e hval t A'' φ'' hφ'').1.comp
      h.toRingHom = ψ.1 := by
    rw [← hh₂, Chart.piecePointBaseChange,
      Subsingleton.elim (ch.piecePoint f hY₀ hy A' φ' hφ' e hval t) (ψ.restrictScalars φ')]
  refine ⟨s, ⟨CategoryOfElements.homMk _ _ (MorphismProperty.Over.homMk ρ hρ) ?_⟩⟩
  apply CategoryTheory.Over.OverMorphism.ext
  change (s.piecePt t).left ≫ ρ = d.2.left
  rw [hpiecePt]
  change _ ≫ iso.hom ≫ iso.inv ≫ Spec.map (CommRingCat.ofHom h.toRingHom) ≫ j ≫
    pullback.fst V.hom ζ = _
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hq,
    hψ₁, ← Category.assoc, hψ₀, hpt₁]

/-- **The pieces of split neighbourhoods are cofinal among the pointed étale neighbourhoods of
`t`**: the piece functor is initial. -/
instance initial_pieceFunctor (t : GeometricFiber f y) : (pieceFunctor t).Initial :=
  Functor.initial_of_exists_of_isCofiltered _ (exists_pieceFunctor_obj_hom f t)
    fun {_ s} g g' ↦ exists_pieceFunctor_map_comp_eq t s g g'

end SplitNeighborhood

end AlgebraicGeometry.Scheme.Hom

end
