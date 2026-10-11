/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.TheoremOfCube.SpreadOut

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {P T : Scheme.{u}}

/-- **Triviality on a fibre is preserved by restriction to an open of the base.** For `f`
proper with geometrically integral fibres and `L` invertible, if `L` is trivial on the fibre
over a point `t` of an open `V`, then so is its restriction for `f ∣_ V`. -/
lemma nonempty_iso_unit_fiber_morphismRestrict (f : P ⟶ T) [IsProper f]
    [GeometricallyIntegral f] (L : P.Modules) [L.IsInvertible] (V : T.Opens) (t : V)
    (ht : Nonempty ((Modules.pullback (f.fiberι (V.ι t))).obj L ≅ 𝟙_ (f.fiber (V.ι t)).Modules)) :
    Nonempty ((Modules.pullback ((f ∣_ V).fiberι t)).obj ((Modules.pullback (f ⁻¹ᵁ V).ι).obj L) ≅
      𝟙_ ((f ∣_ V).fiber t).Modules) := by
  have := IsInvertible.isFinitePresentation L
  have := IsInvertible.isFinitePresentation Lᵛ
  obtain ⟨d⟩ := nonempty_tensorObj_dual_iso_unit L
  obtain ⟨μ⟩ := nonempty_pullback_tensorObj_iso (f ⁻¹ᵁ V).ι L Lᵛ
  have sq : IsPullback (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι := (isPullback_morphismRestrict f V).flip
  rw [nonempty_iso_unit_fiber_iff f d] at ht
  rw [nonempty_iso_unit_fiber_iff (f ∣_ V) (μ.symm ≪≫ (Modules.pullback _).mapIso d ≪≫
    pullbackObjUnitIso _), hFiber_pullback_of_isPullback f L V.ι _ _ sq,
    hFiber_pullback_of_isPullback f Lᵛ V.ι _ _ sq]
  exact ht


/-- **A section generating after pullback generates near the image.** Let `ℓ` be a free generator
of `L` on `O` and `s` a section of `L` over `O` whose pullback along `σ` is a free generator.
Then `s` is a free generator on an open neighbourhood of every point `σ q` in `O`. -/
lemma exists_isFreeGenerator_of_isFreeGenerator_pullbackSection {A : Scheme.{u}} (σ : A ⟶ P)
    {L : P.Modules} {O : P.Opens} {ℓ : Γ(L, O)} (hℓ : IsFreeGenerator ℓ) {s : Γ(L, O)}
    (hs : IsFreeGenerator (pullbackSection σ s)) {q : A} (hq : σ q ∈ O) :
    ∃ (W : P.Opens) (hW : W ≤ O), σ q ∈ W ∧
      IsFreeGenerator (L.presheaf.map (homOfLE hW).op s) := by
  obtain ⟨a, rfl⟩ := hℓ.exists_smul_eq s
  rw [pullbackSection_smul] at hs
  have hℓ' := hℓ.pullback_unit_app σ
  obtain ⟨u, hu⟩ := hℓ'.exists_unit_smul_eq hs
  have hau : σ.app O a = u.1 := hℓ'.smul_left_injective hu
  have hle : P.basicOpen a ≤ O := P.basicOpen_le a
  refine ⟨P.basicOpen a, hle, ?_, ?_⟩
  · have hq' : q ∈ σ ⁻¹ᵁ P.basicOpen a := by
      rw [Scheme.preimage_basicOpen, hau, A.basicOpen_of_isUnit u.isUnit]
      exact hq
    exact hq'
  · have hunit : IsUnit (P.presheaf.map (homOfLE hle).op a) :=
      P.toRingedSpace.isUnit_res_basicOpen a
    rw [map_smul]
    exact (hℓ.map hle).units_smul hunit.unit

end Scheme.Modules

end AlgebraicGeometry
