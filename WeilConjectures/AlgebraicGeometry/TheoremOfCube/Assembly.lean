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

namespace TheoremOfCube

variable {K : Type u} [Field K] (X Y Z : Over (Spec (.of K)))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **Gluing the local lifts.** If `H¹` of the twist `𝒢` vanishes over `f⁻¹ V` for an affine
open `V` of `Z`, there is a section of `L` over `f⁻¹ V` generating `L` along the slice
`{x} × Y × Z`. -/
theorem exists_section_isFreeGenerator (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (L : ((X ⊗ Y) ⊗ Z).left.Modules) [L.IsInvertible]
    {ex : Γ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L, ⊤)}
    {ey : Γ((Scheme.Modules.pullback (sliceY X Y Z y)).obj L, ⊤)}
    (hex : Scheme.Modules.IsFreeGenerator ex)
    (hC : (sliceComparison X Y Z x y L).hom.app ⊤ (Scheme.Modules.pullbackSection _ ex) =
      Scheme.Modules.pullbackSection _ ey)
    {V : Z.left.Opens} (hV : IsAffineOpen V) [IsSeparated ((snd (X ⊗ Y) Z).left ∣_ V)]
    (hH : Subsingleton (((Scheme.Modules.pullback ((snd (X ⊗ Y) Z).left ⁻¹ᵁ V).ι).obj
      (twist X Y Z x y L)).H 1)) :
    ∃ s : Γ(L, (snd (X ⊗ Y) Z).left ⁻¹ᵁ V), ∀ q : (Y ⊗ Z).left,
      sliceX X Y Z x q ∈ (snd (X ⊗ Y) Z).left ⁻¹ᵁ V →
      ∃ (W : ((X ⊗ Y) ⊗ Z).left.Opens) (hW : W ≤ (snd (X ⊗ Y) Z).left ⁻¹ᵁ V),
        sliceX X Y Z x q ∈ W ∧ Scheme.Modules.IsFreeGenerator (L.presheaf.map (homOfLE hW).op s) := by
  classical
  have : SheafOfModules.IsInvertible.{u, u, u} L := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  have := Scheme.Modules.isQuasicoherent_toModules (crossIdeal X Y x y)
  have : (twist X Y Z x y L).IsQuasicoherent := Scheme.Modules.isQuasicoherent_tensorObj _ L
  let S := ((snd (X ⊗ Y) Z).left ⁻¹ᵁ V)
  have : IsAffine V.toScheme := hV
  -- the data of the cover
  have hdata (q : S.toScheme) : ∃ (UW : (X ⊗ Y).left.Opens) (O : ((X ⊗ Y) ⊗ Z).left.Opens)
      (ℓ : Γ(L, O)) (sq : Γ(L, O)), IsAffineOpen UW ∧ IsAffineOpen O ∧ S.ι q ∈ O ∧ O ≤ S ∧
      O ≤ (fst (X ⊗ Y) Z).left ⁻¹ᵁ UW ∧ Scheme.Modules.IsFreeGenerator ℓ ∧
      Scheme.Modules.pullbackSection (sliceX X Y Z x) sq =
        ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L).presheaf.map (homOfLE le_top).op ex ∧
      Scheme.Modules.pullbackSection (sliceY X Y Z y) sq =
        ((Scheme.Modules.pullback (sliceY X Y Z y)).obj L).presheaf.map (homOfLE le_top).op ey := by
    obtain ⟨UW, hUW, hqUW, -⟩ := exists_isAffineOpen_mem_and_subset
      (x := (fst (X ⊗ Y) Z).left (S.ι q)) (U := ⊤) trivial
    have hqS : S.ι q ∈ S := by
      have h := Scheme.Opens.range_ι S
      exact (Set.ext_iff.mp h _).mp ⟨q, rfl⟩
    obtain ⟨O, hpO, hOle, ℓ, hℓ⟩ := Scheme.Modules.exists_isFreeGenerator L
      (W := S ⊓ (fst (X ⊗ Y) Z).left ⁻¹ᵁ UW) ⟨hqS, hqUW⟩
    obtain ⟨sq, hsx, hsy⟩ := exists_lift X Y Z x y L O.2 hℓ ex ey hC
    exact ⟨UW, O.1, ℓ, sq, hUW, O.2, hpO, hOle.trans inf_le_left, hOle.trans inf_le_right, hℓ,
      hsx, hsy⟩
  choose UW O ℓ sq hUW hO hqO hOS hOπ hℓ hsx hsy using hdata
  -- the cover of `S` and its intersections
  have : IsSeparated (terminal.from S.toScheme) := by
    rw [← terminal.comp_from ((snd (X ⊗ Y) Z).left ∣_ V)]
    have : IsAffine V.toScheme := hV
    infer_instance
  let Ω (q : S.toScheme) : S.toScheme.Opens := S.ι ⁻¹ᵁ O q
  have hΩim (q : S.toScheme) : S.ι ''ᵁ Ω q = O q := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (hOS q)]
  have hΩ (q : S.toScheme) : IsAffineOpen (Ω q) :=
    (hO q).preimage_of_isOpenImmersion S.ι (by rw [Scheme.Opens.opensRange_ι]; exact hOS q)
  have hcov : iSup Ω = ⊤ :=
    eq_top_iff.mpr fun q _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨q, hqO q⟩
  have hinter {n : ℕ} (y : Fin (n + 1) → S.toScheme) :
      IsAffineOpen (S.ι ''ᵁ ⨅ l, Ω (y l)) ∧ S.ι ''ᵁ ⨅ l, Ω (y l) ≤ O (y 0) := by
    refine ⟨(IsAffineOpen.iInf fun l ↦ hΩ (y l)).image_of_isOpenImmersion S.ι, ?_⟩
    rw [← hΩim (y 0)]
    exact S.ι.image_mono (iInf_le _ 0)
  -- the restricted modules
  let ι' := (Scheme.Modules.restrictFunctor S.ι).map (twistι X Y Z x y L)
  have : SheafOfModules.IsQuasicoherent (R := S.toScheme.ringCatSheaf)
      ((twist X Y Z x y L).restrict S.ι) :=
    (SheafOfModules.isQuasicoherent S.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback S.ι).app _).symm
      (inferInstance : SheafOfModules.IsQuasicoherent (R := S.toScheme.ringCatSheaf)
        ((Scheme.Modules.pullback S.ι).obj (twist X Y Z x y L)))
  have hH' : Subsingleton (((twist X Y Z x y L).restrict S.ι).H 1) :=
    (Scheme.Modules.H.mapLinearEquiv
      ((Scheme.Modules.restrictFunctorIsoPullback S.ι).app _) 1).toEquiv.subsingleton
  -- the local lifts on `S`
  let s' (q : S.toScheme) : Γ(L.restrict S.ι, Ω q) :=
    L.presheaf.map (homOfLE (hΩim q).le).op (sq q)
  have hpx (q : S.toScheme) {W : ((X ⊗ Y) ⊗ Z).left.Opens} (hW : W ≤ O q) :
      Scheme.Modules.pullbackSection (sliceX X Y Z x) (L.presheaf.map (homOfLE hW).op (sq q)) =
        ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L).presheaf.map (homOfLE le_top).op ex := by
    rw [Scheme.Modules.pullbackSection_map, hsx q, Scheme.Modules.presheaf_map_homOfLE_map_homOfLE]
  have hpy (q : S.toScheme) {W : ((X ⊗ Y) ⊗ Z).left.Opens} (hW : W ≤ O q) :
      Scheme.Modules.pullbackSection (sliceY X Y Z y) (L.presheaf.map (homOfLE hW).op (sq q)) =
        ((Scheme.Modules.pullback (sliceY X Y Z y)).obj L).presheaf.map (homOfLE le_top).op ey := by
    rw [Scheme.Modules.pullbackSection_map, hsy q, Scheme.Modules.presheaf_map_homOfLE_map_homOfLE]
  have hsub {A : Scheme.{u}} (g : A ⟶ ((X ⊗ Y) ⊗ Z).left) {W : ((X ⊗ Y) ⊗ Z).left.Opens}
      (a b : Γ(L, W)) : Scheme.Modules.pullbackSection g (a - b) =
        Scheme.Modules.pullbackSection g a - Scheme.Modules.pullbackSection g b :=
    map_sub _ _ _
  have hinj (y3 : Fin 3 → S.toScheme) : Function.Injective (ι'.app (⨅ l, Ω (y3 l))) := by
    obtain ⟨hA, hle⟩ := hinter y3
    exact injective_twistι_app X Y Z x y L hA (hUW (y3 0)) (hle.trans (hOπ (y3 0)))
      ((hℓ (y3 0)).map hle)
  have hs (y2 : Fin 2 → S.toScheme) : ∃ c : Γ((twist X Y Z x y L).restrict S.ι, ⨅ l, Ω (y2 l)),
      ι'.app _ c = (L.restrict S.ι).presheaf.map (homOfLE (iInf_le (fun l ↦ Ω (y2 l)) 1)).op
        (s' (y2 1)) - (L.restrict S.ι).presheaf.map
          (homOfLE (iInf_le (fun l ↦ Ω (y2 l)) 0)).op (s' (y2 0)) := by
    obtain ⟨hA, hle⟩ := hinter y2
    have hle (i : Fin 2) : S.ι ''ᵁ ⨅ l, Ω (y2 l) ≤ O (y2 i) :=
      (S.ι.image_mono (iInf_le _ i)).trans (hΩim (y2 i)).le
    obtain ⟨c, hc⟩ := mem_range_twistι_app X Y Z x y L hA (hUW (y2 0))
      ((hle 0).trans (hOπ (y2 0))) ((hℓ (y2 0)).map (hle 0))
      (h := L.presheaf.map (homOfLE (hle 1)).op (sq (y2 1)) -
        L.presheaf.map (homOfLE (hle 0)).op (sq (y2 0)))
      (by rw [hsub, hpx, hpx, sub_self]) (by rw [hsub, hpy, hpy, sub_self])
    have e (i : Fin 2) : (L.restrict S.ι).presheaf.map
        (homOfLE (iInf_le (fun l ↦ Ω (y2 l)) i)).op (s' (y2 i)) =
        L.presheaf.map (homOfLE (hle i)).op (sq (y2 i)) :=
      by rw [Scheme.Modules.restrict_map]
         exact Scheme.Modules.presheaf_map_presheaf_map_apply _ _ _ _ _
    rw [e 1, e 0]
    exact ⟨c, hc⟩
  obtain ⟨t, ht⟩ := Scheme.Modules.exists_forall_exists_app_eq_sub_of_subsingleton_H_one
    ((snd (X ⊗ Y) Z).left ∣_ V) ι' hH' Ω hΩ hcov hinj s' hs
  have hSS : S.ι ''ᵁ ⊤ = S := Scheme.Opens.ι_image_top S
  refine ⟨L.presheaf.map (homOfLE hSS.ge).op t, fun q₀ hq₀ ↦ ?_⟩
  obtain ⟨q, hq⟩ : sliceX X Y Z x q₀ ∈ Set.range S.ι := by
    have h := Scheme.Opens.range_ι S
    exact (Set.ext_iff.mp h _).mpr hq₀
  obtain ⟨b, hb⟩ := ht q
  have hΩS : S.ι ''ᵁ Ω q ≤ S.ι ''ᵁ ⊤ := S.ι.image_mono le_top
  have hb' : L.presheaf.map (homOfLE hΩS).op t =
      (twistι X Y Z x y L).app (S.ι ''ᵁ Ω q) b +
        L.presheaf.map (homOfLE (hΩim q).le).op (sq q) :=
    (eq_add_of_sub_eq hb.symm)
  have hA : IsAffineOpen (S.ι ''ᵁ Ω q) := (hΩ q).image_of_isOpenImmersion S.ι
  have hπ : S.ι ''ᵁ Ω q ≤ (fst (X ⊗ Y) Z).left ⁻¹ᵁ UW q := (hΩim q).le.trans (hOπ q)
  have hpb : Scheme.Modules.pullbackSection (sliceX X Y Z x)
      (L.presheaf.map (homOfLE hΩS).op t) =
      ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L).presheaf.map (homOfLE le_top).op ex := by
    rw [hb', Scheme.Modules.pullbackSection_add,
      (pullbackSection_twistι_app_eq_zero X Y Z x y L hA (hUW q) hπ
        ((hℓ q).map (hΩim q).le) b).1, zero_add, hpx]
  have hgen : Scheme.Modules.IsFreeGenerator (Scheme.Modules.pullbackSection (sliceX X Y Z x)
      (L.presheaf.map (homOfLE hΩS).op t)) := by
    rw [hpb]
    exact hex.map le_top
  have hq₀' : sliceX X Y Z x q₀ ∈ S.ι ''ᵁ Ω q := by
    rw [hΩim q, ← hq]
    exact hqO q
  obtain ⟨W, hW, hqW, hWgen⟩ :=
    Scheme.Modules.exists_isFreeGenerator_of_isFreeGenerator_pullbackSection (sliceX X Y Z x)
      ((hℓ q).map (hΩim q).le) hgen hq₀'
  refine ⟨W, hW.trans ((hΩim q).le.trans (hOS q)), hqW, ?_⟩
  rw [Scheme.Modules.presheaf_map_homOfLE_map_homOfLE] at hWgen
  rw [Scheme.Modules.presheaf_map_homOfLE_map_homOfLE]
  exact hWgen

end TheoremOfCube

end AlgebraicGeometry
