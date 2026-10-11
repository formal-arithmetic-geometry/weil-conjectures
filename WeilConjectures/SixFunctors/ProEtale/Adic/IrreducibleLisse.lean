/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseRank
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk

/-!
# Lisse `ℓ`-adic sheaves on an irreducible scheme

On an irreducible scheme `Y` the pointwise rank of a morphism of lisse sheaves is constant: it
descends to `Y` along a trivialising pro-étale cover
(`AlgebraicGeometry.ProEtale.AdicSheaf.rank_eq_of_apply_eq`), is constant along specializations
(the entries of the matrices are continuous functions to the Hausdorff space `ℚ̄_ℓ`, and flat
morphisms lift generizations), and every point of `Y` is a specialization of the generic point.
Hence kernels and cokernels of morphisms of lisse sheaves are lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.kernel_cokernel_of_irreducibleSpace`): the lisse
sheaves on `Y` form an abelian subcategory.

Likewise a lisse sheaf `H` on `Y` has a rank `r`: its pullback to every geometric point is
`ℚ̄_ℓ^r`, and `H = 0` if and only if `r = 0`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_rank_of_irreducibleSpace`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}

open AdicSheaf in
/-- **Kernels and cokernels of lisse sheaves on an irreducible scheme are lisse.** The pointwise
rank of a morphism of lisse sheaves descends to `Y`, is constant along specializations, hence
equal everywhere to its value at the generic point; morphisms of finite free modules of constant
rank have lisse kernel and cokernel. -/
theorem IsAdicLisseSheaf.kernel_cokernel_of_irreducibleSpace [IrreducibleSpace Y]
    {F G : AdicSheaf l Y} (hF : IsAdicLisseSheaf F) (hG : IsAdicLisseSheaf G) (φ : F ⟶ G) :
    IsAdicLisseSheaf (kernel φ) ∧ IsAdicLisseSheaf (cokernel φ) := by
  classical
  obtain ⟨R, hR, hRF⟩ := hF
  obtain ⟨R', hR', hR'G⟩ := hG
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  obtain ⟨ι', V', f', rfl⟩ := R'.exists_eq_ofArrows
  have hW := Precoverage.comp_mem_coverings f hR (fun i j ↦ pullback.fst (f i) (f' j))
    (fun i ↦ Precoverage.mem_coverings_of_isPullback f' hR' (f i) _ _
      fun j ↦ IsPullback.of_hasPullback (f i) (f' j))
  let W (k : Σ _ : ι, ι') : Scheme.{u} := pullback (f k.1) (f' k.2)
  let g (k : Σ _ : ι, ι') : W k ⟶ Y := pullback.fst (f k.1) (f' k.2) ≫ f k.1
  change Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage Y at hW
  have hgw (k) : WeaklyEtale (g k) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hW (.mk k)
  choose n e using fun i ↦ hRF (f i) (.mk i)
  choose m e' using fun j ↦ hR'G (f' j) (.mk j)
  let eF (k : Σ _ : ι, ι') : (g k)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin (n k.1) ↦ unit l (W k) :=
    trivPull (f k.1) (e k.1).some (pullback.fst (f k.1) (f' k.2))
  let eG (k : Σ _ : ι, ι') : (g k)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin (m k.2) ↦ unit l (W k) :=
    (adicUpperStarCongr l pullback.condition).app G ≪≫
      trivPull (f' k.2) (e' k.2).some (pullback.snd (f k.1) (f' k.2))
  let M (k : Σ _ : ι, ι') := unitMatrix ((eF k).inv ≫ (g k)^*ᵃ[l].map φ ≫ (eG k).hom)
  let rk (k : Σ _ : ι, ι') (v : W k) : ℕ :=
    ((M k).map (PadicAlgCl.locallyFiniteFunctionsEval v)).rank
  have hfc (k k' : Σ _ : ι, ι') (v : W k) (v' : W k') (h : g k v = g k' v') :
      rk k v = rk k' v' :=
    rank_eq_of_apply_eq φ (g k) (g k') (eF k) (eG k) (eF k') (eG k') v v' h
  have hspec (k : Σ _ : ι, ι') {v₀ v : W k} (hv : v₀ ⤳ v) : rk k v₀ = rk k v := by
    have : (M k).map (PadicAlgCl.locallyFiniteFunctionsEval v₀) =
        (M k).map (PadicAlgCl.locallyFiniteFunctionsEval v) := by
      ext a b
      exact (hv.map ((M k) a b).1.continuous).eq
    simp only [rk, this]
  -- every point of a member generizes to a point over the generic point of `Y`
  have hgen (k k' : Σ _ : ι, ι') (v : W k) (v' : W k') : rk k v = rk k' v' := by
    obtain ⟨v₀, hv₀, h₀⟩ := Flat.generalizingMap (g k) (genericPoint_specializes (g k v))
    obtain ⟨v₀', hv₀', h₀'⟩ := Flat.generalizingMap (g k') (genericPoint_specializes (g k' v'))
    rw [← hspec k hv₀, ← hspec k' hv₀']
    exact hfc _ _ _ _ (h₀.trans h₀'.symm)
  have hmem (k : Σ _ : ι, ι') : IsAdicLisseSheaf (kernel ((g k)^*ᵃ[l].map φ)) ∧
      IsAdicLisseSheaf (cokernel ((g k)^*ᵃ[l].map φ)) := by
    refine isAdicLisseSheaf_kernel_of_eq_comp _ _ (eF k).symm (eG k) rfl ?_
    by_cases hk : Nonempty (W k)
    · obtain ⟨w₀⟩ := hk
      exact isAdicLisseSheaf_kernel_cokernel_of_rank_eq _ (rk k w₀) fun w ↦ hgen k k w w₀
    · exact isAdicLisseSheaf_kernel_cokernel_of_rank_eq _ 0 fun w ↦ (hk ⟨w⟩).elim
  exact ⟨IsAdicLisseSheaf.of_presieve _ hW fun _ _ ⟨k⟩ ↦
      (hmem k).1.of_iso (PreservesKernel.iso _ _).symm,
    IsAdicLisseSheaf.of_presieve _ hW fun _ _ ⟨k⟩ ↦
      (hmem k).2.of_iso (PreservesCokernel.iso _ _).symm⟩

open ZeroObject in
/-- **The rank of a lisse sheaf on an irreducible scheme.** A lisse sheaf `H` on an irreducible
scheme `Y` has a rank `r`: its pullback to every geometric point `s : Spec K ⟶ Y` is `ℚ̄_ℓ^r`,
and `H = 0` if and only if `r = 0`. The rank of a trivialisation descends to `Y`, and any two
members of a trivialising cover have points over the generic point of `Y`, flat morphisms lifting
generizations. -/
theorem IsAdicLisseSheaf.exists_rank_of_irreducibleSpace [IrreducibleSpace Y]
    {H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H) :
    ∃ r : ℕ, (IsZero H ↔ r = 0) ∧ ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (.of K) ⟶ Y), Nonempty ((s)^*ᵃ[l].obj H ≅
        ⨁ fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of K))) := by
  classical
  obtain ⟨R, hR, hRH⟩ := hH
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hf (i : ι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  choose n e using fun i ↦ hRH (f i) (.mk i)
  -- the rank of the trivialisations descends to `Y`
  have hn (i i' : ι) (v : V i) (v' : V i') (hvv' : f i v = f i' v') : n i = n i' := by
    have := AdicSheaf.rank_eq_of_apply_eq (𝟙 H) (f i) (f i') (e i).some (e i).some (e i').some
      (e i').some v v' hvv'
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id, AdicSheaf.unitMatrix_id, AdicSheaf.unitMatrix_id,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.rank_one, Matrix.rank_one, Fintype.card_fin, Fintype.card_fin] at this
    exact this
  -- every member with a point has a point over the generic point
  have hgen (i i' : ι) (v : V i) (v' : V i') : n i = n i' := by
    obtain ⟨v₀, -, h₀⟩ := Flat.generalizingMap (f i) (genericPoint_specializes (f i v))
    obtain ⟨v₀', -, h₀'⟩ := Flat.generalizingMap (f i') (genericPoint_specializes (f i' v'))
    exact hn _ _ _ _ (h₀.trans h₀'.symm)
  have hsurj : ∀ y, ∃ i, y ∈ Set.range (f i) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
      (Scheme.propQCPrecoverage_le_precoverage _ hR)).1
  obtain ⟨i₀, v₀, -⟩ := hsurj (genericPoint Y)
  refine ⟨n i₀, ⟨fun hz ↦ ?_, fun h0 ↦ ?_⟩, fun K _ _ s ↦ ?_⟩
  · by_contra hne
    have hz' : IsZero (⨁ fun _ : Fin (n i₀) ↦ AdicSheaf.unit l (V i₀)) :=
      (Functor.map_isZero _ hz).of_iso (e i₀).some.symm
    have : Nonempty (V i₀) := ⟨v₀⟩
    exact not_isZero_adicConstantSheaf l (V i₀) ((AdicSheaf.forget _).map_isZero
      (IsZero.of_mono (biproduct.ι (fun _ : Fin (n i₀) ↦ AdicSheaf.unit l (V i₀))
        ⟨0, Nat.pos_of_ne_zero hne⟩) hz'))
  · have hz (i : ι) : IsZero ((f i)^*ᵃ[l].obj H) := by
      by_cases hV : Nonempty (V i)
      · obtain ⟨v⟩ := hV
        refine IsZero.of_iso ?_ (e i).some
        rw [hgen i i₀ v v₀, h0]
        exact ⟨fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext' _ _ fun j ↦ Fin.elim0 j⟩⟩,
          fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext _ _ fun j ↦ Fin.elim0 j⟩⟩⟩
      · have : IsEmpty (V i) := not_nonempty_iff.1 hV
        exact isZero_adicSheaf_of_isEmpty l _
    have : IsIso (0 : H ⟶ 0) := isIso_of_isIso_adicUpperStar l f hR _ fun i ↦ by
      have hz' : IsZero ((f i)^*ᵃ[l].obj 0) := Functor.map_isZero _ (isZero_zero _)
      rw [(hz i).eq_of_src ((f i)^*ᵃ[l].map 0) ((hz i).iso hz').hom]
      infer_instance
    exact (isZero_zero _).of_iso (asIso (0 : H ⟶ 0))
  · obtain ⟨j, w, hw⟩ := hsurj (s.base (IsLocalRing.closedPoint K))
    obtain ⟨t, ht⟩ := exists_comp_eq_of_weaklyEtale (f j) s ⟨w, hw⟩
    rw [← hgen j i₀ w v₀]
    exact ⟨(adicUpperStarCongr l ht.symm).app H ≪≫ AdicSheaf.trivPull (f j) (e j).some t⟩

end AlgebraicGeometry.ProEtale
