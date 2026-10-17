/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.DepthTwo
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.GaloisCoverAction
public import WeilConjectures.RingTheory.Etale.TraitSection

/-!
# The trait case of the spreading theorem

In the situation of the spreading theorem (blueprint `sbc-thm-spreading-finite-etale-galois`)
over a Noetherian base, let `s ∈ S` be a point of codimension one, so that `𝒪_{S,s}` is a
discrete valuation ring. The normalization `N ⟶ C` of `C` in the Galois cover is étale over
`σ(s)` (`AlgebraicGeometry.Scheme.SpreadingDatum.etaleOverSection_of_coheight_eq_one`, tame
ramification and Abhyankar's lemma) and then over all of `C_s`
(`AlgebraicGeometry.Scheme.SpreadingDatum.etaleOver_of_coheight_eq_one`, purity). This is the
first paragraph of the proof of [Stacks 0EYJ].
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.SpreadingDatum

variable {G : Type (u + 1)} [Group G] [Finite G] (D : SpreadingDatum G)

/-- Step of the proof of blueprint `sbc-thm-spreading-finite-etale-galois` (trait case, near
the section; first paragraph of the proof of [Stacks 0EYJ]): over a Noetherian base, at a point
`s` of codimension one the normalization `N ⟶ C` is étale over `σ(s)`.

Proof sketch. Base change to `R = 𝒪_{S,s}`, a discrete valuation ring (normal Noetherian local
of dimension one); normalization commutes with this localization. Then `C_s ⊆ C` is an effective
Cartier divisor, regular as it is smooth over a field, and `C_η = C \ C_s`. At the generic point
`ξ` of `C_s` the local ring is a discrete valuation ring and all ramification indices of the
Galois cover are equal to one `e` dividing `|G|` ([Stacks 09EB]), hence invertible: `Z` is tamely
ramified over `C` in codimension one. By Abhyankar's lemma for a regular divisor ([Stacks 0EYG],
itself proved through the purity of the branch locus [Stacks 0BMB] on the regular scheme
`C[x]/(xᵉ - π)`) and [Stacks 0EYH], étale locally on `C` the normalization is a disjoint union of
`Spec A[x]/(x^{e_i} - f)` with `f` a local equation of `C_s`. The section is transversal to
`C_s` (`σ⁻¹(C_s)` is the reduced closed point), and the fibre of `Z` over `σ(η)` is a disjoint
union of copies of `Spec κ(η)` (it has a rational point and `G` acts simply transitively), so
the trait test [Stacks 0EYI] forces all `e_i = 1` near `σ(s)`: `N` is étale over a
neighbourhood of `σ(s)`.

The commutative algebra is `Algebra.exists_etale_integralClosure_of_height_eq_one`, applied as in
`AlgebraicGeometry.Scheme.SpreadingDatum.etaleOverSection_of_two_le_coheight` to affine opens
`Spec R₀ = W ∋ s` and `Spec B = U ⊆ c⁻¹ W` with `σ(W) ⊆ U`, `B_K = Γ(C_η, j⁻¹ U)` and
`L = Γ(Z.P, ν⁻¹ U)`, a Galois `B_K`-algebra with group `G`
(`AlgebraicGeometry.Scheme.GaloisCover.galoisAction`,
`AlgebraicGeometry.Scheme.GaloisCover.mem_range_app_of_forall_smul_eq`,
`AlgebraicGeometry.Scheme.GaloisCover.rankAtStalk_app_eq`). -/
theorem etaleOverSection_of_coheight_eq_one [IsNoetherian D.S] (s : D.S)
    (hs : Order.coheight s = 1) :
    D.EtaleOverSection s := by
  obtain ⟨W, hW, U, hU, hUW, hsW, hWU⟩ := D.exists_affineOpens_section s
  have : Nonempty W := ⟨⟨s, hsW⟩⟩
  have hjU : IsAffineOpen (D.j ⁻¹ᵁ U) := D.isAffineOpen_preimage_j hW hU hUW
  have hνU : IsAffineOpen (D.ν ⁻¹ᵁ U) := hjU.preimage D.Z.π
  -- rings `R₀ = Γ(S, W)`, `B = Γ(C, U)`, `B_K = Γ(C_η, j⁻¹ U)`, `L = Γ(Z.P, ν⁻¹ U)`
  let := (D.c.appLE W U hUW).hom.toAlgebra
  let := (D.j.appLE U (D.j ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  let : Algebra Γ(D.Cη, D.j ⁻¹ᵁ U) Γ(D.Z.P, D.ν ⁻¹ᵁ U) :=
    (D.Z.π.app (D.j ⁻¹ᵁ U)).hom.toAlgebra
  let := (D.ν.app U).hom.toAlgebra
  have : IsScalarTower Γ(D.C, U) Γ(D.Cη, D.j ⁻¹ᵁ U) Γ(D.Z.P, D.ν ⁻¹ᵁ U) :=
    .of_algebraMap_eq' (by
      simp only [RingHom.algebraMap_toAlgebra, ← Scheme.Hom.app_eq_appLE]
      rfl)
  have : IsIntegrallyClosed Γ(D.S, W) :=
    isIntegrallyClosed_of_isIntegrallyClosed_stalk D.isIntegrallyClosed_stalk W
  have : IsNoetherianRing Γ(D.S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have : Algebra.Smooth Γ(D.S, W) Γ(D.C, U) :=
    HasRingHomProperty.appLE @Smooth D.c inferInstance ⟨W, hW⟩ ⟨U, hU⟩ hUW
  have : IsLocallyNoetherian D.C := LocallyOfFiniteType.isLocallyNoetherian D.c
  have : IsNoetherianRing Γ(D.C, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have := D.isLocalization_appLE_j hW hU hUW
  have : Module.Finite Γ(D.Cη, D.j ⁻¹ᵁ U) Γ(D.Z.P, D.ν ⁻¹ᵁ U) :=
    IsFinite.finite_app D.Z.π _ hjU
  have : Algebra.Etale Γ(D.Cη, D.j ⁻¹ᵁ U) Γ(D.Z.P, D.ν ⁻¹ᵁ U) := by
    have := HasRingHomProperty.appLE @Etale D.Z.π inferInstance ⟨_, hjU⟩
      ⟨_, hjU.preimage D.Z.π⟩ le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  -- the section `ε : B → R₀`
  have hσc : D.c.appLE W U hUW ≫ D.σ.appLE U W hWU = 𝟙 _ := by
    rw [Scheme.Hom.appLE_comp_appLE]
    have (g : D.S ⟶ D.S) (hg : g = 𝟙 _) (e : W ≤ g ⁻¹ᵁ W) : g.appLE W W e = 𝟙 _ := by
      subst hg
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
      exact D.S.presheaf.map_id _
    exact this _ D.σ_c _
  let ε : Γ(D.C, U) →ₐ[Γ(D.S, W)] Γ(D.S, W) :=
    { toRingHom := (D.σ.appLE U W hWU).hom
      commutes' r := congr(($hσc).hom r) }
  -- the prime `q` of `s`, of height one, and the prime `ε⁻¹ q` of `σ(s)`
  let q := (hW.primeIdealOf ⟨s, hsW⟩).asIdeal
  have hq : q.height = 1 := by
    let := TopCat.Presheaf.algebra_section_stalk D.S.presheaf ⟨s, hsW⟩
    have := hW.isLocalization_stalk ⟨s, hsW⟩
    have h := IsLocalization.AtPrime.ringKrullDim_eq_height q (D.S.presheaf.stalk s)
    rw [ringKrullDim_stalk_eq_coheight] at h
    rw [hs] at h
    exact (WithBot.coe_inj.1 h).symm
  have hP : hU.fromSpec (⟨q.comap ε, inferInstance⟩ : PrimeSpectrum Γ(D.C, U)) = D.σ s := by
    have := congrArg (fun m ↦ m (hW.primeIdealOf ⟨s, hsW⟩))
      (IsAffineOpen.SpecMap_appLE_fromSpec D.σ hU hW hWU)
    simp only [Scheme.Hom.comp_apply, hW.fromSpec_primeIdealOf] at this
    exact this
  -- the `k = |G|` points of `L` along the section, from the rational point of `Z` over `σ(η)`
  obtain ⟨z, hz⟩ := D.exists_point
  have hK : ⊤ ≤ D.S.fromSpecFunctionField ⁻¹ᵁ W := top_le_preimage_fromSpecFunctionField W
  have hzg (g : G) : (z ≫ D.Z.smul g) ≫ D.ν = D.S.fromSpecFunctionField ≫ D.σ := by
    simp only [ν, Category.assoc, reassoc_of% (D.Z.smul_π g)]
    rw [← Category.assoc, hz, D.sη_j]
  have hle (g : G) : ⊤ ≤ (z ≫ D.Z.smul g) ⁻¹ᵁ D.ν ⁻¹ᵁ U := by
    intro t _
    rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hzg,
      Scheme.Hom.comp_apply]
    exact hWU (hK trivial)
  let φc (g : G) : Γ(D.Z.P, D.ν ⁻¹ᵁ U) ⟶ D.S.functionField :=
    (z ≫ D.Z.smul g).appLE (D.ν ⁻¹ᵁ U) ⊤ (hle g) ≫
      (Scheme.ΓSpecIso D.S.functionField).hom
  have hφc (g : G) : D.ν.app U ≫ φc g = D.σ.appLE U W hWU ≫ D.S.germToFunctionField W := by
    have key (m : Spec D.S.functionField ⟶ D.C) (hm : m = D.S.fromSpecFunctionField ≫ D.σ)
        (e : ⊤ ≤ m ⁻¹ᵁ U) :
        m.appLE U ⊤ e = D.σ.appLE U W hWU ≫ D.S.fromSpecFunctionField.appLE W ⊤ hK := by
      subst hm
      rw [Scheme.Hom.appLE_comp_appLE]
    rw [← Category.assoc, ← Scheme.Hom.comp_appLE, key _ (hzg g),
      fromSpecFunctionField_appLE_eq, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hφcinj : Function.Injective φc := by
    intro g h hgh
    have hTop := isAffineOpen_top (Spec D.S.functionField)
    have h1 := (cancel_mono _).1 hgh
    have h2 := congrArg (fun m ↦ Spec.map m ≫ hνU.fromSpec) h1
    simp only [IsAffineOpen.SpecMap_appLE_fromSpec _ hνU hTop] at h2
    rw [IsAffineOpen.fromSpec_top, cancel_epi] at h2
    have : Nonempty (Spec D.S.functionField) :=
      inferInstanceAs (Nonempty (PrimeSpectrum D.S.functionField))
    exact D.Z.eq_of_comp_smul_eq z h2
  let eG := Finite.equivFin G
  let φ (i : Fin (Nat.card G)) : Γ(D.Z.P, D.ν ⁻¹ᵁ U) →+* D.S.functionField :=
    (φc (eG.symm i)).hom
  have hφ (i : Fin (Nat.card G)) : (φ i).comp (algebraMap Γ(D.C, U) Γ(D.Z.P, D.ν ⁻¹ᵁ U)) =
      (algebraMap Γ(D.S, W) D.S.functionField).comp ε.toRingHom :=
    congrArg CommRingCat.Hom.hom (hφc (eG.symm i))
  have hφinj : Function.Injective φ := fun i j hij ↦
    eG.symm.injective (hφcinj (CommRingCat.hom_ext hij))
  -- the Galois structure of `L` over `B_K`
  let : MulSemiringAction G Γ(D.Z.P, D.ν ⁻¹ᵁ U) := D.Z.galoisAction (D.j ⁻¹ᵁ U)
  have : SMulCommClass G Γ(D.Cη, D.j ⁻¹ᵁ U) Γ(D.Z.P, D.ν ⁻¹ᵁ U) :=
    D.Z.smulCommClass_galoisAction (D.j ⁻¹ᵁ U)
  have hfix (x : Γ(D.Z.P, D.ν ⁻¹ᵁ U)) (hx : ∀ g : G, g • x = x) :
      x ∈ Set.range (algebraMap Γ(D.Cη, D.j ⁻¹ᵁ U) Γ(D.Z.P, D.ν ⁻¹ᵁ U)) :=
    D.Z.mem_range_app_of_forall_smul_eq hjU x hx
  have hrank (p : PrimeSpectrum Γ(D.Cη, D.j ⁻¹ᵁ U)) :
      Module.rankAtStalk (R := Γ(D.Cη, D.j ⁻¹ᵁ U)) Γ(D.Z.P, D.ν ⁻¹ᵁ U) p = Nat.card G :=
    D.Z.rankAtStalk_app_eq hjU p
  have hG : IsUnit (Nat.card G : Γ(D.S, W)) := by
    simpa using D.isUnit_card.map (D.S.presheaf.map (homOfLE le_top).op).hom
  -- the commutative algebra
  have := functionField_isFractionRing_of_isAffineOpen D.S W hW
  obtain ⟨g, hg, hE⟩ := Algebra.exists_etale_integralClosure_of_height_eq_one
    (Bk := Γ(D.Cη, D.j ⁻¹ᵁ U)) (L := Γ(D.Z.P, D.ν ⁻¹ᵁ U)) ε q hq G hfix hrank hG φ hφ hφinj
  have hEg := D.ν.etale_fromNormalization_basicOpen hU hνU g hE
  rw [etaleOverSection_iff]
  intro x hx
  refine Scheme.Hom.mem_etaleLocus.2 ⟨_, ?_, hEg⟩
  rw [Scheme.Hom.mem_preimage, hx, ← hP]
  have : (⟨q.comap ε, inferInstance⟩ : PrimeSpectrum Γ(D.C, U)) ∈
      hU.fromSpec ⁻¹ᵁ D.C.basicOpen g := by
    rw [hU.fromSpec_preimage_basicOpen, PrimeSpectrum.mem_basicOpen]
    exact hg
  exact this

/-- Step of the proof of blueprint `sbc-thm-spreading-finite-etale-galois` (trait case, purity;
first paragraph of the proof of [Stacks 0EYJ]): over a Noetherian base, at a point `s` of
codimension one, if the normalization `N ⟶ C` is étale over the generic point and over `σ(s)`,
it is étale over all of `C_s`.

Proof. The only strict generization of `s` is the generic point of `S`, so this is
`AlgebraicGeometry.Scheme.SpreadingDatum.etaleOver_of_etaleOverSection`: the generic point of the
irreducible fibre `C_s` specializes to `σ(s)`, so `N` is unramified over `C` in codimension one;
`C` is regular along `C_s` (smooth over the discrete valuation ring `𝒪_{S,s}`), and purity
across the regular divisor `C_s` ([Stacks 0EYE], through
`AlgebraicGeometry.Scheme.Hom.mem_etaleLocus_fromNormalization_of_smooth`) shows that `N` is
étale at every point over `s`. -/
theorem etaleOver_of_coheight_eq_one [IsNoetherian D.S] (s : D.S)
    (hs : Order.coheight s = 1) (hη : D.EtaleOver (genericPoint D.S))
    (hsec : D.EtaleOverSection s) : D.EtaleOver s := by
  refine D.etaleOver_of_etaleOverSection (D.ne_genericPoint_of_coheight_ne_zero (by simp [hs]))
    (fun s' hs' hne ↦ ?_) hsec
  have hlt : s < s' := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hs')
    fun h ↦ hne (Inseparable.eq ((Scheme.le_iff_specializes.1 h).antisymm hs')).symm
  have h1 := Order.coheight_add_one_le hlt
  rw [hs] at h1
  have h0 : Order.coheight s' = 0 := by
    induction h : Order.coheight s' using ENat.recTopCoe with
    | top => simp [h] at h1
    | coe n => rw [h] at h1; norm_cast at h1 ⊢; omega
  by_cases h : s' = genericPoint D.S
  · exact h ▸ hη
  · exact absurd h0 (coheight_ne_zero_of_ne_genericPoint s' h)

end AlgebraicGeometry.Scheme.SpreadingDatum
