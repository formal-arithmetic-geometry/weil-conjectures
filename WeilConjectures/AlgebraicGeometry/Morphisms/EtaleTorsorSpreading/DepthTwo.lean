/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.GaloisCoverRank
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.Purity
public import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationBasicOpen
public import WeilConjectures.RingTheory.Etale.DepthTwo.Global

/-!
# The case of depth at least two of the spreading theorem

In the situation of the spreading theorem (blueprint `sbc-thm-spreading-finite-etale-galois`)
over a Noetherian base, let `s ∈ S` be a point of codimension at least two, so that `𝒪_{S,s}`
has depth at least two. If the normalization `N ⟶ C` of `C` in the Galois cover is étale over
all strict generizations of `s`, it is étale over `σ(s)`
(`AlgebraicGeometry.Scheme.SpreadingDatum.etaleOverSection_of_two_le_coheight`, through the
formal neighbourhood of the section) and then over all of `C_s`
(`AlgebraicGeometry.Scheme.SpreadingDatum.etaleOver_of_two_le_coheight`). This is the "proof of
the claim" in the proof of [Stacks 0EYJ].
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.SpreadingDatum

variable {G : Type (u + 1)} [Group G] [Finite G] (D : SpreadingDatum G)

/-- The section `σ` is a section of `c`. -/
lemma c_σ (x : D.S) : D.c (D.σ x) = x := by
  rw [← Scheme.Hom.comp_apply, D.σ_c]
  rfl

/-- Around every point `s` of `S` there are affine opens `W ∋ s` of `S` and `U ⊆ c⁻¹ W` of
`C` such that the section maps `W` into `U`. -/
lemma exists_affineOpens_section (s : D.S) : ∃ (W : D.S.Opens) (_ : IsAffineOpen W)
    (U : D.C.Opens) (_ : IsAffineOpen U) (_ : U ≤ D.c ⁻¹ᵁ W),
    s ∈ W ∧ W ≤ D.σ ⁻¹ᵁ U := by
  obtain ⟨W, hW, U, hU, hUW, hsU, -⟩ := D.exists_affineOpens (D.σ s)
  have hsW : s ∈ W := by
    have := hUW hsU
    rwa [Scheme.Hom.mem_preimage, c_σ] at this
  obtain ⟨r, hrU, hsr⟩ := hW.exists_basicOpen_le (V := D.σ ⁻¹ᵁ U) ⟨s, hsU⟩ hsW
  refine ⟨D.S.basicOpen r, hW.basicOpen r, D.C.basicOpen (D.c.appLE W U hUW r),
    hU.basicOpen _, ?_, hsr, fun x hx ↦ ?_⟩
  · rw [Scheme.basicOpen_appLE]
    exact inf_le_right
  · rw [Scheme.Hom.mem_preimage, Scheme.basicOpen_appLE]
    refine ⟨hrU hx, ?_⟩
    rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, c_σ]
    exact hx

/-- Step of the proof of blueprint `sbc-thm-spreading-finite-etale-galois` (depth at least two,
near the section; proof of the claim in [Stacks 0EYJ]): over a Noetherian base, at a point `s`
of codimension at least two, if the normalization `N ⟶ C` is étale over all strict
generizations of `s`, it is étale over `σ(s)`.

Proof sketch. Base change to `A = 𝒪_{S,s}` (normalization commutes with this localization); `U`
is the punctured spectrum of `A` and `N` is finite étale over `C_U`. As `A` is normal of dimension
at least two, `depth A ≥ 2` ([Stacks 031S]), and `depth 𝒪_{C,x} ≥ 2` for `x` over `s`
([Stacks 0337]); `N` is normal, so it is the finite `C`-scheme of [Stacks 0EY6] extending
`N|_{C_U}` with depth at least two along the complement, and its formation commutes with flat
base change. Choose an affine `Spec B ⊆ C` around `σ(s)`, so `A → B` is smooth with a section
`B → A` of kernel `I`; the `I`-adic completion is `B^ ≅ A[[x_1, …, x_d]]` ([Stacks 05D5]) and
`B → B^` is flat. Let `V ⊆ Spec B^` be the preimage of `U`, `W = N ×_C V`, and
`V_0 = V ∩ V(x_1, …, x_d) ≅ U`. Then `W_0 = W ×_V V_0 ⟶ U` is completely split: its generic
fibre is the fibre of `Z` over `σ(η)`, a disjoint union of copies of `Spec κ(η)`, and `U` is
normal. By the full faithfulness of `FÉt_V ⟶ FÉt_{V_0}` for power series over a local ring of
depth at least two ([Stacks 0EY9], which rests on `Γ(U, 𝒪_U) = A` in depth two [Stacks 0BK0], the
formal full faithfulness [Stacks 0EKP] and [Stacks 0EL8]), `W ≅ W_0 ×_U V` is split, hence so
is `N ×_C Spec B^`; by faithfully flat descent along `𝒪_{C,σ(s)} → B^` (localized at its maximal
ideal) `N` is étale over `σ(s)`.

The commutative algebra is `RingTheory.DepthTwo.exists_etale_integralClosure_of_two_le_height'`,
applied to affine opens `Spec R₀ = W ∋ s` and `Spec B = U ⊆ c⁻¹ W` with `σ(W) ⊆ U`, the
localization `B_K = Γ(C_η, j⁻¹ U)` and `L = Γ(Z.P, ν⁻¹ U)`, of rank at most `|G|`
(`AlgebraicGeometry.Scheme.GaloisCover.rankAtStalk_app_le`); the `|G|` points of `L` along the
section are the translates of the rational point of `Z` over `σ(η)`. The sections of `N` over
a basic open of `U` are integral closures
(`AlgebraicGeometry.Scheme.Hom.exists_etale_integralClosure_away`,
`AlgebraicGeometry.Scheme.Hom.etale_fromNormalization_basicOpen`). -/
theorem etaleOverSection_of_two_le_coheight [IsNoetherian D.S] (s : D.S)
    (hs : 2 ≤ Order.coheight s) (H : ∀ s' : D.S, s' ⤳ s → s' ≠ s → D.EtaleOver s') :
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
  -- the prime `q` of `s`, of height at least two, and the prime `ε⁻¹ q` of `σ(s)`
  let q := (hW.primeIdealOf ⟨s, hsW⟩).asIdeal
  have hq : 2 ≤ q.height := by
    let := TopCat.Presheaf.algebra_section_stalk D.S.presheaf ⟨s, hsW⟩
    have := hW.isLocalization_stalk ⟨s, hsW⟩
    have h := IsLocalization.AtPrime.ringKrullDim_eq_height q (D.S.presheaf.stalk s)
    rw [ringKrullDim_stalk_eq_coheight] at h
    have h2 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ q.height := h ▸ WithBot.coe_le_coe.2 hs
    exact WithBot.coe_le_coe.1 h2
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
  -- the étaleness over the strict generizations of `s`
  have hH (Q : Ideal Γ(D.C, U)) (hQ : Q.IsPrime) (hQP : Q ≤ q.comap ε)
      (hQq : Q.comap (algebraMap Γ(D.S, W) Γ(D.C, U)) ≠ q) : ∃ h ∉ Q,
        ∃ (B' L' : Type u) (_ : CommRing B') (_ : CommRing L') (_ : Algebra Γ(D.C, U) B')
          (_ : IsLocalization.Away h B') (_ : Algebra Γ(D.Z.P, D.ν ⁻¹ᵁ U) L')
          (_ : IsLocalization.Away (algebraMap Γ(D.C, U) Γ(D.Z.P, D.ν ⁻¹ᵁ U) h) L')
          (_ : Algebra B' L') (_ : Algebra Γ(D.C, U) L') (_ : IsScalarTower Γ(D.C, U) B' L')
          (_ : IsScalarTower Γ(D.C, U) Γ(D.Z.P, D.ν ⁻¹ᵁ U) L'),
          Algebra.Etale B' (integralClosure B' L') := by
    have hyσ : hU.fromSpec (⟨Q, hQ⟩ : PrimeSpectrum Γ(D.C, U)) ⤳ D.σ s := by
      rw [← hP]
      exact ((PrimeSpectrum.le_iff_specializes _ _).1 hQP).map hU.fromSpec.continuous
    have hcy : D.c (hU.fromSpec (⟨Q, hQ⟩ : PrimeSpectrum Γ(D.C, U))) ⤳ s := by
      have := hyσ.map D.c.continuous
      rwa [c_σ] at this
    have hne : D.c (hU.fromSpec (⟨Q, hQ⟩ : PrimeSpectrum Γ(D.C, U))) ≠ s := by
      intro hys
      apply hQq
      have h1 := congrArg (fun m ↦ m (⟨Q, hQ⟩ : PrimeSpectrum Γ(D.C, U)))
        (IsAffineOpen.SpecMap_appLE_fromSpec D.c hW hU hUW)
      simp only [Scheme.Hom.comp_apply] at h1
      replace h1 := (h1.trans hys).trans (hW.fromSpec_primeIdealOf ⟨s, hsW⟩).symm
      have := hW.isOpenImmersion_fromSpec
      exact congrArg PrimeSpectrum.asIdeal (hW.fromSpec.isOpenEmbedding.injective h1)
    have hEt := (D.etaleOver_iff _).1 (H _ hcy hne)
    have hyU : hU.fromSpec (⟨Q, hQ⟩ : PrimeSpectrum Γ(D.C, U)) ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]
      exact Set.mem_range_self _
    obtain ⟨h, hyh, hle⟩ := D.ν.fromNormalization.exists_basicOpen_le_etaleLocus hU hyU
      fun x hx ↦ hEt x (by rw [hx])
    have hhQ : h ∉ Q := by
      have : (⟨Q, hQ⟩ : PrimeSpectrum Γ(D.C, U)) ∈
          hU.fromSpec ⁻¹ᵁ D.C.basicOpen h := hyh
      rwa [hU.fromSpec_preimage_basicOpen, PrimeSpectrum.mem_basicOpen] at this
    exact ⟨h, hhQ, D.ν.exists_etale_integralClosure_away hU hνU h
      (Scheme.Hom.etale_of_le_etaleLocus hle)⟩
  -- the commutative algebra
  have := functionField_isFractionRing_of_isAffineOpen D.S W hW
  have hrank (p : PrimeSpectrum Γ(D.Cη, D.j ⁻¹ᵁ U)) :
      Module.rankAtStalk (R := Γ(D.Cη, D.j ⁻¹ᵁ U)) Γ(D.Z.P, D.ν ⁻¹ᵁ U) p ≤
        Nat.card G :=
    D.Z.rankAtStalk_app_le hjU p
  obtain ⟨g, hg, hE⟩ := RingTheory.DepthTwo.exists_etale_integralClosure_of_two_le_height'
    (Bk := Γ(D.Cη, D.j ⁻¹ᵁ U)) (L := Γ(D.Z.P, D.ν ⁻¹ᵁ U)) ε q hq hrank hH φ hφ
    hφinj
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

/-- Step of the proof of blueprint `sbc-thm-spreading-finite-etale-galois` (depth at least two,
extension over the fibre; proof of the claim in [Stacks 0EYJ]): over a Noetherian base, at a
point `s` of codimension at least two, if the normalization `N ⟶ C` is étale over all strict
generizations of `s` and over `σ(s)`, it is étale over all of `C_s`.

Proof. This is `AlgebraicGeometry.Scheme.SpreadingDatum.etaleOver_of_etaleOverSection`: the
étale locus `E` of `N ⟶ C` contains `C_U` (`U` the punctured spectrum of `𝒪_{S,s}`) and the
points over `σ(s)`, hence the generic point of the irreducible fibre `C_s`, so `E ∩ C_s` is dense
in `C_s`. By [Stacks 0EYB] (applied over `Spec 𝒪_{S,s}`, whose points of depth at most one lie
in `U`; through `AlgebraicGeometry.Scheme.Hom.mem_etaleLocus_fromNormalization_of_smooth`),
`N|_E` extends to a finite étale `C`-scheme, which is normal and hence equal to `N`. -/
theorem etaleOver_of_two_le_coheight [IsNoetherian D.S] (s : D.S)
    (hs : 2 ≤ Order.coheight s) (H : ∀ s' : D.S, s' ⤳ s → s' ≠ s → D.EtaleOver s')
    (hsec : D.EtaleOverSection s) : D.EtaleOver s :=
  D.etaleOver_of_etaleOverSection
    (D.ne_genericPoint_of_coheight_ne_zero fun h ↦ by simp [h] at hs) H hsec

end AlgebraicGeometry.Scheme.SpreadingDatum
