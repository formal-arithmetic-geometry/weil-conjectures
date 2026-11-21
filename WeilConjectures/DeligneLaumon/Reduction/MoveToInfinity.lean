/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineIrreducible
public import WeilConjectures.DeligneLaumon.AffineLine.DenseOpen
public import WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary
public import WeilConjectures.DeligneLaumon.Reduction.CompactSupport
public import WeilConjectures.WeilSheaf.CohomologySequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.PointCount
public import WeilConjectures.WeilSheaf.BaseChangeField.CompactSupport
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.OpenClosedTriangle
public import WeilConjectures.WeilSheaf.StalkUpperStar
public import WeilConjectures.WeilSheaf.UpperStarId

/-!
# Moving a lisse point to infinity

## Main statements

- `AlgebraicGeometry.WeilSheaf.exists_surjective_compactlySupportedCohomology_one_of_finite_compl`:
  for an open immersion `j : U ⟶ X` with finite complement, `H_c^1(U, j^*F) → H_c^1(X, F)` is
  surjective.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

/-- **Localization in degree one.** Let `j : U ⟶ X` be an open immersion of separated
`k₀`-schemes of finite type whose complement is finite. For a Weil sheaf `F` on `X`, the open–closed
triangle gives a Frobenius-equivariant surjection `H_c^1(U, j^*F) ↠ H_c^1(X, F)`: the next term
`H_c^1(Z, i^*F)` of the long exact sequence vanishes, the complement `Z` being finite. -/
theorem exists_surjective_compactlySupportedCohomology_one_of_finite_compl
    {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hj : (Set.range j.base)ᶜ.Finite) (F : WeilSheaf k₀ l X) :
    ∃ g : (((WeilSheaf.upperStar j).obj F).compactlySupportedCohomology 1).carrier →ₗ[PadicAlgCl l]
        (F.compactlySupportedCohomology 1).carrier,
      Function.Surjective g ∧
        ∀ x, g ((((WeilSheaf.upperStar j).obj F).compactlySupportedCohomology 1).frobenius x) =
          (F.compactlySupportedCohomology 1).frobenius (g x) := by
  obtain ⟨Z, _, i, _, _, hrange, _⟩ :=
    Scheme.Opens.exists_isClosedImmersion_isFinite_compl (k₀ := k₀) j.opensRange
      (by simpa using hj)
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by simpa using hrange
  have : IsSeparated (Z ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : QuasiCompact (Z ↘ Spec (CommRingCat.of k₀)) := inferInstance
  -- the open–closed triangle `RΓ_c(U, j^*F) → RΓ_c(X, F) → RΓ_c(Z, i^*F) →`
  obtain ⟨α, β, γ, hT⟩ := WeilComplex.exists_distTriang_derivedLowerShriek_structure_openClosed
    j i hij (WeilSheaf.toComplex.obj F)
  set T := Triangle.mk α β γ
  let EU := WeilComplex.cohomologyEquivOfIso
    ((WeilComplex.derivedLowerShriek k₀ l (U ↘ Spec (CommRingCat.of k₀))).mapIso
      ((WeilSheaf.toComplexCompUpperStarIso j).app F)) 1
  let EZ := WeilComplex.cohomologyEquivOfIso
    ((WeilComplex.derivedLowerShriek k₀ l (Z ↘ Spec (CommRingCat.of k₀))).mapIso
      ((WeilSheaf.toComplexCompUpperStarIso i).app F)) 1
  -- the finite complement has no cohomology in degree one
  have hZ : Subsingleton (T.obj₃.cohomologyFrobeniusModule 1).carrier := by
    have h := WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite
      ((WeilSheaf.upperStar i).obj F) one_ne_zero
    exact ⟨fun a b ↦ EZ.toLinearEquiv.injective (h.elim _ _)⟩
  refine ⟨WeilComplex.cohomologyMap T.mor₁ 1 ∘ₗ EU.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · intro z
    obtain ⟨x, hx⟩ := (WeilComplex.exact_cohomologyMap T 1 hT z).1 (Subsingleton.elim _ _)
    refine ⟨EU.toLinearEquiv x, ?_⟩
    change WeilComplex.cohomologyMap T.mor₁ 1 (EU.toLinearEquiv.symm (EU.toLinearEquiv x)) = z
    rw [LinearEquiv.symm_apply_apply, hx]
  · intro x
    change WeilComplex.cohomologyMap T.mor₁ 1 (EU.symm.toLinearEquiv _) =
      (T.obj₂.cohomologyFrobeniusModule 1).frobenius
        (WeilComplex.cohomologyMap T.mor₁ 1 (EU.symm.toLinearEquiv x))
    erw [EU.symm.map_frobenius x, WeilComplex.cohomologyMap_frobenius]

end WeilSheaf


/-- Let `i : V ⟶ X` be a morphism of `K`-schemes and `j : V ⟶ 𝔸¹_K` an open immersion which
extends over infinity: there are an open `W'` of `ℙ¹_K` containing `∞` with `W' ∩ 𝔸¹_K = j(V)`
and a morphism `ψ : W' ⟶ X` restricting to `i` on `j(V)`. Then the pullback `i^*G` of a lisse
Weil sheaf `G` on `X` is unramified at infinity: it extends to the lisse sheaf `ψ^*G` on `W'`. -/
theorem WeilSheaf.IsLisse.isUnramifiedAtInfinity_upperStar {K : Type u} [Field K] [Finite K]
    [Fact (ringChar K ≠ l)] {V X : Scheme.{u}} [V.Over (Spec (CommRingCat.of K))]
    [X.Over (Spec (CommRingCat.of K))] {G : WeilSheaf K l X} (hG : G.IsLisse) (i : V ⟶ X)
    [i.IsOver (Spec (CommRingCat.of K))] (j : V ⟶ affineLine K) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of K))] (W' : (ProjectiveLine (Spec (CommRingCat.of K))).Opens)
    (ψ : W'.toScheme ⟶ X) [ψ.IsOver (Spec (CommRingCat.of K))]
    (hW' : ProjectiveLine.affineChart (Spec (CommRingCat.of K)) ⁻¹ᵁ W' = j.opensRange)
    (htop : (ProjectiveLine.affineChart (Spec (CommRingCat.of K))).opensRange ⊔ W' = ⊤)
    (hψ : ∀ h, IsOpenImmersion.lift W'.ι (j ≫ ProjectiveLine.affineChart _) h ≫ ψ = i) :
    ((WeilSheaf.upperStar i).obj G).IsUnramifiedAtInfinity j := by
  have hr : Set.range (j ≫ ProjectiveLine.affineChart (Spec (CommRingCat.of K))).base ⊆
      Set.range W'.ι.base := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : j t ∈ ProjectiveLine.affineChart (Spec (CommRingCat.of K)) ⁻¹ᵁ W' := hW' ▸ ⟨t, rfl⟩
    exact this
  refine ⟨W', hW', htop, (WeilSheaf.upperStar ψ).obj G, hG.upperStar ψ, ⟨?_⟩⟩
  -- the two lifts only differ in proofs; going through `upperStarCongr` keeps the kernel from
  -- unfolding `WeilSheaf.upperStar`
  exact (WeilSheaf.upperStarCongr
      (ψ := IsOpenImmersion.lift W'.ι (j ≫ ProjectiveLine.affineChart _) hr) (by rfl)).app _ ≪≫
    ((WeilSheaf.upperStarCompIso _ ψ).app G).symm ≪≫ (WeilSheaf.upperStarCongr (hψ hr)).app G

/-- **Moving a point of an open of the projective line to infinity.** Let `W₀` be a nonempty open
of `ℙ¹_{k₀}`, embedded by `c`. There are a finite extension `K` of `k₀` and an open `V` of
`W_K = W₀ ×_{k₀} K` with finite complement, embedded by `i`, together with a dense open
immersion `j : V ⟶ 𝔸¹_K` which extends over infinity: there are an open `W'` of `ℙ¹_K`
containing `∞` with `W' ∩ 𝔸¹_K = j(V)` and a morphism `ψ : W' ⟶ W_K` restricting to `i` on
`j(V)`. Indeed, `W₀` has a rational point `s` over the residue field `K` of a closed point, and
the composite of a translation of `𝔸¹_K` and of the chart at infinity sends `s` to `∞`. -/
theorem ProjectiveLine.exists_isOpenImmersion_affineLine_baseChangeField {W : Scheme.{u}}
    [W.Over (Spec (CommRingCat.of k₀))] [Nonempty W]
    (c : W ⟶ ProjectiveLine (Spec (CommRingCat.of k₀))) [IsOpenImmersion c]
    [c.IsOver (Spec (CommRingCat.of k₀))] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k₀ K) (_ : Module.Finite k₀ K)
      (V : Scheme.{u}) (_ : V.Over (Spec (CommRingCat.of K)))
      (i : V ⟶ W.baseChangeField k₀ K) (_ : IsOpenImmersion i)
      (_ : i.IsOver (Spec (CommRingCat.of K)))
      (j : V ⟶ affineLine K) (_ : IsOpenImmersion j) (_ : j.IsOver (Spec (CommRingCat.of K)))
      (W' : (ProjectiveLine (Spec (CommRingCat.of K))).Opens)
      (ψ : W'.toScheme ⟶ W.baseChangeField k₀ K) (_ : ψ.IsOver (Spec (CommRingCat.of K))),
      Dense (Set.range j.base) ∧ (Set.range i.base)ᶜ.Finite ∧
        ProjectiveLine.affineChart (Spec (CommRingCat.of K)) ⁻¹ᵁ W' = j.opensRange ∧
        (ProjectiveLine.affineChart (Spec (CommRingCat.of K))).opensRange ⊔ W' = ⊤ ∧
        ∀ h, IsOpenImmersion.lift W'.ι (j ≫ ProjectiveLine.affineChart _) h ≫ ψ = i := by
  have hc := comp_over c (Spec (CommRingCat.of k₀))
  have : LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k₀)) := by rw [← hc]; infer_instance
  -- the part `W_A` of `W` in the affine chart is a nonempty open
  set ι₀ := ProjectiveLine.affineChart (Spec (CommRingCat.of k₀))
  let WA : W.Opens := c ⁻¹ᵁ ι₀.opensRange
  have hWA : (WA : Set W).Nonempty := by
    obtain ⟨y⟩ := ‹Nonempty W›
    obtain ⟨_, ⟨z, rfl⟩, ⟨t, ht⟩⟩ := nonempty_preirreducible_inter c.opensRange.isOpen
      ι₀.opensRange.isOpen ⟨_, y, rfl⟩
      ⟨_, (AffineSpace.zeroSection PUnit.{u + 1} _).base (IsLocalRing.closedPoint k₀), rfl⟩
    exact ⟨z, t, ht⟩
  -- a closed point `x` of `W_A`, with residue field `K`
  have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace (W ↘ Spec (CommRingCat.of k₀))
  obtain ⟨x, hxWA, hxc⟩ := nonempty_inter_closedPoints hWA WA.isOpen.isLocallyClosed
  obtain ⟨K, _, _, _, p, hp, hpx⟩ : ∃ (K : Type u) (_ : Field K) (_ : Algebra k₀ K)
      (_ : Module.Finite k₀ K) (p : Spec (CommRingCat.of K) ⟶ W),
      p ≫ W ↘ Spec (CommRingCat.of k₀) = Spec.map (CommRingCat.ofHom (algebraMap k₀ K)) ∧
        p.base (IsLocalRing.closedPoint K) = x := by
    let := ((W ↘ Spec (CommRingCat.of k₀)).residueFieldAlgebraMap x).toAlgebra
    exact ⟨W.residueField x, inferInstance, this,
      (W ↘ Spec (CommRingCat.of k₀)).finite_residueField_of_isClosed x hxc,
      W.fromSpecResidueField x,
      ((W ↘ Spec (CommRingCat.of k₀)).specMap_residueFieldAlgebraMap x).symm,
      W.fromSpecResidueField_apply x _⟩
  have : Finite K := Module.finite_of_finite k₀
  -- the base change `W_K` of `W`, and the `K`-rational point `s_W` of `W_K` over `x`
  set WK := W.baseChangeField k₀ K
  let π : WK ⟶ W := pullback.fst _ _
  let sW : Spec (CommRingCat.of K) ⟶ WK := pullback.lift p (𝟙 _) (by simpa using hp)
  have hsW : sW ≫ WK ↘ Spec (CommRingCat.of K) = 𝟙 _ := pullback.lift_snd _ _ _
  have hsWπ : sW ≫ π = p := pullback.lift_fst _ _ _
  -- the part `O` of `W_K` over `W_A`, and the point `s` of `O`
  let O : WK.Opens := π ⁻¹ᵁ WA
  have hsO : Set.range sW.base ⊆ Set.range O.ι.base := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change π.base (sW.base t) ∈ WA
    rw [← Scheme.Hom.comp_apply, hsWπ, Subsingleton.elim t (IsLocalRing.closedPoint K)]
    have h : p.base (IsLocalRing.closedPoint K) = x := hpx
    change p.base (IsLocalRing.closedPoint K) ∈ (WA : Set W)
    rw [h]
    exact hxWA
  let s : Spec (CommRingCat.of K) ⟶ O := IsOpenImmersion.lift O.ι sW hsO
  have hs : s ≫ O.ι = sW := IsOpenImmersion.lift_fac _ _ _
  -- the open immersion `u : W_A ⟶ 𝔸¹_{k₀}` and its base change `ρ : O ⟶ 𝔸¹_K`
  have hWAι : Set.range (WA.ι ≫ c).base ⊆ Set.range ι₀.base := by
    rintro _ ⟨t, rfl⟩
    exact t.2
  let u : WA.toScheme ⟶ 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)) :=
    IsOpenImmersion.lift ι₀ (WA.ι ≫ c) hWAι
  have hu : u ≫ 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀) =
      WA.toScheme ↘ Spec (CommRingCat.of k₀) := by
    rw [← ProjectiveLine.affineChart_over, IsOpenImmersion.lift_fac_assoc, Category.assoc, hc]
    rfl
  have hsq : IsPullback (O.toScheme ↘ Spec (CommRingCat.of K)) (π ∣_ WA)
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) (WA.toScheme ↘ Spec (CommRingCat.of k₀)) :=
    ((isPullback_morphismRestrict π WA).paste_vert (IsPullback.of_hasPullback _ _)).flip
  have hA := (AffineSpace.isPullback_map (n := PUnit.{u + 1})
    (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))).flip
  let ρ : O.toScheme ⟶ 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of K)) :=
    hA.lift (O.toScheme ↘ Spec (CommRingCat.of K)) ((π ∣_ WA) ≫ u) (by rw [Category.assoc, hu, hsq.w])
  have hρ : ρ ≫ 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) =
      O.toScheme ↘ Spec (CommRingCat.of K) := hA.lift_fst _ _ _
  have hρsq : IsPullback ρ (π ∣_ WA) (AffineSpace.map PUnit.{u + 1}
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) u :=
    IsPullback.of_right (by rwa [hρ, hu]) (hA.lift_snd _ _ _) hA
  have : IsOpenImmersion ρ := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsOpenImmersion) hρsq.flip inferInstance
  -- `ρ(s)` is a rational point `a`; translating by `-a` and inverting sends it to `∞`
  let a : Γ(Spec (CommRingCat.of K), ⊤) := (s ≫ ρ).appTop (AffineSpace.coord (Spec (CommRingCat.of K)) PUnit.unit)
  let v : PUnit.{u + 1} → Γ(Spec (CommRingCat.of K), ⊤) := fun _ ↦ a
  let τ := AffineSpace.translation (-v)
  have : IsIso τ := ⟨AffineSpace.translation v, by
    rw [← AffineSpace.translation_add, neg_add_cancel, AffineSpace.translation_zero], by
    rw [← AffineSpace.translation_add, add_neg_cancel, AffineSpace.translation_zero]⟩
  have hτ : τ ≫ 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) =
      𝔸(PUnit.{u + 1}; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) :=
    AffineSpace.translation_over _
  let e : O.toScheme ⟶ ProjectiveLine (Spec (CommRingCat.of K)) :=
    ρ ≫ τ ≫ ProjectiveLine.infinityChart (Spec (CommRingCat.of K))
  have he : e ≫ ProjectiveLine (Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) =
      O.toScheme ↘ Spec (CommRingCat.of K) := by
    simp only [e, Category.assoc, ProjectiveLine.infinityChart_over, hτ, hρ]
  have hsρ : s ≫ ρ = AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of K))) v := by
    refine AffineSpace.hom_ext ?_ fun _ ↦ by rw [AffineSpace.homOfVector_appTop_coord]
    rw [Category.assoc, hρ, AffineSpace.homOfVector_over, ← Scheme.Opens.ι_comp_over,
      ← Category.assoc, hs]
    exact hsW
  have hse : s ≫ e = ProjectiveLine.infinity (Spec (CommRingCat.of K)) := by
    rw [ProjectiveLine.infinity, ← Category.assoc, ← Category.assoc, hsρ]
    congr 1
    refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
    · rw [Category.assoc, hτ, AffineSpace.homOfVector_over, AffineSpace.zeroSection_over]
    · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.translation_appTop_coord,
        map_add, AffineSpace.homOfVector_appTop_coord, AffineSpace.zeroSection_appTop_coord,
        ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over,
        Scheme.Hom.id_appTop, CommRingCat.id_apply]
      simp [v]
  have : e.IsOver (Spec (CommRingCat.of K)) := ⟨he⟩
  have : IsOpenImmersion e := by dsimp only [e]; infer_instance
  -- the open `V = O \ {s}` of `O` mapping into the affine chart, and `j : V ⟶ 𝔸¹_K`
  let ιK := ProjectiveLine.affineChart (Spec (CommRingCat.of K))
  let Ω : O.toScheme.Opens := e ⁻¹ᵁ ιK.opensRange
  have hΩ : Set.range (Ω.ι ≫ e).base ⊆ Set.range ιK.base := by
    rintro _ ⟨t, rfl⟩
    exact t.2
  let jV : Ω.toScheme ⟶ 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of K)) :=
    IsOpenImmersion.lift ιK (Ω.ι ≫ e) hΩ
  have hjV : jV ≫ ιK = Ω.ι ≫ e := IsOpenImmersion.lift_fac _ _ _
  have hΩne : (Ω : Set O.toScheme).Nonempty := by
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := nonempty_preirreducible_inter e.opensRange.isOpen
      ιK.opensRange.isOpen ⟨_, s.base (IsLocalRing.closedPoint K), rfl⟩
      ⟨_, (AffineSpace.zeroSection PUnit.{u + 1} _).base (IsLocalRing.closedPoint K), rfl⟩
    exact ⟨z, hz⟩
  let iV : Ω.toScheme ⟶ WK := Ω.ι ≫ O.ι
  refine ⟨K, inferInstance, inferInstance, inferInstance, Ω.toScheme, inferInstance, iV,
    inferInstance, inferInstance, jV, inferInstance, inferInstance, e.opensRange,
    e.isoOpensRange.inv ≫ O.ι, ⟨?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, Scheme.Opens.ι_comp_over, ← he, ← Category.assoc,
      Scheme.Hom.isoOpensRange_inv_comp, Scheme.Opens.ι_comp_over]
  · obtain ⟨z, hz⟩ := hΩne
    exact jV.isOpenEmbedding.isOpen_range.dense ⟨_, ⟨z, hz⟩, rfl⟩
  · -- the complement of `V` in `W_K` lies over `W \ W_A ⊆ c⁻¹{∞}`, or is the point `e⁻¹{∞}`
    have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) := by
      rw [IsFinite.SpecMap_iff]
      exact RingHom.finite_algebraMap.mpr inferInstance
    have : IsFinite π := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite)
      (IsPullback.of_hasPullback _ _).flip this
    have hWAc : ((WA : Set W)ᶜ).Finite := by
      refine ((Set.finite_singleton (ProjectiveLine.infinity (Spec (CommRingCat.of k₀))
        (IsLocalRing.closedPoint k₀))).preimage c.isOpenEmbedding.injective.injOn).subset ?_
      intro y hy
      rw [Set.mem_preimage, ← ProjectiveLine.compl_opensRange_affineChart_eq_singleton]
      exact hy
    have hΩc : ((Ω : Set O.toScheme)ᶜ).Finite := by
      refine ((Set.finite_singleton (ProjectiveLine.infinity (Spec (CommRingCat.of K))
        (IsLocalRing.closedPoint K))).preimage e.isOpenEmbedding.injective.injOn).subset ?_
      intro y hy
      rw [Set.mem_preimage, ← ProjectiveLine.compl_opensRange_affineChart_eq_singleton]
      exact hy
    refine ((π.finite_preimage hWAc).union (hΩc.image O.ι.base)).subset ?_
    intro y hy
    by_cases hyO : y ∈ O
    · exact Or.inr ⟨⟨y, hyO⟩, fun hΩ ↦ hy ⟨⟨⟨y, hyO⟩, hΩ⟩, rfl⟩, rfl⟩
    · exact Or.inl hyO
  · apply le_antisymm
    · rintro y ⟨z, hz⟩
      have hzΩ : z ∈ Ω := ⟨y, hz.symm⟩
      refine ⟨⟨z, hzΩ⟩, ιK.isOpenEmbedding.injective ?_⟩
      change (jV ≫ ιK).base ⟨z, hzΩ⟩ = _
      rw [hjV]
      exact hz
    · rintro _ ⟨t, rfl⟩
      change ιK.base (jV.base t) ∈ e.opensRange
      rw [← Scheme.Hom.comp_apply, hjV]
      exact ⟨_, rfl⟩
  · rw [eq_top_iff]
    intro y _
    by_cases hy : y ∈ ιK.opensRange
    · exact Or.inl hy
    · right
      have hy' : y ∈ ((ιK.opensRange : Set (ProjectiveLine (Spec (CommRingCat.of K)))))ᶜ := hy
      rw [ProjectiveLine.compl_opensRange_affineChart_eq_singleton] at hy'
      rw [hy']
      refine ⟨s.base (IsLocalRing.closedPoint K), ?_⟩
      change (s ≫ e).base _ = _
      rw [hse]
  · intro h
    rw [← Category.assoc]
    congr 1
    rw [← cancel_mono e, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp,
      IsOpenImmersion.lift_fac, hjV]

/-- Bundle a lisse Weil sheaf on a dense open of the affine line, with its weight and a
surjection of its `H_c^1`, into a `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen`. -/
private theorem exists_lisseOnDenseOpen_of_surjective {K : Type u} [Field K] [Finite K]
    [Fact (ringChar K ≠ l)] (ι : PadicAlgCl l →+* ℂ) {w : ℝ}
    (M : FrobeniusModule.{u + 1, 0} (PadicAlgCl l)) {V : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of K))] [IsSeparated (V ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (V ↘ Spec (CommRingCat.of K))] (j : V ⟶ affineLine K) [IsOpenImmersion j]
    [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of K))] [IsDominant j] (G : WeilSheaf K l V)
    (hG : G.IsLisse) (hGw : G.IsPunctuallyPureOfWeight ι w) (hGinf : G.IsUnramifiedAtInfinity j)
    (f : (G.compactlySupportedCohomology 1).carrier →ₗ[PadicAlgCl l] M.carrier)
    (hf : Function.Surjective f)
    (hfF : ∀ x, f ((G.compactlySupportedCohomology 1).frobenius x) = M.frobenius (f x)) :
    ∃ D : WeilSheaf.LisseOnDenseOpen K l,
      D.sheaf.IsPunctuallyPureOfWeight ι w ∧ D.IsUnramifiedAtInfinity ∧
      ∃ f : (D.sheaf.compactlySupportedCohomology 1).carrier →ₗ[PadicAlgCl l] M.carrier,
        Function.Surjective f ∧
          ∀ x, f ((D.sheaf.compactlySupportedCohomology 1).frobenius x) = M.frobenius (f x) :=
  ⟨⟨V, j, G, hG⟩, hGw, hGinf, f, hf, hfF⟩

/-- **Moving a lisse point to infinity.** Let `W₀` be a nonempty open of the projective line
`ℙ¹_{k₀}`, embedded by `c`, and let `F` be a lisse Weil sheaf on `W₀`, punctually `ι`-pure of
weight `w`. There are a finite extension `K` of `k₀`, a dense open `V₀` of the affine line `𝔸¹_K`
with a lisse Weil sheaf `G` on it, punctually `ι`-pure of weight `w` and unramified at infinity,
and a surjection `H_c^1(V, G) ↠ H_c^1(W, F)` carrying the geometric Frobenius of `K` to the
`[K : k₀]`-th power of that of `k₀`. -/
theorem exists_surjective_compactlySupportedCohomology_one_of_projectiveLine
    (ι : PadicAlgCl l →+* ℂ) {W : Scheme.{u}} [W.Over (Spec (CommRingCat.of k₀))] [Nonempty W]
    (c : W ⟶ ProjectiveLine (Spec (CommRingCat.of k₀))) [IsOpenImmersion c]
    [c.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact (W ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l W) (hF : F.IsLisse) {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w) :
    -- `W ↘ Spec k₀` is separated and locally of finite type, being `c` followed by `ℙ¹ ↘ Spec k₀`
    haveI : IsSeparated (W ↘ Spec (CommRingCat.of k₀)) := by rw [← comp_over c]; infer_instance
    haveI : LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over c]; infer_instance
    ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : Algebra k₀ K) (_ : Fact (ringChar K ≠ l))
      (D : WeilSheaf.LisseOnDenseOpen K l),
      D.sheaf.IsPunctuallyPureOfWeight ι w ∧ D.IsUnramifiedAtInfinity ∧
      ∃ f : (D.sheaf.compactlySupportedCohomology 1).carrier →ₗ[PadicAlgCl l]
          (F.compactlySupportedCohomology 1).carrier,
        Function.Surjective f ∧
          ∀ x, f ((D.sheaf.compactlySupportedCohomology 1).frobenius x) =
            ((F.compactlySupportedCohomology 1).powFrobenius (Module.finrank k₀ K)).frobenius
              (f x) := by
  have hc := comp_over c (Spec (CommRingCat.of k₀))
  have : IsSeparated (W ↘ Spec (CommRingCat.of k₀)) := by rw [← hc]; infer_instance
  have : LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k₀)) := by rw [← hc]; infer_instance
  obtain ⟨K, _, _, _, V, _, i, _, _, j, _, _, W', ψ, _, hj, hfin, hW', htop, hψ⟩ :=
    ProjectiveLine.exists_isOpenImmersion_affineLine_baseChangeField c
  have : Finite K := Module.finite_of_finite k₀
  have : Fact (ringChar K ≠ l) := ⟨Algebra.ringChar_eq k₀ K ▸ Fact.out⟩
  have hi := comp_over i (Spec (CommRingCat.of K))
  have : IsSeparated (V ↘ Spec (CommRingCat.of K)) := by rw [← hi]; infer_instance
  have : LocallyOfFiniteType (V ↘ Spec (CommRingCat.of K)) := by rw [← hi]; infer_instance
  have : QuasiCompact (V ↘ Spec (CommRingCat.of K)) := by rw [← hi]; infer_instance
  have : IsLocallyNoetherian (affineLine K) :=
    LocallyOfFiniteType.isLocallyNoetherian (affineLine K ↘ Spec (CommRingCat.of K))
  have : IsDominant j := ⟨hj⟩
  -- the restriction `F_K` of `F` to `W_K`, and the localization sequence for `V ⊆ W_K`
  obtain ⟨FK, hFKl, hFKp, hFKc⟩ := WeilSheaf.exists_compactlySupportedCohomology_baseChangeField K F
  obtain ⟨g, hg, hgF⟩ :=
    WeilSheaf.exists_surjective_compactlySupportedCohomology_one_of_finite_compl i hfin FK
  obtain ⟨E⟩ := hFKc 1
  have hinf := (hFKl hF).isUnramifiedAtInfinity_upperStar i j W' ψ hW' htop hψ
  obtain ⟨D, h₁, h₂, h₃⟩ := exists_lisseOnDenseOpen_of_surjective ι
    ((F.compactlySupportedCohomology 1).powFrobenius (Module.finrank k₀ K)) j _
    ((hFKl hF).upperStar i) ((hFKp ι w hw).upperStar i) hinf
    (E.toLinearEquiv.toLinearMap ∘ₗ g) (E.toLinearEquiv.surjective.comp hg) fun x ↦ by
      change E.toLinearEquiv (g _) = _
      rw [hgF, E.map_frobenius]
      rfl
  exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, D, h₁, h₂, h₃⟩

end AlgebraicGeometry
