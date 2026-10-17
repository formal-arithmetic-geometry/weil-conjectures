/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.ArtinSchreierDual
public import WeilConjectures.DeligneLaumon.AffineLine.RamifiedAtInfinity
public import WeilConjectures.SixFunctors.ProEtale.Adic.IrreducibleLisseQuotients

/-!
# The geometric linear characters are pairwise distinct

For `a ∈ k̄` let `ℒ_{ψ(a x)} = (a ·)^* ℒ_ψ` be the geometric linear Artin–Schreier sheaf on
`𝔸¹_{k̄}`. On the geometric fibre `Ū` of a dense open `U₀ ⊆ 𝔸¹`:

- `ℒ_{ψ(a x)}|_Ū` has rank one, hence is an irreducible local system
  (`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isIrreducibleAdicLocalSystem_linearCharacter`);
- for `ψ ≠ 1` and `a ≠ b` the restrictions `ℒ_{ψ(a x)}|_Ū` and `ℒ_{ψ(b x)}|_Ū` are not
  isomorphic (`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isEmpty_iso_linearCharacter`).

For the second statement we pull an isomorphism back to the punctured disc at `∞`. Over an
algebraic closure `L` of `k̄((t))` the Artin–Schreier covers `u^q - u = a / t` and
`u^q - u = b / t` have points `u₁`, `u₂`, and some inertia element `σ` translates them by `c₁`
and `c₂` with `ψ(c₁) ≠ ψ(c₂)`: take `u₂ = u₁ + w` with `w^q - w = (b - a) / t` and `σ` moving `w`
by `c₀`, `ψ(c₀) ≠ 1`
(`AlgebraicGeometry.exists_pair_comp_geometricArtinSchreierMap_eq_laurentPoint`).
So `σ` acts on the two (rank one) fibres by different scalars
(`AlgebraicGeometry.ProEtale.isEmpty_iso_of_twist`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀]


section Pair

variable (k₀)

/-- In a field `L` receiving the finite field `k₀`, the solutions of `x ^ q = x`, `q = #k₀`, are
the elements of `k₀`. -/
lemma exists_apply_eq_of_pow_card_eq {L : Type*} [Field L] (ι : k₀ →+* L) {x : L}
    (hx : x ^ Nat.card k₀ = x) : ∃ c, ι c = x := by
  classical
  have := Fintype.ofFinite k₀
  by_contra! h
  have hq : 1 < Nat.card k₀ := Finite.one_lt_card
  have hP : (Polynomial.X ^ Nat.card k₀ - Polynomial.X : Polynomial L) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero L hq
  have hsub : insert x (Finset.univ.image ι) ⊆
      (Polynomial.X ^ Nat.card k₀ - Polynomial.X : Polynomial L).roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hx
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hy
      rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hcard := (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _))
  rw [Finset.card_insert_of_notMem (by simpa using h),
    Finset.card_image_of_injective _ ι.injective, Finset.card_univ,
    FiniteField.X_pow_card_sub_X_natDegree_eq L hq, Nat.card_eq_fintype_card] at hcard
  omega

local notation "K̄" => LaurentSeries (AlgebraicClosure k₀)

local notation "L̄" => AlgebraicClosure (LaurentSeries (AlgebraicClosure k₀))

local notation "Ā" => Scheme.Hom.geometricFiber (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

/-- **Inertia at infinity on two Artin–Schreier covers.** For `a ≠ b` in `k̄` and `c₀ ∈ k₀`,
there are roots `u₁`, `u₂` of `u^q - u = a / t` and `u^q - u = b / t` in an algebraic closure
`L` of `K = k̄((t))` and a `K`-automorphism `σ` of `L` translating them by `c₁` and `c₂ = c₁ + c₀`
in `k₀`: take `u₂ = u₁ + w` for a root `w` of `w^q - w = (b - a) / t` moved by `c₀`. -/
lemma exists_algEquiv_artinSchreier_pair {a b : AlgebraicClosure k₀} (hab : a ≠ b) (c₀ : k₀) :
    ∃ (u₁ u₂ : L̄) (σ : L̄ ≃ₐ[K̄] L̄) (c₁ c₂ : k₀),
      u₁ ^ Nat.card k₀ - u₁ = algebraMap K̄ L̄ (HahnSeries.single (-1) a) ∧
      u₂ ^ Nat.card k₀ - u₂ = algebraMap K̄ L̄ (HahnSeries.single (-1) b) ∧
      σ u₁ = u₁ + algebraMap K̄ L̄ (HahnSeries.C (algebraMap k₀ (AlgebraicClosure k₀) c₁)) ∧
      σ u₂ = u₂ + algebraMap K̄ L̄ (HahnSeries.C (algebraMap k₀ (AlgebraicClosure k₀) c₂)) ∧
      c₂ = c₁ + c₀ := by
  set ι : k₀ →+* L̄ :=
    (algebraMap K̄ L̄).comp (HahnSeries.C.comp (algebraMap k₀ (AlgebraicClosure k₀)))
  have := Fintype.ofFinite k₀
  obtain ⟨p, hp⟩ := CharP.exists k₀
  have : Fact p.Prime := ⟨CharP.char_is_prime k₀ p⟩
  have : CharP L̄ p := charP_of_injective_ringHom ι.injective p
  obtain ⟨m, -, hm⟩ := FiniteField.card k₀ p
  have hqc : Nat.card k₀ = p ^ (m : ℕ) := Nat.card_eq_fintype_card.trans hm
  obtain ⟨u₁, hu₁⟩ := exists_pow_card_sub_eq k₀ L̄ (algebraMap K̄ L̄ (HahnSeries.single (-1) a))
  obtain ⟨w, hw⟩ :=
    exists_pow_card_sub_eq k₀ L̄ (algebraMap K̄ L̄ (HahnSeries.single (-1) (b - a)))
  obtain ⟨σ, hσ⟩ := LaurentSeries.exists_algEquiv_apply_eq_add_C_of_pow_sub_eq_single_of_ne_zero
    (sub_ne_zero.2 hab.symm) L̄ hw c₀
  have hσ₁ : (σ u₁ - u₁) ^ Nat.card k₀ = σ u₁ - u₁ := by
    have h := congrArg σ hu₁
    rw [map_sub, map_pow, AlgEquiv.commutes] at h
    rw [hqc, sub_pow_char_pow, ← hqc]
    linear_combination h - hu₁
  obtain ⟨c₁, hc₁⟩ := exists_apply_eq_of_pow_card_eq k₀ ι hσ₁
  have hc₁' : algebraMap K̄ L̄ (HahnSeries.C (algebraMap k₀ (AlgebraicClosure k₀) c₁)) =
      σ u₁ - u₁ := hc₁
  refine ⟨u₁, u₁ + w, σ, c₁, c₁ + c₀, hu₁, ?_, ?_, ?_, rfl⟩
  · have hb : HahnSeries.single (-1 : ℤ) b =
        HahnSeries.single (-1) a + HahnSeries.single (-1) (b - a) := by
      rw [← HahnSeries.single_add, add_sub_cancel]
    rw [hqc, add_pow_char_pow, ← hqc, hb, map_add, ← hu₁, ← hw]
    ring
  · rw [hc₁']
    ring
  · rw [map_add, hσ, map_add, map_add, map_add, hc₁']
    ring

/-- A root `u` of `u^q - u = b / t` in `L` is a point of `𝔸¹_{k̄}` lifting the point `x = b / t`
along the geometric Artin–Schreier map. -/
lemma geometricPoint_comp_geometricArtinSchreierMap {b : AlgebraicClosure k₀} {u : L̄}
    (hu : u ^ Nat.card k₀ - u = algebraMap K̄ L̄ (HahnSeries.single (-1) b)) :
    affineLine.geometricPoint k₀ L̄ u ≫ affineLine.geometricArtinSchreierMap k₀ =
      Spec.map (CommRingCat.ofHom (algebraMap K̄ L̄)) ≫ laurentPoint k₀ b := by
  rw [laurentPoint_eq, affineLine.specMap_comp_geometricPoint k₀ K̄ (algebraMap K̄ L̄)
    (fun x ↦ (IsScalarTower.algebraMap_apply (AlgebraicClosure k₀) K̄ L̄ x).symm)]
  refine affineLine.geometricPoint_comp_geometricFiberMap k₀ _ _ _ _ _ ?_
  let := Fintype.ofFinite k₀
  rw [affineLine.artinSchreierMap, AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_pow,
    AffineSpace.homOfVector_appTop_coord, ← map_pow, ← map_sub, Fintype.card_eq_nat_card, hu]

omit [Finite k₀] in
/-- A `K`-automorphism `σ` of `L` translating `u` by `c ∈ k₀` moves the point `x = u` of `𝔸¹_{k̄}`
by the translation `σ̄_c`. -/
lemma specMap_algEquiv_comp_geometricPoint {u : L̄} (σ : L̄ ≃ₐ[K̄] L̄) {c : k₀}
    (hσ : σ u = u + algebraMap K̄ L̄ (HahnSeries.C (algebraMap k₀ (AlgebraicClosure k₀) c))) :
    Spec.map (CommRingCat.ofHom (σ : L̄ →+* L̄)) ≫ affineLine.geometricPoint k₀ L̄ u =
      affineLine.geometricPoint k₀ L̄ u ≫ (affineLine.geometricTranslationIso k₀ c).hom := by
  rw [affineLine.specMap_comp_geometricPoint k₀ L̄ (σ : L̄ →+* L̄) fun x ↦ by
      rw [IsScalarTower.algebraMap_apply (AlgebraicClosure k₀) K̄ L̄ x]
      exact σ.commutes _]
  refine (affineLine.geometricPoint_comp_geometricFiberMap k₀ L̄ (affineLine.translation k₀ c)
    (comp_over _ _) u _ ?_).symm
  rw [affineLine.translation, AffineSpace.translation_appTop_coord, map_add,
    affineLine.homOfVector_appTop_appTop, AffineSpace.homOfVector_appTop_coord, ← map_add]
  congr 1
  rw [IsScalarTower.algebraMap_apply k₀ K̄ L̄ c, HahnSeries.algebraMap_apply',
    PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C]
  exact hσ.symm

/-- **Two Artin–Schreier covers over the punctured disc at infinity.** For `a ≠ b` in `k̄` and
`c₀ ∈ k₀`, the points `x = a / t` and `x = b / t` of `𝔸¹_{k̄}` lift along `ĀS` to points `z₁`,
`z₂` over an algebraic closure `L` of `K = k̄((t))`, and some `K`-automorphism of `L` moves them
by translations `σ̄_{c₁}` and `σ̄_{c₂}` with `c₂ = c₁ + c₀`. -/
theorem exists_pair_comp_geometricArtinSchreierMap_eq_laurentPoint {a b : AlgebraicClosure k₀}
    (hab : a ≠ b) (c₀ : k₀) :
    ∃ (z₁ z₂ : Spec (.of L̄) ⟶ Ā) (σ : Spec (.of L̄) ⟶ Spec (.of L̄)) (c₁ c₂ : k₀),
      z₁ ≫ affineLine.geometricArtinSchreierMap k₀ =
        Spec.map (CommRingCat.ofHom (algebraMap K̄ L̄)) ≫ laurentPoint k₀ a ∧
      z₂ ≫ affineLine.geometricArtinSchreierMap k₀ =
        Spec.map (CommRingCat.ofHom (algebraMap K̄ L̄)) ≫ laurentPoint k₀ b ∧
      σ ≫ Spec.map (CommRingCat.ofHom (algebraMap K̄ L̄)) =
        Spec.map (CommRingCat.ofHom (algebraMap K̄ L̄)) ∧
      σ ≫ z₁ = z₁ ≫ (affineLine.geometricTranslationIso k₀ c₁).hom ∧
      σ ≫ z₂ = z₂ ≫ (affineLine.geometricTranslationIso k₀ c₂).hom ∧ c₂ = c₁ + c₀ := by
  obtain ⟨u₁, u₂, σ, c₁, c₂, hu₁, hu₂, hσ₁, hσ₂, hc⟩ :=
    exists_algEquiv_artinSchreier_pair k₀ hab c₀
  refine ⟨_, _, Spec.map (CommRingCat.ofHom (σ : L̄ →+* L̄)), c₁, c₂,
    geometricPoint_comp_geometricArtinSchreierMap k₀ hu₁,
    geometricPoint_comp_geometricArtinSchreierMap k₀ hu₂, ?_,
    specMap_algEquiv_comp_geometricPoint k₀ σ hσ₁,
    specMap_algEquiv_comp_geometricPoint k₀ σ hσ₂, hc⟩
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun x ↦ σ.commutes x

end Pair

variable {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace ProEtale

/-- On the spectrum of a field, the global sections of a sheaf isomorphic to a pullback of `ℚ̄_ℓ`
are the multiples of a single one. -/
lemma exists_forall_eq_smul_of_iso_upperStar {L : Type u} [Field L] {V : Scheme.{u}}
    (z : Spec (.of L) ⟶ V)
    {M : Sheaf (Scheme.ProEt.topology (Spec (.of L))) (WeilCoefficients.{u} l)}
    (Φ : (z)^*[WeilCoefficients.{u} l].obj (adicConstantSheaf l V) ≅ M) :
    ∃ v₀ : (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of L))) (WeilCoefficients.{u} l)).obj M,
      ∀ x, ∃ c : ULift.{u + 1} (PadicAlgCl l), x = c • v₀ := by
  refine ⟨((Sheaf.Γ _ _).map Φ.hom).hom (((globalSectionsToUpperStar _ z).app
    (adicConstantSheaf l V)).hom (oneGlobalSection V)), fun x ↦ ?_⟩
  obtain ⟨c, hc⟩ := exists_eq_smul_globalSectionsToUpperStar_oneGlobalSection z
    (((Sheaf.Γ _ _).map Φ.inv).hom x)
  refine ⟨c, ?_⟩
  rw [← map_smul, ← hc, ← ModuleCat.comp_apply, ← Functor.map_comp, Φ.inv_hom_id,
    CategoryTheory.Functor.map_id, ModuleCat.id_apply]

/-- **Twisted sections with different characters.** In the situation of
`AlgebraicGeometry.ProEtale.not_epi_of_mono_biproduct_unit_of_twist`, let `z₁, z₂ : S ⟶ Y` be two
points lifting along `w` after the base change `π`, on which `σ` restricts to `g₁` and `g₂`
acting on the section of `θ` by `χ₁ ≠ χ₂`. Then `z₁^* N ≇ z₂^* N`: the sections of
`π^* z₂^* N` form a line on which the germ along `σ` acts by `χ₂`, while an isomorphism would
carry a nonzero section with eigenvalue `χ₁` into it. -/
theorem isEmpty_iso_of_twist {S Y Y' : Scheme.{u}} {L : Type u} [Field L]
    {π : Spec (.of L) ⟶ S} {σ : Spec (.of L) ⟶ Spec (.of L)} (hσ : σ ≫ π = π)
    {w : Y' ⟶ Y} {g₁ g₂ : Y' ⟶ Y'} (hg₁ : g₁ ≫ w = w) (hg₂ : g₂ ≫ w = w)
    {z₁ z₂ : S ⟶ Y} {z₁' z₂' : Spec (.of L) ⟶ Y'} (hz₁ : z₁' ≫ w = π ≫ z₁)
    (hz₂ : z₂' ≫ w = π ≫ z₂) (hσz₁ : σ ≫ z₁' = z₁' ≫ g₁) (hσz₂ : σ ≫ z₂' = z₂' ≫ g₂)
    {N : AdicSheaf l Y} (θ : AdicSheaf.unit l Y' ≅ (w)^*ᵃ[l].obj N) {χ₁ χ₂ : PadicAlgCl l}
    (hχ : χ₁ ≠ χ₂)
    (hθ₁ : (factorGerm (WeilCoefficients.{u} l) hg₁ N.X).hom (globalSectionOfModHom θ.hom) =
      ULift.up χ₁ • globalSectionOfModHom θ.hom)
    (hθ₂ : (factorGerm (WeilCoefficients.{u} l) hg₂ N.X).hom (globalSectionOfModHom θ.hom) =
      ULift.up χ₂ • globalSectionOfModHom θ.hom) :
    IsEmpty ((z₁)^*ᵃ[l].obj N ≅ (z₂)^*ᵃ[l].obj N) := by
  refine ⟨fun F ↦ ?_⟩
  let A := WeilCoefficients.{u} l
  obtain ⟨e₁, he₁0, he₁⟩ := exists_ne_zero_factorGerm_eq_smul_of_twist hσ hg₁ hz₁ hσz₁ θ χ₁ hθ₁
  obtain ⟨e₂, he₂0, he₂⟩ := exists_ne_zero_factorGerm_eq_smul_of_twist hσ hg₂ hz₂ hσz₂ θ χ₂ hθ₂
  obtain ⟨v₀, hv₀⟩ := exists_forall_eq_smul_of_iso_upperStar
    (M := (π)^*[A].obj ((z₂)^*[A].obj N.X)) z₂'
    ((z₂')^*[A].mapIso ((AdicSheaf.forget Y').mapIso θ) ≪≫ (upperStarCompIso A hz₂).app N.X)
  -- the germ along `σ` acts on the line of sections of `π^* z₂^* N` by `χ₂`
  obtain ⟨d, hd⟩ := hv₀ e₂
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact he₂0 (by rw [hd, zero_smul])
  have hv : (factorGerm A hσ _).hom v₀ = ULift.up χ₂ • v₀ := by
    have h : d • ((factorGerm A hσ _).hom v₀ - ULift.up χ₂ • v₀) = 0 := by
      rw [smul_sub, ← map_smul, ← hd, he₂, hd, smul_comm, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h).resolve_left hd0)
  -- transport `e₁` along `F`
  let Fs : (z₁)^*[A].obj N.X ≅ (z₂)^*[A].obj N.X := (AdicSheaf.forget S).mapIso F
  let F' := (Sheaf.Γ _ A).mapIso ((π)^*[A].mapIso Fs)
  have hf0 : F'.hom.hom e₁ ≠ 0 := fun h ↦
    he₁0 ((ConcreteCategory.bijective_of_isIso F'.hom).1 (h.trans (map_zero _).symm))
  have hfe : (factorGerm A hσ _).hom (F'.hom.hom e₁) = ULift.up χ₁ • F'.hom.hom e₁ := by
    have hn := congrArg (fun φ ↦ φ.hom e₁) (factorGerm_naturality A hσ Fs.hom)
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, he₁, map_smul] at hn
    exact hn
  obtain ⟨c, hc⟩ := hv₀ (F'.hom.hom e₁)
  have h2 : (factorGerm A hσ _).hom (F'.hom.hom e₁) = ULift.up χ₂ • F'.hom.hom e₁ := by
    rw [hc, map_smul, hv, smul_comm]
  have h3 : (ULift.up χ₁ - ULift.up χ₂) • F'.hom.hom e₁ = 0 := by
    rw [sub_smul, ← hfe, ← h2, sub_self]
  exact hχ (congrArg ULift.down (sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hf0)))

end ProEtale

/-- The geometric linear character `ℒ_{ψ(a x)}` has rank one: its stalks are lines. By lissity
the rank is that of `ℒ_{ψ(0 · x)} ≅ ℚ̄_ℓ`. -/
theorem finrank_geometricStalkFunctor_upperStar_geometricSMul_artinSchreier
    (ψ : AddChar k₀ (PadicAlgCl l)) (a : AlgebraicClosure k₀) {Y : Scheme.{u}}
    (g : Y ⟶ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    {K : Type u} [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ Y) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((ProEtale.geometricStalkFunctor l s).obj
        ((g)^*ᵃ[l].obj ((affineLine.geometricSMul k₀ a)^*ᵃ[l].obj
          (artinSchreier ψ 1).obj.carrier)))) = 1 := by
  obtain ⟨e₀⟩ := WeilSheaf.nonempty_iso_upperStar_geometricSMul_zero_artinSchreier (l := l) ψ 1
  set L := (artinSchreier ψ 1).obj.carrier
  have hL : ProEtale.IsAdicLisseSheaf L := isLisse_artinSchreier ψ 1
  have h₁ := ProEtale.finrank_geometricStalkFunctor_upperStar g
    ((affineLine.geometricSMul k₀ a)^*ᵃ[l].obj L) s
  have h₂ := ProEtale.finrank_geometricStalkFunctor_upperStar (affineLine.geometricSMul k₀ a) L
    (s ≫ g)
  have h₃ := hL.finrank_geometricStalkFunctor_eq ((s ≫ g) ≫ affineLine.geometricSMul k₀ a)
    ((s ≫ g) ≫ affineLine.geometricSMul k₀ 0)
  have h₄ := ProEtale.finrank_geometricStalkFunctor_upperStar (affineLine.geometricSMul k₀ 0) L
    (s ≫ g)
  have h₅ : Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((ProEtale.geometricStalkFunctor l (s ≫ g)).obj
        ((affineLine.geometricSMul k₀ 0)^*ᵃ[l].obj L))) =
      Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
        ((ProEtale.geometricStalkFunctor l (s ≫ g)).obj (ProEtale.AdicSheaf.unit l _))) :=
    ((ProEtale.geometricStalkFunctor l (s ≫ g) ⋙
      WeilCoefficients.toModuleCat l).mapIso e₀).toLinearEquiv.finrank_eq
  have h₆ := ProEtale.finrank_geometricStalkFunctor_unit (l := l) (s ≫ g)
  omega

/-- A geometric point of a nonempty scheme, at the algebraic closure of the residue field of some
point. -/
lemma exists_geometricPoint (Y : Scheme.{u}) [Nonempty Y] :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K), Nonempty (Spec (.of K) ⟶ Y) := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  exact ⟨AlgebraicClosure (Y.residueField y), inferInstance, inferInstance,
    ⟨Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
        Y.fromSpecResidueField y⟩⟩

namespace WeilSheaf.LisseOnDenseOpen

variable (D : LisseOnDenseOpen k₀ l) (ψ : AddChar k₀ (PadicAlgCl l))

/-- The restriction `ℒ_{ψ(a x)}|_Ū` of a geometric linear character to the geometric fibre of the
open `U₀`. -/
noncomputable abbrev linearCharacter (a : AlgebraicClosure k₀) :
    ProEtale.AdicSheaf l (D.U ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  (Scheme.Hom.geometricFiberMap D.j (comp_over D.j _))^*ᵃ[l].obj
    ((affineLine.geometricSMul k₀ a)^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier)

/-- `ℒ_{ψ(a x)}|_Ū` is an irreducible local system: it is lisse of rank one on the irreducible
`Ū`. -/
theorem isIrreducibleAdicLocalSystem_linearCharacter (a : AlgebraicClosure k₀) :
    ProEtale.IsIrreducibleAdicLocalSystem (D.linearCharacter ψ a) := by
  have := D.irreducibleSpace_geometricFiber
  obtain ⟨K, _, _, ⟨s⟩⟩ := exists_geometricPoint (D.U ↘ Spec (CommRingCat.of k₀)).geometricFiber
  exact ProEtale.IsAdicLisseSheaf.isIrreducibleAdicLocalSystem_of_finrank_eq_one
    (ProEtale.IsAdicLisseSheaf.upperStar _
      (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreier ψ 1))) s
    (finrank_geometricStalkFunctor_upperStar_geometricSMul_artinSchreier ψ a _ s)

/-- **The geometric linear characters are pairwise distinct** on `Ū`: for `ψ ≠ 1` and `a ≠ b`
in `k̄`, `ℒ_{ψ(a x)}|_Ū ≇ ℒ_{ψ(b x)}|_Ū`. Pull an isomorphism back to the punctured disc at `∞`,
along a point `x = 1 / t` of `Ū`: over an algebraic closure `L` of `k̄((t))` the Artin–Schreier
covers `u^q - u = a / t` and `u^q - u = b / t` have points moved by some inertia element `σ`
through translations `c₁` and `c₂ = c₁ - c₀` with `ψ(c₀) ≠ 1`, so `σ` acts on the trivialised
fibres by the distinct scalars `ψ(-c₁)` and `ψ(-c₂)`. -/
theorem isEmpty_iso_linearCharacter (hψ : ψ ≠ 1) {a b : AlgebraicClosure k₀} (hab : a ≠ b) :
    IsEmpty (D.linearCharacter ψ a ≅ D.linearCharacter ψ b) := by
  refine ⟨fun e ↦ ?_⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, ψ c₀ ≠ 1 := by
    by_contra! h
    exact hψ (DFunLike.ext _ _ fun x ↦ by rw [h x, AddChar.one_apply])
  have : Nonempty (affineLine k₀) :=
    ⟨(laurentPoint k₀ 1 ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)
      (IsLocalRing.closedPoint (LaurentSeries (AlgebraicClosure k₀)))⟩
  have : Nonempty D.U := D.j.denseRange.nonempty
  obtain ⟨zU, hzU⟩ := exists_comp_geometricFiberMap_eq_laurentPoint k₀ D.j
  have hpt (c : AlgebraicClosure k₀) : (zU ≫ Scheme.Hom.geometricFiberMap D.j (comp_over D.j _) ≫
      affineLine.geometricSMul k₀ c) ≫
        Scheme.Hom.geometricFiberMap (affineLine.smul k₀ 1) (comp_over _ _) =
      laurentPoint k₀ c := by
    rw [Category.assoc, Category.assoc, reassoc_of% hzU,
      reassoc_of% laurentPoint_comp_geometricSMul, laurentPoint_comp_geometricFiberMap_smul]
    simp
  -- `zU^* ℒ_{ψ(c x)}|_Ū` is the pullback of `ℒ_ψ` along the point `x = c / t`
  let G (c : AlgebraicClosure k₀) : (zU)^*ᵃ[l].obj (D.linearCharacter ψ c) ≅
      (laurentPoint k₀ c)^*ᵃ[l].obj (affineLine.artinSchreierImage l ψ) :=
    (zU)^*ᵃ[l].mapIso (ProEtale.adicUpperStarCompObjIso rfl _) ≪≫
      ProEtale.adicUpperStarCompObjIso rfl _ ≪≫ ProEtale.adicUpperStarCompObjIso (hpt c) _ ≪≫
      (laurentPoint k₀ c)^*ᵃ[l].mapIso (affineLine.artinSchreierCarrierIso ψ)
  obtain ⟨z₁, z₂, σ, c₁, c₂, hz₁, hz₂, hσ, hσ₁, hσ₂, hc⟩ :=
    exists_pair_comp_geometricArtinSchreierMap_eq_laurentPoint k₀ hab (-c₀)
  have hχ : ψ (-c₁) ≠ ψ (-c₂) := by
    intro h
    have h0 : ψ (-c₁) ≠ 0 := fun h0 ↦ by
      simpa [h0] using (AddChar.map_add_eq_mul ψ (-c₁) c₁).symm
    rw [hc, neg_add, neg_neg, AddChar.map_add_eq_mul] at h
    exact hc₀ (mul_left_cancel₀ h0 (h.symm.trans (mul_one _).symm))
  exact (ProEtale.isEmpty_iso_of_twist hσ
    (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c₁)
    (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c₂) hz₁ hz₂ hσ₁ hσ₂
    (affineLine.artinSchreierTrivialization l ψ) hχ
    (affineLine.germ_artinSchreierTrivialization ψ c₁)
    (affineLine.germ_artinSchreierTrivialization ψ c₂)).false
    ((G a).symm ≪≫ (zU)^*ᵃ[l].mapIso e ≪≫ G b)

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry
