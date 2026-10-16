/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Estimate
public import WeilConjectures.AlgebraicGeometry.Curve.GmCohomology
public import WeilConjectures.AlgebraicGeometry.Curve.Jacobian
public import WeilConjectures.AlgebraicGeometry.Curve.Kummer
public import WeilConjectures.AlgebraicGeometry.Curve.BaseChange
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnityPullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback

/-!
# The cohomology of `μₙ` on a smooth proper curve

Let `C` be a smooth proper connected curve of genus `g` over an algebraically closed field `k`
and `n ≥ 1` prime to `char k`. The long exact sequence of the Kummer sequence
`0 → μₙ → 𝔾ₘ → 𝔾ₘ → 0`, with `H¹(C, 𝔾ₘ) = Pic(C)` and `Hᵠ(C, 𝔾ₘ) = 0` for `q ≥ 2`, gives
canonical identifications

* `H⁰(C, μₙ) = μₙ(k)`,
* `H¹(C, μₙ) = Pic(C)[n] = J[n](k)`, of order `n^{2g}`,
* `H²(C, μₙ) = ℤ/n`, the Kummer boundary of a line bundle `L` going to `deg L mod n`,
* `Hᵠ(C, μₙ) = 0` for `q > 2`.

## Main statements

- `AlgebraicGeometry.IsConnectedCurve.sheafH_rootsOfUnitySheaf_of_isProper`: the computation.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open AlgebraicGeometry.Etale

namespace AlgebraicGeometry

namespace Scheme

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- An integer which is nonzero in a field `k` is invertible on every `k`-scheme. -/
lemma isUnit_natCast_of_ne_zero (f : C ⟶ Spec (.of k)) {n : ℕ} (hn : (n : k) ≠ 0) :
    IsUnit (n : Γ(C, ⊤)) := by
  simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

/-- The sheaf `μₙ` of `n`-th roots of unity is killed by `n`, so it is a torsion sheaf. -/
lemma isTorsion_rootsOfUnitySheaf (X : Scheme.{u}) {n : ℕ} (hn : 0 < n) :
    (X.rootsOfUnitySheaf n).IsTorsion := by
  refine isTorsion_of_nsmul_id_eq_zero hn ((cancel_mono (kernel.ι (n • 𝟙 X.gmSheaf))).1 ?_)
  rw [Preadditive.nsmul_comp, Category.id_comp, zero_comp,
    ← Category.comp_id (kernel.ι (n • 𝟙 X.gmSheaf)), ← Preadditive.comp_nsmul, kernel.condition]

/-- `H⁰` of `μₙ` injects into `H⁰` of `𝔾ₘ`, the global units. -/
lemma injective_map_rootsOfUnitySheafι_zero (X : Scheme.{u}) (n : ℕ) :
    Function.Injective (Sheaf.H.map (X.rootsOfUnitySheafι n) 0) := by
  intro x y h
  obtain ⟨a, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x
  obtain ⟨b, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 y
  rw [Sheaf.H.map_apply, Sheaf.H.map_apply, Abelian.Ext.mk₀_comp_mk₀,
    Abelian.Ext.mk₀_comp_mk₀] at h
  rw [(cancel_mono (X.rootsOfUnitySheafι n)).1 ((Abelian.Ext.mk₀_bijective _ _).1 h)]

end Scheme

namespace IsConnectedCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- Blueprint `det-curveestimate-canonical-mu`, parts 1–4: the canonical identifications of the
cohomology of `μₙ` on a smooth proper curve.

Let `C` be a smooth proper connected curve of genus `g` over an algebraically closed field `k`
and `n ≥ 1` prime to `char k`. Write `δ² : Pic(C) = H¹(C, 𝔾ₘ) → H²(C, μₙ)` for the Kummer
boundary (`AlgebraicGeometry.Scheme.kummerδ₁`). Then

1. `H⁰(C, μₙ) ≅ μₙ(k)`; the map `H⁰(C, μₙ) → H⁰(C, 𝔾ₘ) = 𝒪(C)ˣ` is injective;
2. the map `H¹(C, μₙ) → H¹(C, 𝔾ₘ) = Pic(C)` is injective with image `Pic(C)[n]`, a group of
   order `n^{2g}`;
3. `δ²` is surjective, and there is a unique isomorphism `degₙ : H²(C, μₙ) ≅ ℤ/n` with
   `degₙ (δ² [L]) = deg L mod n` for every line bundle `L`;
4. `Hᵠ(C, μₙ) = 0` for `q > 2`.

The Kummer sequence is exact, `H¹(C, 𝔾ₘ) = Pic(C)` and `Hᵠ(C, 𝔾ₘ) = 0` for `q ≥ 2`
(`AlgebraicGeometry.IsCurve.sheafH_gmSheaf_of_smooth`); global units are `n`-divisible, so the
long exact sequence gives `H¹(C, μₙ) = Pic(C)[n]` and `H²(C, μₙ) = Pic(C)/n`. The degree
sequence `0 → Pic⁰(C) → Pic(C) → ℤ → 0` with `Pic⁰(C) = J(k)` `n`-divisible with `n`-torsion
`(ℤ/n)^{2g}` gives the rest. -/
theorem sheafH_rootsOfUnitySheaf_of_isProper (f : C ⟶ Spec (.of k)) [IsConnectedCurve f]
    [Smooth f] [IsProper f] (n : ℕ) (hn : (n : k) ≠ 0) :
    (Function.Injective (Sheaf.H.map (C.rootsOfUnitySheafι n) 0) ∧
        Nonempty (Sheaf.H (C.rootsOfUnitySheaf n) 0 ≃+ Additive (rootsOfUnity n k))) ∧
      (Function.Injective (Sheaf.H.map (C.rootsOfUnitySheafι n) 1) ∧
        (Sheaf.H.map (C.rootsOfUnitySheafι n) 1).range =
          AddSubgroup.torsionBy C.CohomologicalPicardGroup n ∧
        Nat.card (Sheaf.H (C.rootsOfUnitySheaf n) 1) = n ^ (2 * f.genus)) ∧
      (Function.Surjective (C.kummerδ₁ n (Scheme.isUnit_natCast_of_ne_zero f hn)) ∧
        ∃! d : Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+ ZMod n, ∀ L : C.Pic,
          d (C.kummerδ₁ n (Scheme.isUnit_natCast_of_ne_zero f hn)
            (Scheme.Pic.toCohomologicalPicardGroup C L)) = (f.picDegree L : ZMod n)) ∧
      ∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H (C.rootsOfUnitySheaf n) q) := by
  have := IsConnectedCurve.connectedSpace' f
  have hn' := Scheme.isUnit_natCast_of_ne_zero f hn
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn Nat.cast_zero)
  have : NeZero n := ⟨hn0.ne'⟩
  have : NeZero (n : k) := ⟨hn⟩
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
    IsConnectedCurve.smoothOfRelativeDimension_one f
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  refine ⟨⟨C.injective_map_rootsOfUnitySheafι_zero n, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- `H⁰(C, μₙ) ≅ H⁰(C, ℤ/n) ≅ ℤ/n ≅ μₙ(k)`
    obtain ⟨e₁⟩ := Scheme.nonempty_addEquiv_sheafH_constantZMod_rootsOfUnitySheaf f n hn 0
    obtain ⟨e₂⟩ := IsCurve.nonempty_addEquiv_sheafH_constantZMod_zero f n hn
    obtain ⟨-, -, ζ, hζ, -⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} k n
    exact ⟨e₁.symm.trans (e₂.trans (hζ.isUnit_unit NeZero.out).zmodAddEquivRootsOfUnity)⟩
  · -- the global units are `n`-divisible, so the Kummer map on them vanishes
    obtain ⟨hα, hαβ, -⟩ := C.exact_sheafH_rootsOfUnitySheaf_one n hn'
    let := (Scheme.globalSectionsRingHom k (X := C)).toAlgebra
    have : Module.Finite k Γ(C, ⊤) := Scheme.finite_globalSectionsRingHom_of_isProper
    have hdiv := IsAlgClosed.exists_pow_eq_of_finite (A := Γ(C, ⊤)) hn
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨u, rfl⟩ := (hαβ x).1 hx
    obtain ⟨v, hv⟩ := hdiv (Additive.toMul u)
    have hu : u ∈ (C.kummerδ₀ n hn').ker := by
      rw [hα]
      exact ⟨Additive.ofMul v, by simp [← ofMul_pow, hv]⟩
    exact hu
  · exact (C.exact_sheafH_rootsOfUnitySheaf_one n hn').2.2
  · -- `H¹(C, μₙ) ≅ H¹(C, ℤ/n) ≅ (ℤ/n)^{2g}`
    obtain ⟨e₁⟩ := Scheme.nonempty_addEquiv_sheafH_constantZMod_rootsOfUnitySheaf f n hn 1
    obtain ⟨e₂⟩ := IsCurve.nonempty_addEquiv_sheafH_constantZMod_one f n hn
    rw [Nat.card_congr (e₁.symm.trans e₂).toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  · -- `δ²` is surjective since `Br(C) = 0`
    obtain ⟨hker, hαβ, -⟩ := C.exact_sheafH_rootsOfUnitySheaf_two n hn'
    have := IsCurve.subsingleton_cohomologicalBrauerGroup_of_smooth f
    have hsurj : Function.Surjective (C.kummerδ₁ n hn') :=
      fun y ↦ (hαβ y).1 (Subsingleton.elim _ _)
    refine ⟨hsurj, ?_⟩
    -- the degree modulo `n` on `H¹(C, 𝔾ₘ) = Pic(C)`
    let eP := Scheme.Pic.toCohomologicalPicardGroupAddEquiv C
    let D : C.CohomologicalPicardGroup →+ ZMod n :=
      { toFun := fun c ↦ ((Scheme.picDegreeHom k C (eP.symm c).toMul).toAdd : ZMod n)
        map_zero' := by simp
        map_add' := fun a b ↦ by simp [Int.cast_add] }
    have hD (L : C.Pic) :
        D (Scheme.Pic.toCohomologicalPicardGroup C L) = (f.picDegree L : ZMod n) := by
      have : eP.symm (Scheme.Pic.toCohomologicalPicardGroup C L) = .ofMul L :=
        eP.symm_apply_eq.2 rfl
      simp only [D, AddMonoidHom.coe_mk, ZeroHom.coe_mk, this, toMul_ofMul]
      rfl
    obtain ⟨-, -, hdiv⟩ := Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient (C := C) hn
    have : Nonempty C := IsConnectedCurve.nonempty f
    obtain ⟨L₁, hL₁⟩ := Scheme.surjective_picDegreeHom (k := k) (C := C) (Multiplicative.ofAdd 1)
    have hdegL₁ : (Scheme.picDegreeHom k C L₁).toAdd = 1 := by rw [hL₁]; rfl
    have hDe (x : Additive C.Pic) :
        D (eP x) = ((Scheme.picDegreeHom k C x.toMul).toAdd : ZMod n) := by
      simp [D]
    have hDker : D.ker = (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (n : ℤ)).range := by
      ext c
      obtain ⟨x, rfl⟩ := eP.surjective c
      rw [AddMonoidHom.mem_ker, hDe, ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [AddMonoidHom.mem_range, zsmulAddGroupHom_apply]
      constructor
      · rintro ⟨m, hm⟩
        have hy : x.toMul * L₁ ^ (-((n : ℤ) * m)) ∈ picardZero k C := by
          rw [MonoidHom.mem_ker, map_mul, map_zpow]
          apply Multiplicative.toAdd.injective
          rw [toAdd_mul, toAdd_zpow, hm, hdegL₁]
          simp
        obtain ⟨z, hz⟩ := hdiv ⟨_, hy⟩
        have hz' : (z : C.Pic) ^ n = x.toMul * L₁ ^ (-((n : ℤ) * m)) :=
          congrArg Subtype.val hz
        refine ⟨eP (.ofMul ((z : C.Pic) * L₁ ^ m)), ?_⟩
        rw [← map_zsmul]
        congr 1
        apply Additive.toMul.injective
        rw [toMul_zsmul, toMul_ofMul, mul_zpow, zpow_natCast, hz', ← zpow_mul, mul_assoc,
          ← zpow_add, mul_comm (m : ℤ), neg_add_cancel, zpow_zero, mul_one]
      · rintro ⟨c, hc⟩
        obtain ⟨y, rfl⟩ := eP.surjective c
        rw [← map_zsmul] at hc
        rw [← eP.injective hc, toMul_zsmul, map_zpow, toAdd_zpow]
        exact ⟨_, zsmul_eq_mul _ _⟩
    have hDsurj : Function.Surjective D := by
      intro a
      refine ⟨eP (.ofMul (L₁ ^ (a.val : ℤ))), ?_⟩
      rw [hDe, toMul_ofMul, map_zpow, toAdd_zpow, hdegL₁, smul_eq_mul, mul_one, Int.cast_natCast,
        ZMod.natCast_zmod_val]
    let eα := QuotientAddGroup.quotientKerEquivOfSurjective _ hsurj
    let eD := QuotientAddGroup.quotientKerEquivOfSurjective D hDsurj
    let d : Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+ ZMod n :=
      eα.symm.trans ((QuotientAddGroup.quotientAddEquivOfEq (hker.trans hDker.symm)).trans eD)
    have hd (c : C.CohomologicalPicardGroup) : d (C.kummerδ₁ n hn' c) = D c := by
      simp only [d, AddEquiv.trans_apply]
      rw [show eα.symm (C.kummerδ₁ n hn' c) = (c : _ ⧸ _) from eα.symm_apply_eq.2 rfl]
      rfl
    refine ⟨d, fun L ↦ (hd _).trans (hD L), fun d' hd' ↦ ?_⟩
    ext y
    obtain ⟨c, rfl⟩ := hsurj y
    obtain ⟨L, rfl⟩ := (Scheme.Pic.toCohomologicalPicardGroup C).surjective c
    rw [hd', hd, hD]
  · intro q hq
    exact IsCurve.subsingleton_sheafH_of_three_le f _ (C.isTorsion_rootsOfUnitySheaf hn0) q hq

/-- A morphism of sheaves which is an isomorphism induces bijections on cohomology. -/
lemma _root_.CategoryTheory.Sheaf.H.bijective_map_of_isIso {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [IsIso φ] (q : ℕ) :
    Function.Bijective (Sheaf.H.map φ q) :=
  ((Sheaf.functorH _ q).mapIso (asIso φ)).addCommGroupIsoToAddEquiv.bijective

/-- Blueprint `det-curveestimate-canonical-mu`, part 5: invariance under extension of
algebraically closed fields.

Let `C` be a smooth proper connected curve over an algebraically closed field `k`, let
`k ⊆ k'` be an extension of algebraically closed fields, `π : C_{k'} ⟶ C` the projection and
`n ≥ 1` prime to `char k`. Then the pullback maps `ρᵠ : Hᵠ(C, μₙ) ⟶ Hᵠ(C_{k'}, μₙ)`
(`AlgebraicGeometry.Scheme.rootsOfUnityCohomologyMap`) are bijective, and under the
identifications of `AlgebraicGeometry.IsConnectedCurve.sheafH_rootsOfUnitySheaf_of_isProper`

* `ρ⁰` is the inclusion `μₙ(k) ⟶ μₙ(k')`: on the global units it is the pullback of units
  along `π`;
* `ρ¹` is the restriction of the base change map `π^* : Pic(C) ⟶ Pic(C_{k'})` to `n`-torsion,
  which on `Pic⁰(C) = J(k)` is the base change map `J[n](k) ⟶ J[n](k')`;
* `ρ²` is the identity of `ℤ/n`: `degₙ' ∘ ρ² = degₙ` for the isomorphisms `degₙ` and `degₙ'`
  characterised by `degₙ (δ² [L]) = deg L mod n`.

The pullback commutes with the Kummer sequences, hence with all maps of their long exact
sequences (`AlgebraicGeometry.Scheme.map_kernelι_rootsOfUnityCohomologyMap`,
`AlgebraicGeometry.Scheme.rootsOfUnityCohomologyMap_kummerδ₁`), the identification
`Pic = H¹(-, 𝔾ₘ)` is natural (`AlgebraicGeometry.Scheme.gmCohomologyMap_toCohomologicalPicardGroup`)
and pullback preserves degrees (`AlgebraicGeometry.Scheme.Hom.picDegree_map_baseChangeField`).
Bijectivity follows from the comparison `π^* μₙ ≅ μₙ` and the invariance of the cohomology of
`ℤ/n ≅ μₙ` (`AlgebraicGeometry.IsConnectedCurve.bijective_fieldExtensionCohomologyMap_of_isProper`).
-/
theorem rootsOfUnityCohomologyMap_baseChangeField (f : C ⟶ Spec (.of k)) [IsConnectedCurve f]
    [Smooth f] [IsProper f] (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k'] (n : ℕ)
    (hn : (n : k) ≠ 0) :
    (∀ q, Function.Bijective (Scheme.rootsOfUnityCohomologyMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) n q)) ∧
    (∀ (x : Sheaf.H (C.rootsOfUnitySheaf n) 0) (a : Γ(C, ⊤)ˣ),
      Sheaf.H.equiv₀ _ terminalIsTerminal (Sheaf.H.map (C.rootsOfUnitySheafι n) 0 x) =
        Scheme.gmSection a →
      Sheaf.H.equiv₀ _ terminalIsTerminal
          (Sheaf.H.map (Scheme.rootsOfUnitySheafι _ n) 0 (Scheme.rootsOfUnityCohomologyMap
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) n 0 x)) =
        Scheme.gmSection (Units.map (pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop.hom.toMonoidHom a)) ∧
    (∀ (x : Sheaf.H (C.rootsOfUnitySheaf n) 1) (L : C.Pic),
      Sheaf.H.map (C.rootsOfUnitySheafι n) 1 x = Scheme.Pic.toCohomologicalPicardGroup C L →
      Sheaf.H.map (Scheme.rootsOfUnitySheafι _ n) 1 (Scheme.rootsOfUnityCohomologyMap
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) n 1 x) =
        Scheme.Pic.toCohomologicalPicardGroup _ (Scheme.Pic.map
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) L)) ∧
    ∀ (hC : IsUnit (n : Γ(C, ⊤)))
      (hC' : IsUnit (n : Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤)))
      (d : Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+ ZMod n)
      (d' : Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).rootsOfUnitySheaf
        n) 2 ≃+ ZMod n),
      (∀ L : C.Pic, d (C.kummerδ₁ n hC (Scheme.Pic.toCohomologicalPicardGroup C L)) =
        (f.picDegree L : ZMod n)) →
      (∀ L, d' (Scheme.kummerδ₁ _ n hC' (Scheme.Pic.toCohomologicalPicardGroup _ L)) =
        ((f.baseChangeField k').picDegree L : ZMod n)) →
      ∀ y, d' (Scheme.rootsOfUnityCohomologyMap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) n 2 y) = d y := by
  set π := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))
  have hn0 : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  have hnC := Scheme.isUnit_natCast_of_ne_zero f hn
  refine ⟨fun q ↦ ?_, fun x a hx ↦ ?_, fun x L hx ↦ ?_, fun hC hC' d d' hd hd' y ↦ ?_⟩
  · -- `π^* μₙ ≅ μₙ`, and the cohomology of `μₙ ≅ ℤ/n` is invariant
    have : IsIso (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf n π) :=
      Scheme.isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit n π hnC
    have : NeZero (n : k) := ⟨hn⟩
    obtain ⟨-, -, ζ, hζ, -⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} k n
    let θ := C.constantZModIsoRootsOfUnitySheaf n f hζ
    have hZ := IsConnectedCurve.bijective_fieldExtensionCohomologyMap_of_isProper f k' n hn q
    have hμ : Function.Bijective (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) q) := by
      have h : ⇑(Etale.cohomologyMap π (C.rootsOfUnitySheaf n) q) =
          Sheaf.H.map ((Etale.upperStar AddCommGrpCat.{u + 1} π).map θ.hom) q ∘
            Etale.cohomologyMap π (C.constantZMod n) q ∘ Sheaf.H.map θ.inv q := by
        ext z
        simp only [Function.comp_apply]
        rw [← Etale.cohomologyMap_map, ← Sheaf.H.map_comp_apply, Iso.inv_hom_id,
          Sheaf.H.map_id_apply]
      rw [h]
      exact (Sheaf.H.bijective_map_of_isIso _ q).comp
        (hZ.comp (Sheaf.H.bijective_map_of_isIso _ q))
    exact (Sheaf.H.bijective_map_of_isIso _ q).comp hμ
  · rw [Scheme.map_kernelι_rootsOfUnityCohomologyMap, Scheme.equiv₀_gmCohomologyMap_zero, hx,
      Scheme.gmSectionsPullback_gmSection]
  · rw [Scheme.map_kernelι_rootsOfUnityCohomologyMap, hx,
      Scheme.gmCohomologyMap_toCohomologicalPicardGroup]
  · obtain ⟨-, -, ⟨hsurj, -⟩, -⟩ := sheafH_rootsOfUnitySheaf_of_isProper f n hn
    obtain ⟨c, rfl⟩ := hsurj y
    obtain ⟨L, rfl⟩ := (Scheme.Pic.toCohomologicalPicardGroup C).surjective c
    rw [Scheme.rootsOfUnityCohomologyMap_kummerδ₁ π n _ hC',
      Scheme.gmCohomologyMap_toCohomologicalPicardGroup, hd', hd,
      Scheme.Hom.picDegree_map_baseChangeField]

end IsConnectedCurve

end AlgebraicGeometry
