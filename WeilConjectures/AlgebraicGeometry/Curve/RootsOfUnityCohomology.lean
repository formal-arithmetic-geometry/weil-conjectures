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
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDelta

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

For a morphism `g : X ⟶ Y` we also record the comparison `g^* μₙ ⟶ μₙ` and the compatibility of
the Kummer boundary with pullback.

## Main definitions

- `AlgebraicGeometry.Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf`: `g^* μₙ ⟶ μₙ`.
- `AlgebraicGeometry.Scheme.gmCohomologyMap`, `AlgebraicGeometry.Scheme.rootsOfUnityCohomologyMap`:
  the pullback maps `Hᵠ(Y, 𝔾ₘ) → Hᵠ(X, 𝔾ₘ)` and `Hᵠ(Y, μₙ) → Hᵠ(X, μₙ)`.

## Main statements

- `AlgebraicGeometry.Scheme.rootsOfUnityCohomologyMap_kummerδ₁`: the Kummer boundary commutes
  with pullback.
- `AlgebraicGeometry.IsConnectedCurve.sheafH_rootsOfUnitySheaf_of_isProper`: the computation.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open AlgebraicGeometry.Etale

namespace AlgebraicGeometry

namespace Scheme

section Pullback

variable (X : Scheme.{u}) (n : ℕ) in
/-- The inclusion `μₙ ⟶ 𝔾ₘ` of the sheaf of `n`-th roots of unity. -/
noncomputable abbrev rootsOfUnitySheafι : X.rootsOfUnitySheaf n ⟶ X.gmSheaf :=
  kernel.ι (n • 𝟙 X.gmSheaf)

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ)

/-- The comparison `g^* 𝔾ₘ ⟶ 𝔾ₘ` commutes with the `n`-th power maps. -/
@[reassoc]
lemma map_nsmul_comp_upperStarGmSheafToGmSheaf :
    (g)^*[AddCommGrpCat.{u + 1}].map (n • 𝟙 Y.gmSheaf) ≫ upperStarGmSheafToGmSheaf g =
      upperStarGmSheafToGmSheaf g ≫ (n • 𝟙 X.gmSheaf) := by
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Preadditive.nsmul_comp,
    Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]

/-- The comparison `g^* μₙ ⟶ μₙ` of sheaves of `n`-th roots of unity along `g : X ⟶ Y`: the
restriction of the comparison `g^* 𝔾ₘ ⟶ 𝔾ₘ`
(`AlgebraicGeometry.Scheme.upperStarGmSheafToGmSheaf`). -/
noncomputable def upperStarRootsOfUnitySheafToRootsOfUnitySheaf :
    (g)^*[AddCommGrpCat.{u + 1}].obj (Y.rootsOfUnitySheaf n) ⟶ X.rootsOfUnitySheaf n :=
  kernel.lift _ ((g)^*[AddCommGrpCat.{u + 1}].map (kernel.ι (n • 𝟙 Y.gmSheaf)) ≫
    upperStarGmSheafToGmSheaf g) (by
      rw [Category.assoc, ← map_nsmul_comp_upperStarGmSheafToGmSheaf, ← Category.assoc,
        ← Functor.map_comp, kernel.condition, Functor.map_zero, zero_comp])

@[reassoc (attr := simp)]
lemma upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι :
    upperStarRootsOfUnitySheafToRootsOfUnitySheaf g n ≫ X.rootsOfUnitySheafι n =
      (g)^*[AddCommGrpCat.{u + 1}].map (Y.rootsOfUnitySheafι n) ≫
        upperStarGmSheafToGmSheaf g :=
  kernel.lift_ι _ _ _

/-- The pullback of the Kummer sequence of `Y` maps to the Kummer sequence of `X`. -/
noncomputable def kummerSequenceUpperStarMap :
    (Y.kummerSequence n).map (g)^*[AddCommGrpCat.{u + 1}] ⟶ X.kummerSequence n where
  τ₁ := upperStarRootsOfUnitySheafToRootsOfUnitySheaf g n
  τ₂ := upperStarGmSheafToGmSheaf g
  τ₃ := upperStarGmSheafToGmSheaf g
  comm₁₂ := upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι g n
  comm₂₃ := (map_nsmul_comp_upperStarGmSheafToGmSheaf g n).symm

/-- The pullback map `Hᵠ(Y, 𝔾ₘ) → Hᵠ(X, 𝔾ₘ)` along `g : X ⟶ Y`. -/
noncomputable def gmCohomologyMap (q : ℕ) : Sheaf.H Y.gmSheaf q →+ Sheaf.H X.gmSheaf q :=
  (Sheaf.H.map (upperStarGmSheafToGmSheaf g) q).comp (Etale.cohomologyMap g Y.gmSheaf q)

/-- The pullback map `Hᵠ(Y, μₙ) → Hᵠ(X, μₙ)` along `g : X ⟶ Y`. -/
noncomputable def rootsOfUnityCohomologyMap (q : ℕ) :
    Sheaf.H (Y.rootsOfUnitySheaf n) q →+ Sheaf.H (X.rootsOfUnitySheaf n) q :=
  (Sheaf.H.map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf g n) q).comp
    (Etale.cohomologyMap g (Y.rootsOfUnitySheaf n) q)

/-- The pullback maps on the cohomology of `μₙ` and of `𝔾ₘ` are compatible with the inclusion
`μₙ ⟶ 𝔾ₘ`. -/
lemma map_kernelι_rootsOfUnityCohomologyMap (q : ℕ) (x : Sheaf.H (Y.rootsOfUnitySheaf n) q) :
    Sheaf.H.map (X.rootsOfUnitySheafι n) q (rootsOfUnityCohomologyMap g n q x) =
      gmCohomologyMap g q (Sheaf.H.map (Y.rootsOfUnitySheafι n) q x) := by
  simp only [rootsOfUnityCohomologyMap, gmCohomologyMap, AddMonoidHom.comp_apply]
  rw [← Sheaf.H.map_comp_apply, upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι,
    Sheaf.H.map_comp_apply, Etale.cohomologyMap_map]

/-- **The Kummer boundary commutes with pullback.** For `g : X ⟶ Y` and `n` invertible on `Y`
and on `X`, the square

```
  H¹(Y, 𝔾ₘ) ──δ──▶ H²(Y, μₙ)
      │                 │
      ▼                 ▼
  H¹(X, 𝔾ₘ) ──δ──▶ H²(X, μₙ)
```

of Kummer boundaries (`AlgebraicGeometry.Scheme.kummerδ₁`) and pullback maps commutes. -/
lemma rootsOfUnityCohomologyMap_kummerδ₁ (hY : IsUnit (n : Γ(Y, ⊤))) (hX : IsUnit (n : Γ(X, ⊤)))
    (c : Y.CohomologicalPicardGroup) :
    rootsOfUnityCohomologyMap g n 2 (Y.kummerδ₁ n hY c) =
      X.kummerδ₁ n hX (gmCohomologyMap g 1 c) := by
  have h₁ := Etale.cohomologyMap_δSucc g (Y.kummerSequence_shortExact n hY) 1 c
  have h₂ := Sheaf.H.map_δSucc
    ((Y.kummerSequence_shortExact n hY).map_of_exact (g)^*[AddCommGrpCat.{u + 1}])
    (X.kummerSequence_shortExact n hX)
    (kummerSequenceUpperStarMap g n) 1 (Etale.cohomologyMap g Y.gmSheaf 1 c)
  exact (congrArg (Sheaf.H.map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf g n) 2) h₁).trans h₂

end Pullback

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

end IsConnectedCurve

end AlgebraicGeometry
