/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
public import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# The Kummer sequence

For a scheme `X` and `n ≥ 1` the *Kummer sequence* is the sequence of étale sheaves

```
  0 ──▶ μₙ ──kernel.ι──▶ 𝔾ₘ ──n • 𝟙──▶ 𝔾ₘ ──▶ 0
```

whose right hand map is the `n`-th power map (written additively as `n • 𝟙`) and whose sheaf
`μₙ` of `n`-th roots of unity is by definition its kernel. It is exact as soon as `n` is
invertible on `X`: for a unit `t` on `U`, the scheme `U ×_{Spec Γ(U, 𝒪)} Spec Γ(U, 𝒪)[T]/(Tⁿ - t)`
is a surjective étale cover of `U` on which `t` has an `n`-th root. Its long exact
cohomology sequence

```
  Γ(X, 𝒪)ˣ ──(·)ⁿ──▶ Γ(X, 𝒪)ˣ ──▶ H¹(X, μₙ) ──▶ H¹(X, 𝔾ₘ) ──n·──▶ H¹(X, 𝔾ₘ)
           ──▶ H²(X, μₙ) ──▶ H²(X, 𝔾ₘ) ──n·──▶ H²(X, 𝔾ₘ)
```

computes `H¹` and `H²` of `μₙ` in terms of the Picard and Brauer groups of `X`. The group of
units `Γ(X, 𝒪)ˣ` is written additively, as `Additive Γ(X, ⊤)ˣ`, so that its `n`-th power map
is `n • ·`.

This file also defines the constant étale sheaf `ℤ/n`, which is `μₙ` after the choice of a
primitive `n`-th root of unity.

## Main definitions

- `AlgebraicGeometry.Scheme.rootsOfUnitySheaf`: the sheaf `μₙ` of `n`-th roots of unity.
- `AlgebraicGeometry.Scheme.kummerSequence`: the Kummer sequence, as a short complex.
- `AlgebraicGeometry.Scheme.constantZMod`: the constant étale sheaf `ℤ/n`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_etale_surjective_pow_eq_appTop`: a unit on a scheme on which
  `n` is invertible has an `n`-th root on a surjective étale cover.
- `AlgebraicGeometry.Scheme.isLocallySurjective_nsmul_gmSheaf`: the `n`-th power map on `𝔾ₘ` is
  locally surjective for the étale topology.
- `AlgebraicGeometry.Scheme.kummerSequence_shortExact`: the Kummer sequence is short exact
  when `n` is invertible on `X`.
- `AlgebraicGeometry.Scheme.exists_exact_sheafH_rootsOfUnitySheaf_one`: the short exact
  sequence `0 → Γ(X, 𝒪)ˣ/n → H¹(X, μₙ) → H¹(X, 𝔾ₘ)[n] → 0`.
- `AlgebraicGeometry.Scheme.exists_exact_sheafH_rootsOfUnitySheaf_two`: the short exact
  sequence `0 → H¹(X, 𝔾ₘ)/n → H²(X, μₙ) → H²(X, 𝔾ₘ)[n] → 0`.
- `AlgebraicGeometry.Scheme.nonempty_addEquiv_sheafH_zero_constantZMod`:
  `H⁰(X, ℤ/n) ≅ ℤ/n` for a connected scheme `X`.

## TODO

The maps of the two Kummer statements are those of the long exact sequence. The long exact
sequence of a short exact sequence of sheaves is
`CategoryTheory.Abelian.Ext.covariantSequence_exact`; once its maps are connected to
`CategoryTheory.Sheaf.H`, the maps should be named rather than quantified.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry.Scheme

/-- An element `t` of `Γ(U, ⊤)` whose image under `φ : Γ(U, ⊤) ⟶ R` is an `n`-th power has an
`n`-th root on the base change of `Spec R ⟶ Spec Γ(U, ⊤)` along `U ⟶ Spec Γ(U, ⊤)`. -/
private lemma exists_pow_eq_pullback_fst_toSpecΓ_appTop {U : Scheme.{u}} {R : CommRingCat.{u}}
    (φ : Γ(U, ⊤) ⟶ R) {n : ℕ} {t : Γ(U, ⊤)} {r : R} (h : φ t = r ^ n) :
    ∃ ω : Γ(pullback U.toSpecΓ (Spec.map φ), ⊤),
      ω ^ n = (pullback.fst U.toSpecΓ (Spec.map φ)).appTop t := by
  refine ⟨(pullback.snd U.toSpecΓ (Spec.map φ)).appTop ((ΓSpecIso R).inv r), ?_⟩
  rw [pullback_fst_toSpecΓ_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply, h, map_pow,
    map_pow]

/-- **Kummer covers.** Let `U` be a scheme, `n ≠ 0` invertible on `U` and `t` a unit on `U`.
Then `t` has an `n`-th root on a surjective étale cover of `U`: there is an étale surjective
`f : V ⟶ U` and `ω ∈ Γ(V, 𝒪_V)` with `ωⁿ = f^* t`.

One takes for `V` the base change of `Spec Γ(U, 𝒪)[T]/(Tⁿ - t) ⟶ Spec Γ(U, 𝒪)` along
`U ⟶ Spec Γ(U, 𝒪)`, and for `ω` the image of `T`. The algebra `Γ(U, 𝒪)[T]/(Tⁿ - t)` is étale
since the derivative `nTⁿ⁻¹` is invertible modulo `Tⁿ - t`
(`AdjoinRoot.etale_X_pow_sub_C`), and faithfully flat since it is free of rank `n ≥ 1`
(`AdjoinRoot.faithfullyFlat_of_monic`), so its spectrum is surjective; both properties are
stable under base change.

This is the main step of the proof of exactness of the Kummer sequence
(blueprint: `lem-sc-kummer-exact`). -/
theorem exists_etale_surjective_pow_eq_appTop {U : Scheme.{u}} {n : ℕ} (hn₀ : n ≠ 0)
    (hn : IsUnit (n : Γ(U, ⊤))) {t : Γ(U, ⊤)} (ht : IsUnit t) :
    ∃ (V : Scheme.{u}) (f : V ⟶ U), Etale f ∧ Surjective f ∧
      ∃ ω : Γ(V, ⊤), ω ^ n = f.appTop t := by
  let φ : Γ(U, ⊤) ⟶ CommRingCat.of (AdjoinRoot (X ^ n - C t)) :=
    CommRingCat.ofHom (algebraMap _ _)
  have : Etale (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr (AdjoinRoot.etale_X_pow_sub_C hn₀ hn ht)
  have hdeg : (X ^ n - C t).degree ≠ 0 := by
    nontriviality Γ(U, ⊤)
    rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero hn₀)]
    exact_mod_cast hn₀
  have : Surjective (Spec.map φ) :=
    ((flat_and_surjective_SpecMap_iff φ).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr
      (AdjoinRoot.faithfullyFlat_of_monic (monic_X_pow_sub_C t hn₀)
        hdeg))).2
  have hφ : φ t = AdjoinRoot.root (X ^ n - C t) ^ n := by
    have := AdjoinRoot.eval₂_root (X ^ n - C t)
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at this
    exact this.symm
  exact ⟨_, _, inferInstance, inferInstance, exists_pow_eq_pullback_fst_toSpecΓ_appTop φ hφ⟩

variable (X : Scheme.{u}) (n : ℕ)

/-- The sheaf `μₙ` of `n`-th roots of unity on the small étale site of `X`: the kernel of the
`n`-th power map `n • 𝟙` on `𝔾ₘ`. -/
noncomputable def rootsOfUnitySheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel (n • 𝟙 X.gmSheaf)

/-- The *Kummer sequence* of a scheme `X` and an integer `n`: the sequence of étale sheaves

```
  0 ──▶ μₙ ──kernel.ι──▶ 𝔾ₘ ──n • 𝟙──▶ 𝔾ₘ ──▶ 0
```

on `X`, the second map being `ω ↦ ωⁿ` and `μₙ = ker(n)` the sheaf of `n`-th roots of unity.
Its exactness is `AlgebraicGeometry.Scheme.kummerSequence_shortExact` and is *not* part of
the definition.
(blueprint: `def-sc-kummer-sequence`) -/
noncomputable def kummerSequence :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (kernel.ι (n • 𝟙 X.gmSheaf)) (n • 𝟙 X.gmSheaf) (kernel.condition _)

/-- The `n`-th power map `n • 𝟙` on `𝔾ₘ` is locally surjective for the étale topology when `n` is
invertible on `X`: a unit `t` on an étale `X`-scheme `U` acquires an `n`-th root on the
surjective étale cover of `AlgebraicGeometry.Scheme.exists_etale_surjective_pow_eq_appTop`.
(blueprint: `lem-sc-kummer-exact`) -/
theorem isLocallySurjective_nsmul_gmSheaf (hn : IsUnit (n : Γ(X, ⊤))) :
    Sheaf.IsLocallySurjective (n • 𝟙 X.gmSheaf) where
  imageSieve_mem {U} s := by
    have hnU : IsUnit (n : Γ(U.left, ⊤)) := by
      have := hn.map U.hom.appTop.hom
      rwa [map_natCast] at this
    rcases eq_or_ne n 0 with rfl | hn₀
    · -- If `0` is invertible then `Γ(U, 𝒪)` is zero, so every section is in the image.
      have : Subsingleton Γ(U.left, ⊤) := subsingleton_of_zero_eq_one (by simpa using hnU)
      have hs : s = 0 := by
        apply ULift.ext
        apply Additive.toMul.injective
        exact Subsingleton.elim (α := Γ(U.left, ⊤)ˣ) _ _
      rw [show s = (0 • 𝟙 X.gmSheaf).hom.app (Opposite.op U) 0 by rw [hs, map_zero],
        Presheaf.imageSieve_app]
      exact GrothendieckTopology.top_mem _ _
    obtain ⟨V, f, hf, hsurj, ω, hω⟩ :=
      exists_etale_surjective_pow_eq_appTop hn₀ hnU (Units.isUnit (Additive.toMul s.down))
    have : Etale (f ≫ U.hom) := by have := U.prop; infer_instance
    let g : MorphismProperty.Over.mk ⊤ (f ≫ U.hom) this ⟶ U :=
      MorphismProperty.Over.homMk f rfl
    refine GrothendieckTopology.superset_covering _ ?_
      ((ofArrows_mem_smallEtaleTopology_iff (fun _ : Unit ↦ g)).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨⟩
      have hωu : IsUnit ω := (isUnit_pow_iff hn₀).mp (hω ▸ (Units.isUnit _).map _)
      refine ⟨⟨Additive.ofMul hωu.unit⟩, ?_⟩
      have e : (n • 𝟙 X.gmSheaf).hom = n • 𝟙 X.gmSheaf.obj :=
        (sheafToPresheaf _ _).map_nsmul (f := 𝟙 X.gmSheaf) (n := n)
      have e' (A : AddCommGrpCat.{u + 1}) (x : A) : ConcreteCategory.hom (n • 𝟙 A) x = n • x :=
        rfl
      rw [e, NatTrans.app_nsmul, NatTrans.id_app, e']
      apply ULift.ext
      apply Additive.toMul.injective
      apply Units.ext
      change ((Additive.toMul (n • Additive.ofMul hωu.unit : Additive Γ(V, ⊤)ˣ) : Γ(V, ⊤)ˣ) :
        Γ(V, ⊤)) = f.appTop.hom
          ((Additive.toMul (s.down : Additive Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤))
      rw [toMul_nsmul, toMul_ofMul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, hω]
      rfl
    · simp only [Set.iUnion_const]
      exact Set.range_eq_univ.mpr hsurj.surj

/-- **Exactness of the Kummer sequence.** Let `X` be a scheme and let `n ≥ 1` be invertible on
`X`. Then the Kummer sequence `AlgebraicGeometry.Scheme.kummerSequence` is a short exact
sequence of sheaves on `X_ét`.

The first map is a kernel of the second by definition of `μₙ`. The second map, `ω ↦ ωⁿ`, is
an epimorphism because it is locally surjective
(`AlgebraicGeometry.Scheme.isLocallySurjective_nsmul_gmSheaf`): a unit `t` acquires an `n`-th
root on the finite étale surjective cover `Spec 𝒪[T]/(Tⁿ - t)`. The hypothesis is necessary: in
characteristic `p` the `p`-th power map is not an epimorphism of étale sheaves, and the correct
replacement is the Artin–Schreier sequence.
(blueprint: `lem-sc-kummer-exact`) -/
theorem kummerSequence_shortExact (hn : IsUnit (n : Γ(X, ⊤))) :
    (X.kummerSequence n).ShortExact :=
  have := X.isLocallySurjective_nsmul_gmSheaf n hn
  { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
    mono_f := by dsimp [kummerSequence]; infer_instance
    epi_g := Sheaf.epi_of_isLocallySurjective (n • 𝟙 X.gmSheaf) }

/-- **`H¹` via the Kummer sequence.** For a scheme `X` and `n` invertible on `X` there is an
exact sequence

```
  Γ(X, 𝒪)ˣ ──(·)ⁿ──▶ Γ(X, 𝒪)ˣ ──α──▶ H¹(X, μₙ) ──β──▶ H¹(X, 𝔾ₘ)[n] ⟶ 0,
```

that is, `0 → Γ(X, 𝒪)ˣ/n → H¹(X, μₙ) → H¹(X, 𝔾ₘ)[n] → 0`. It is recorded as the existence of
maps `α` and `β` with `ker α = (Γ(X, 𝒪)ˣ)ⁿ`, `ker β = im α` and `im β = H¹(X, 𝔾ₘ)[n]`.
(blueprint: `sk-prop-h1`) -/
theorem exists_exact_sheafH_rootsOfUnitySheaf_one (hn : IsUnit (n : Γ(X, ⊤))) :
    ∃ (α : Additive Γ(X, ⊤)ˣ →+ Sheaf.H (X.rootsOfUnitySheaf n) 1)
      (β : Sheaf.H (X.rootsOfUnitySheaf n) 1 →+ X.CohomologicalPicardGroup),
      α.ker = (zsmulAddGroupHom (α := Additive Γ(X, ⊤)ˣ) (n : ℤ)).range ∧
        Function.Exact α β ∧ β.range = AddSubgroup.torsionBy X.CohomologicalPicardGroup n :=
  -- Proof sketch: this is the start of the long exact sequence of
  -- `AlgebraicGeometry.Scheme.kummerSequence_shortExact`, with `H⁰(X, 𝔾ₘ) = Γ(X, 𝒪)ˣ`.
  sorry

/-- **`H²` via the Kummer sequence.** For a scheme `X` and `n` invertible on `X` there is an
exact sequence

```
  H¹(X, 𝔾ₘ) ──n·──▶ H¹(X, 𝔾ₘ) ──α──▶ H²(X, μₙ) ──β──▶ H²(X, 𝔾ₘ)[n] ⟶ 0,
```

that is, `0 → H¹(X, 𝔾ₘ)/n → H²(X, μₙ) → H²(X, 𝔾ₘ)[n] → 0`. It is recorded as the existence of
maps `α` and `β` with `ker α = n · H¹(X, 𝔾ₘ)`, `ker β = im α` and `im β = H²(X, 𝔾ₘ)[n]`.
(blueprint: `sk-prop-h2`) -/
theorem exists_exact_sheafH_rootsOfUnitySheaf_two (hn : IsUnit (n : Γ(X, ⊤))) :
    ∃ (α : X.CohomologicalPicardGroup →+ Sheaf.H (X.rootsOfUnitySheaf n) 2)
      (β : Sheaf.H (X.rootsOfUnitySheaf n) 2 →+ X.CohomologicalBrauerGroup),
      α.ker = (zsmulAddGroupHom (α := X.CohomologicalPicardGroup) (n : ℤ)).range ∧
        Function.Exact α β ∧ β.range = AddSubgroup.torsionBy X.CohomologicalBrauerGroup n :=
  -- Proof sketch: this is the middle part of the long exact sequence of
  -- `AlgebraicGeometry.Scheme.kummerSequence_shortExact`.
  sorry

/-- The constant étale sheaf `ℤ/n` on a scheme `X`, valued in abelian groups of the universe of
the small étale site. -/
noncomputable abbrev constantZMod : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))

/-- The global sections of the constant sheaf `ℤ/n` on a connected scheme are `ℤ/n`:
`H⁰(X_ét, ℤ/n) ≅ ℤ/n`.
(blueprint: `sk-thm-curveestimate`) -/
theorem nonempty_addEquiv_sheafH_zero_constantZMod [ConnectedSpace X] :
    Nonempty (Sheaf.H (X.constantZMod n) 0 ≃+ ZMod n) :=
  -- Proof sketch: the sections of a constant étale sheaf over `X` are the locally constant
  -- functions `X → ℤ/n`, and these are constant since `X` is connected.
  sorry

end AlgebraicGeometry.Scheme
