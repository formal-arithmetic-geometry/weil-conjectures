/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Kummer
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Smooth affine curves over an algebraically closed field

Let `C` be a smooth affine connected curve over an algebraically closed field `k`. This file
collects the inputs of the computation of the étale cohomology of `C`
(`AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_of_two_le_of_isAffine_of_smooth`):

* the normalization of `C` in a finite extension of its function field is again a smooth affine
  connected curve, finite over `C`;
* the group `𝒪(C)ˣ / 𝒪(C)ˣⁿ` is finite;
* `Pic(C)` is a quotient of the `k`-points of the Jacobian of the smooth compactification of `C`
  by a finitely generated subgroup; hence it is `n`-divisible with finite `n`-torsion for `n`
  prime to `char k`;
* `H²(C, ℤ/ℓ) = 0` for every prime `ℓ`, and `H²(C, η_* M) = 0` for every torsion sheaf `M` on
  the generic point `η` of `C`.

## Main statements

- `AlgebraicGeometry.IsConnectedCurve.normalizationIn`: the normalization in a finite extension.
- `AlgebraicGeometry.IsConnectedCurve.finite_units_quotient`: `𝒪(C)ˣ / 𝒪(C)ˣⁿ` is finite.
- `AlgebraicGeometry.IsConnectedCurve.surjective_zsmul_pic_and_finite_torsionBy`: `Pic(C)` is
  `n`-divisible with finite `n`-torsion.
- `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_constantZMod`: `H²(C, ℤ/ℓ) = 0`.
- `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_lowerStar`: `H²(C, η_* M) = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry.IsConnectedCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **An affine curve model for a finite extension.** Let `C` be a smooth integral affine
connected curve over an algebraically closed field `k`, and `L` a finite extension of its function
field. Then the normalization `h : C' ⟶ C` of `C` in `L`
(`AlgebraicGeometry.Scheme.normalizationIn`) is finite, `C'` is a smooth affine connected curve
over `k` (it is integral, `AlgebraicGeometry.Scheme.Hom.normalization` of an integral scheme), and
the morphism `Spec L ⟶ C'` is the generic point of `C'`, identifying `L` with the function field
of `C'`.

Finiteness is `AlgebraicGeometry.Scheme.isFinite_fromNormalizationIn`, so `C'` is affine and has
dimension one. Its local rings are integrally closed, hence `C'` is regular, hence smooth over the
perfect field `k` (`AlgebraicGeometry.smooth_of_isRegular`).
(blueprint: `lem-sc-finite-extension-affine-model`) -/
theorem normalizationIn (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    [IsIntegral C] (L : Type u) [Field L] [Algebra C.functionField L]
    [FiniteDimensional C.functionField L] :
    IsFinite (C.fromNormalizationIn L) ∧ IsAffine (C.normalizationIn L) ∧
      IsConnectedCurve (C.fromNormalizationIn L ≫ f) ∧ Smooth (C.fromNormalizationIn L ≫ f) ∧
      ∃ e : Spec (.of L) ≅ Spec (C.normalizationIn L).functionField,
        e.hom ≫ (C.normalizationIn L).fromSpecFunctionField =
          (C.fromSpecOfAlgebraFunctionField L).toNormalization := by
  set h := C.fromNormalizationIn L
  have : IsFinite h := C.isFinite_fromNormalizationIn L f
  have : IsAffine (C.normalizationIn L) := isAffine_of_isAffineHom h
  -- `h` is surjective: it is closed, and dominant since `Spec L ⟶ C` is.
  have : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap C.functionField L))) := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨y⟩ : Nonempty (Spec (.of L)) := inferInstance
    exact subset_closure ⟨y, Subsingleton.elim _ _⟩
  have : IsDominant ((C.fromSpecOfAlgebraFunctionField L).toNormalization ≫ h) := by
    rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
  have : IsDominant h := .of_comp (C.fromSpecOfAlgebraFunctionField L).toNormalization _
  have hdim : topologicalKrullDim (C.normalizationIn L) = 1 := by
    rw [h.topologicalKrullDim_eq_of_surjective]
    exact IsConnectedCurve.krullDim_eq_one (f := f)
  have : IsLocallyNoetherian (C.normalizationIn L) :=
    LocallyOfFiniteType.isLocallyNoetherian (h ≫ f)
  -- The local rings of `Spec L` are integrally closed, hence so are those of `C'`.
  have hK (x : Spec (.of L)) : IsIntegrallyClosed ((Spec (.of L)).presheaf.stalk x) := by
    let := TopCat.Presheaf.algebra_section_stalk (Spec (.of L)).presheaf
      (⟨x, trivial⟩ : (⊤ : (Spec (.of L)).Opens))
    have := (isAffineOpen_top (Spec (.of L))).isLocalization_stalk ⟨x, trivial⟩
    have : IsIntegrallyClosed Γ(Spec (.of L), ⊤) :=
      .of_equiv (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv.symm
    exact isIntegrallyClosed_of_isLocalization _ _
      ((isAffineOpen_top _).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl_le_nonZeroDivisors
  have : IsRegular (C.normalizationIn L) := IsRegular.of_isIntegrallyClosed_stalk
    (fun y ↦ ⟨inferInstance,
      (C.fromSpecOfAlgebraFunctionField L).isIntegrallyClosed_stalk_normalization hK y⟩) hdim.le
  have : Smooth (h ≫ f) := smooth_of_isRegular _
  exact ⟨inferInstance, inferInstance,
    { krullDim_le_one := hdim.le
      connectedSpace := inferInstance
      krullDim_eq_one := hdim }, inferInstance,
    C.exists_iso_toNormalization_normalizationIn L⟩

/-- **Units modulo `n`-th powers on an affine curve.** Let `C` be a smooth affine connected curve
over an algebraically closed field `k` and `n ≥ 1`. Then `𝒪(C)ˣ / 𝒪(C)ˣⁿ` is finite.

Let `C ⊆ C̄` be the smooth compactification, with finite complement `S`. The divisor of a unit
of `𝒪(C)` is supported on `S`, and it vanishes only for the units which extend to `C̄`, i.e. for
`k^×` (`AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_isAlgClosed`). So `𝒪(C)ˣ / k^×` is a
subgroup `Λ` of the free abelian group `ℤ^S`, and `𝒪(C)ˣ / 𝒪(C)ˣⁿ ≅ Λ / nΛ` since every element of
`k^×` is an `n`-th power.
(blueprint: `lem-sc-affine-unit-quotient`) -/
theorem finite_units_quotient (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    [IsAffine C] (n : ℕ) (hn : 0 < n) :
    Finite (Additive Γ(C, ⊤)ˣ ⧸ (zsmulAddGroupHom (α := Additive Γ(C, ⊤)ˣ) n).range) :=
  sorry

/-- **`Pic` of an affine curve as a quotient of the Jacobian.** Let `C` be a smooth affine
connected curve over an algebraically closed field `k`. Then there are a smooth proper connected
compactification `C̄` of `C`, an abelian variety `J` over `k` representing the degree zero part
`Pic⁰_{C̄/k}` of the Picard functor of `C̄` (the Jacobian of `C̄`), and a finitely generated
subgroup `Λ ⊆ J(k)` with `Pic(C) ≅ J(k) / Λ`.

The restriction `Pic(C̄) ⟶ Pic(C)` is surjective with kernel generated by the classes of the
points of `S = C̄ ∖ C` (`AlgebraicGeometry.Scheme.exists_divisorClassGroup_addEquiv_pic`). Fixing
`P₀ ∈ S`, the splitting `Pic(C̄) = ℤ ⊕ Pic⁰(C̄)` of the degree
(`AlgebraicGeometry.Scheme.exists_mulEquiv_prod_ker_picDegreeHom`) identifies `Pic(C)` with
`Pic⁰(C̄) / Λ` for `Λ` generated by the classes `[P] - [P₀]`, `P ∈ S`, and
`Pic⁰(C̄) = J(k)` (`AlgebraicGeometry.exists_jacobian`). The group `Λ` is finitely generated
since `S` is finite.
(blueprint: `lem-sc-pic-affine`, the presentation) -/
theorem exists_addEquiv_pic_quotient (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    [IsAffine C] :
    ∃ (c : Compactification f) (J : Over (Spec (.of k))) (_ : GrpObj J) (_ : IsAbelianVariety J)
      (Λ : AddSubgroup (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J))),
      IsConnectedCurve c.g ∧ Smooth c.g ∧
        Nonempty ((picardFunctorDegree c.g 0).obj.RepresentableBy J) ∧ Λ.FG ∧
        Nonempty (Additive C.Pic ≃+ Additive (𝟙_ (Over (Spec (.of k))) ⟶ J) ⧸ Λ) :=
  sorry

/-- **`Pic` of an affine curve is divisible with finite torsion.** Let `C` be a smooth affine
connected curve over an algebraically closed field `k` and `n` prime to `char k`. Then `Pic(C)`
is `n`-divisible and `Pic(C)[n]` is finite.

By `AlgebraicGeometry.IsConnectedCurve.exists_addEquiv_pic_quotient`, `Pic(C) ≅ J(k) / Λ` for an
abelian variety `J` and a finitely generated subgroup `Λ`. The group `J(k)` is divisible with
finite `n`-torsion (`AlgebraicGeometry.abelianVariety_estimate_of_isAlgClosed`), hence so is its
quotient by `Λ` (`AddSubgroup.finite_torsionBy_quotient`).
(blueprint: `lem-sc-pic-affine`) -/
theorem surjective_zsmul_pic_and_finite_torsionBy (f : C ⟶ Spec (.of k)) [IsConnectedCurve f]
    [Smooth f] [IsAffine C] {n : ℕ} (hn : (n : k) ≠ 0) :
    Function.Surjective (zsmulAddGroupHom (α := Additive C.Pic) n) ∧
      Finite (AddSubgroup.torsionBy (Additive C.Pic) n) := by
  obtain ⟨c, J, _, _, Λ, -, -, -, hΛ, ⟨e⟩⟩ := exists_addEquiv_pic_quotient f
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have hp : ¬ ringChar k ∣ n := fun h ↦ hn ((ringChar.spec k n).2 h)
  obtain ⟨hfin, -, hdiv, -, -⟩ := abelianVariety_estimate_of_isAlgClosed (ringChar k) J
  set G := Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)
  have hG : Function.Surjective (zsmulAddGroupHom (α := G) n) := by
    intro x
    obtain ⟨a, ha⟩ := hdiv n (Nat.pos_of_ne_zero hn0) x.toMul
    refine ⟨.ofMul a, ?_⟩
    rw [zsmulAddGroupHom_apply, natCast_zsmul, ← ofMul_pow, show a ^ n = x.toMul from ha]
    rfl
  have : NeZero n := ⟨hn0⟩
  obtain ⟨eJ⟩ := hfin n (Nat.pos_of_ne_zero hn0) hp
  have : Finite (AddSubgroup.torsionBy G n) := .of_equiv _ eJ.toEquiv.symm
  have hQ := AddSubgroup.finite_torsionBy_quotient Λ hn0 hG hΛ
  refine ⟨fun y ↦ ?_, ?_⟩
  · obtain ⟨x, hx⟩ := (QuotientAddGroup.mk'_surjective Λ).comp hG (e y)
    refine ⟨e.symm (QuotientAddGroup.mk' Λ x), ?_⟩
    simp only [zsmulAddGroupHom_apply, Function.comp_apply] at hx ⊢
    rw [← map_zsmul, ← map_zsmul, hx, AddEquiv.symm_apply_apply]
  · refine Finite.of_injective (β := AddSubgroup.torsionBy (G ⧸ Λ) n)
      (fun x ↦ ⟨e x, (Submodule.mem_torsionBy_iff _ _).2 ?_⟩) fun x y hxy ↦ ?_
    · rw [← map_zsmul, (Submodule.mem_torsionBy_iff _ _).1 x.2, map_zero]
    · exact Subtype.ext (e.injective (congrArg Subtype.val hxy))

/-- **Second cohomology of `ℤ/ℓ` on an affine curve.** Let `C` be a smooth affine connected curve
over an algebraically closed field `k` and `ℓ` a prime. Then `H²(C_ét, ℤ/ℓ) = 0`.

If `ℓ ≠ char k`, a primitive `ℓ`-th root of unity identifies `ℤ/ℓ` with `μ_ℓ`
(`AlgebraicGeometry.Scheme.constantZModIsoRootsOfUnitySheaf`), and the Kummer sequence gives
`H²(C, μ_ℓ) ≅ Pic(C) / ℓ`
(`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two`), which vanishes as `Pic(C)` is `ℓ`-divisible
(`AlgebraicGeometry.IsConnectedCurve.surjective_zsmul_pic_and_finite_torsionBy`). If
`ℓ = char k`, this is the Artin–Schreier vanishing
`AlgebraicGeometry.Scheme.subsingleton_sheafH_constantZMod_of_isAffine`.
(blueprint: `lem-sc-affine-constant-second`) -/
theorem subsingleton_sheafH_two_constantZMod (f : C ⟶ Spec (.of k)) [IsConnectedCurve f]
    [Smooth f] [IsAffine C] (ℓ : ℕ) [Fact ℓ.Prime] :
    Subsingleton (Sheaf.H (C.constantZMod ℓ) 2) := by
  by_cases hℓ : (ℓ : k) = 0
  · refine C.subsingleton_sheafH_constantZMod_of_isAffine ℓ ?_ 2 le_rfl
    simpa using congrArg ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom hℓ
  have : NeZero (ℓ : k) := ⟨hℓ⟩
  have : NeZero ℓ := .of_neZero_natCast k
  obtain ⟨-, -, ζ, hζ, -⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} k ℓ
  obtain ⟨e⟩ := IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two f ℓ hℓ
  obtain ⟨ePic⟩ := C.nonempty_addEquiv_cohomologicalPicardGroup
  have hdiv := (surjective_zsmul_pic_and_finite_torsionBy f hℓ).1
  have htop : (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (ℓ : ℤ)).range = ⊤ := by
    refine AddMonoidHom.range_eq_top.2 fun y ↦ ?_
    obtain ⟨x, hx⟩ := hdiv (ePic.symm y)
    refine ⟨ePic x, ?_⟩
    simp only [zsmulAddGroupHom_apply] at hx ⊢
    rw [← map_zsmul, hx, AddEquiv.apply_symm_apply]
  have : Subsingleton (C.CohomologicalPicardGroup ⧸
      (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (ℓ : ℤ)).range) := by
    rw [htop]
    exact QuotientAddGroup.subsingleton_quotient_top
  have e' := ((Sheaf.functorH _ 2).mapIso
    (C.constantZModIsoRootsOfUnitySheaf ℓ f hζ)).addCommGroupIsoToAddEquiv
  exact (e'.trans e).subsingleton

/-- **Second cohomology of a generic extension on an affine curve.** Let `C` be a smooth integral
affine connected curve over an algebraically closed field `k`, with generic point
`η : Spec k(C) ⟶ C`. Then `H²(C_ét, η_* M) = 0` for every torsion étale sheaf `M` on
`Spec k(C)`.

For `M` finite and `ℓ`-primary, a finite separable extension `K'/k(C)` of degree prime to `ℓ`
over which `M` has a filtration with trivial `𝔽_ℓ` quotients makes `η_* M` a direct summand of
`h_* b_* M|_{K'}`, where `h : C' ⟶ C` is the normalization of `C` in `K'`
(`AlgebraicGeometry.IsConnectedCurve.normalizationIn`) and `b` the generic point of `C'`. Since
`h_*` is exact, the claim reduces along the filtration to
`AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_constantZMod` on `C'`. A general
torsion module is the filtered union of its finite submodules, and cohomology commutes with
filtered colimits on the quasi-compact quasi-separated scheme `C`.
(blueprint: `lem-sc-affine-generic-second`) -/
theorem subsingleton_sheafH_two_lowerStar (f : C ⟶ Spec (.of k)) [IsConnectedCurve f]
    [Smooth f] [IsAffine C] [IsIntegral C]
    (M : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : M.IsTorsion) :
    Subsingleton
      (Sheaf.H ((Etale.lowerStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField).obj M) 2) :=
  sorry

end AlgebraicGeometry.IsConnectedCurve
