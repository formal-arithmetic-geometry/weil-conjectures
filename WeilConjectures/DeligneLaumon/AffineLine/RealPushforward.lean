/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PointCount
public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.StalkCharpoly
public import WeilConjectures.WeilSheaf.TraceFormula
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Real

/-!
# Reality of a higher direct image with compact support concentrated in one degree

Let `f : X ⟶ Y` be a separated morphism of finite type of `k₀`-schemes and `K` an `ι`-real Weil
sheaf on `X`. If `Rf_!K` is concentrated in degree one, then `R¹f_!K` is `ι`-real. At a closed
point `ξ` of `Y` of degree `d` and for `m ≥ 1`, the relative trace formula gives

`Tr(F_ξ^m | (R¹f_!K)_ξ̄) = - ∑_{x ∈ X_ξ(𝔽_{q^{dm}})} Tr(F_x | K_x̄)`,

every term on the right is `ι`-real since `K` is, so all the traces of the powers of `F_ξ` are
`ι`-real, and by Newton's identities so is the local polynomial `det(1 - T F_ξ)`
(`FrobeniusModule.isReal_iff_forall_trace_pow`).

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_fieldPoints_galoisExtension_base_eq`: a point of degree
  dividing `n ≠ 0` is the image of an `𝔽_{qⁿ}`-rational point.
- `AlgebraicGeometry.WeilSheaf.IsReal.traceFunction`: the trace function of an `ι`-real Weil
  sheaf has real `ι`-image.
- `AlgebraicGeometry.WeilSheaf.isZero_homologySheaf_derivedLowerShriek_toComplex_of_neg`: `Rf_!K`
  vanishes in negative degrees.
- `AlgebraicGeometry.WeilSheaf.isReal_higherLowerShriek_one`: reality of `R¹f_!K` when `Rf_!K` is
  concentrated in degree one.
- `AlgebraicGeometry.WeilSheaf.isReal_higherLowerShriek_snd_one`
  (`lem-fd-realness-pushforward`): the case of the second projection `𝔸² ⟶ 𝔸¹`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A point `x` of a scheme over a finite field `k` whose degree divides `n ≠ 0` is the image of
an `𝔽_{qⁿ}`-rational point: its residue field embeds into the degree `n` extension of `k`. -/
theorem Scheme.Hom.exists_fieldPoints_galoisExtension_base_eq {k : Type u} [Field k] [Finite k]
    {X : Scheme.{u}} (f : X.Hom (Spec (.of k))) {n : ℕ} (hn : n ≠ 0) {x : X}
    (hx : f.degreeOver x ∣ n) :
    ∃ y : f.fieldPoints (FiniteField.galoisExtension k n),
      y.1.base (IsLocalRing.closedPoint _) = x := by
  have : Finite (FiniteField.galoisExtension k n) := Module.finite_of_finite k
  let := (f.residueFieldAlgebraMap x).toAlgebra
  obtain ⟨ψ⟩ : Nonempty (X.residueField x →ₐ[k] FiniteField.galoisExtension k n) := by
    rw [FiniteField.nonempty_algHom_iff_finrank_dvd, FiniteField.finrank_galoisExtension k n hn]
    exact hx
  obtain ⟨y, hy⟩ := (f.exists_fieldPoints_base_eq_iff _ x).2
    ⟨CommRingCat.ofHom ψ.toRingHom, ψ.comp_algebraMap⟩
  exact ⟨y, (congrArg y.1.base (Subsingleton.elim _ _)).trans hy⟩

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

/-- The trace function of an `ι`-real Weil sheaf has real `ι`-image: at a rational point over
a closed point `x` it is the trace of a power of the local Frobenius `Fₓ`
(`AlgebraicGeometry.WeilSheaf.traceFunction_eq_trace_frobeniusEnd_stalk_pow`), and the traces of
the powers of the Frobenius of an `ι`-real Frobenius module are `ι`-real by Newton's identities
(`FrobeniusModule.isReal_iff_forall_trace_pow`). -/
theorem IsReal.traceFunction {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X} (hF : F.IsReal ι)
    (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    starRingEnd ℂ (ι (F.traceFunction n x)) = ι (F.traceFunction n x) := by
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  obtain ⟨φ, -⟩ := Scheme.exists_eq_spec_map_comp_fromSpecResidueField x.1 _ rfl
  have hx : x.1.base (IsLocalRing.closedPoint _) ∈ X.finitePoints :=
    X.mem_finitePoints.2 (Finite.of_injective _ φ.hom.injective)
  rw [traceFunction_eq_trace_frobeniusEnd_stalk_pow F n x ⟨_, hx⟩ rfl]
  exact (FrobeniusModule.isReal_iff_forall_trace_pow ι _).1 (hF _) _

attribute [local instance] Compactification.over in
/-- The direct image with compact support `Rf_!K` of a Weil sheaf has no cohomology sheaves in
negative degrees: `Rf_! = Rḡ_* ∘ ī_!` carries `K` placed in degree zero to the total right
derived functor of `ḡ_*` applied to the sheaf `ī_!K` placed in degree zero. -/
theorem isZero_homologySheaf_derivedLowerShriek_toComplex_of_neg (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (K : WeilSheaf k₀ l X) {ν : ℤ}
    (hν : ν < 0) :
    IsZero ((WeilComplex.homologySheaf ν).obj
      ((WeilComplex.derivedLowerShriek k₀ l f).obj (toComplex.obj K))) := by
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  rw [WeilComplex.isZero_homologySheaf_obj_iff]
  have := (ProEtaleWeilSheaf.lowerStar k₀ l c.g).isGE_rightDerivedFunctor_obj_singleFunctor
    ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).obj K.obj)
  exact (_root_.DerivedCategory.isZero_of_isGE (hX := this) _ 0 ν hν).of_iso
    ((_root_.DerivedCategory.homologyFunctor _ ν).mapIso
      ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
        (((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategorySingleFunctor 0).app
          K.obj)))

/-- **Reality survives a direct image concentrated in degree one.** Let `f : X ⟶ Y` be a
separated morphism of finite type of `k₀`-schemes and `K` an `ι`-real Weil sheaf on `X` such
that `Rf_!K` has no cohomology sheaves outside degree one. Then `R¹f_!K` is `ι`-real.

At a closed point `ξ` of degree `d` and for `m ≥ 1`, the trace of `F_ξ^m` on the stalk of
`R¹f_!K` is the value of the trace function of `R¹f_!K` at an `𝔽_{q^{dm}}`-point over `ξ`, which
is minus that of `Rf_!K`, the sum of the trace function of `K` over the fibre by the relative
trace formula (`AlgebraicGeometry.WeilComplex.traceFunction_derivedLowerShriek`). Each term is
`ι`-real (`AlgebraicGeometry.WeilSheaf.IsReal.traceFunction`), so all the traces of the powers of
`F_ξ` are `ι`-real, hence so is `det(1 - T F_ξ)` (`FrobeniusModule.isReal_iff_forall_trace_pow`).
(blueprint: `lem-fd-realness-pushforward`, for a general `f`, vanishing stated on `ℤ`) -/
theorem isReal_higherLowerShriek_one_of_isZero_homologySheaf {ι : PadicAlgCl l →+* ℂ} (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] {K : WeilSheaf k₀ l X} (hK : K.IsReal ι)
    (hvan : ∀ ν : ℤ, ν ≠ 1 → IsZero ((WeilComplex.homologySheaf ν).obj
      ((WeilComplex.derivedLowerShriek k₀ l f).obj (toComplex.obj K)))) :
    ((higherLowerShriek k₀ l f 1).obj K).IsReal ι := by
  intro ξ
  rw [FrobeniusModule.isReal_iff_forall_trace_pow]
  intro m
  rcases m with _ | m
  · rw [pow_zero, LinearMap.trace_one, map_natCast, Complex.conj_natCast]
  set d := (Y ↘ Spec (CommRingCat.of k₀)).degreeOver ξ.1
  have hd : d ≠ 0 := Scheme.Hom.degreeOver_ne_zero _ ξ.2
  have hn : d * (m + 1) ≠ 0 := Nat.mul_ne_zero hd (Nat.succ_ne_zero m)
  obtain ⟨y, hy⟩ := Scheme.Hom.exists_fieldPoints_galoisExtension_base_eq _ hn
    (dvd_mul_right d (m + 1))
  have h := traceFunction_eq_trace_frobeniusEnd_stalk_pow ((higherLowerShriek k₀ l f 1).obj K)
    (d * (m + 1)) y ξ hy
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd)] at h
  have hL := WeilComplex.traceFunction_eq_sum
    ((WeilComplex.derivedLowerShriek k₀ l f).obj (toComplex.obj K)) {1}
    (fun j hj ↦ hvan j (Finset.notMem_singleton.1 hj)) (d * (m + 1)) y
  rw [Finset.sum_singleton, Int.negOnePow_one, Units.val_neg, Units.val_one, neg_smul, one_smul,
    WeilComplex.traceFunction_derivedLowerShriek f _ (Nat.one_le_iff_ne_zero.2 hn) y] at hL
  have hH : ((higherLowerShriek k₀ l f 1).obj K).traceFunction (d * (m + 1)) y =
      -∑ᶠ x : {x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints
          (FiniteField.galoisExtension k₀ (d * (m + 1))) // x.1 ≫ f = y.1},
        (toComplex.obj K).traceFunction (d * (m + 1)) x.1 := by
    rw [hL, neg_neg]
    rfl
  rw [← h, hH]
  refine RingHom.mem_realSubfield.1 (neg_mem (finsum_induction _ (zero_mem _)
    (fun _ _ ↦ add_mem) fun x ↦ ?_))
  rw [WeilComplex.traceFunction_toComplex]
  exact hK.traceFunction _ _

/-- **Reality survives a direct image concentrated in degree one**, with the vanishing of the
higher direct images `Rᵛf_!K` assumed for `ν ∈ ℕ`, `ν ≠ 1`: in negative degrees they vanish
automatically
(`AlgebraicGeometry.WeilSheaf.isZero_homologySheaf_derivedLowerShriek_toComplex_of_neg`).
See `AlgebraicGeometry.WeilSheaf.isReal_higherLowerShriek_one_of_isZero_homologySheaf`.
(blueprint: `lem-fd-realness-pushforward`, for a general `f`) -/
theorem isReal_higherLowerShriek_one {ι : PadicAlgCl l →+* ℂ} (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] {K : WeilSheaf k₀ l X} (hK : K.IsReal ι)
    (hvan : ∀ ν : ℕ, ν ≠ 1 → IsZero ((higherLowerShriek k₀ l f ν).obj K)) :
    ((higherLowerShriek k₀ l f 1).obj K).IsReal ι := by
  refine isReal_higherLowerShriek_one_of_isZero_homologySheaf f hK fun ν hν ↦ ?_
  rcases lt_or_ge ν 0 with h | h
  · exact isZero_homologySheaf_derivedLowerShriek_toComplex_of_neg f K h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    exact hvan n (by omega)

/-- **Reality survives the Fourier projection.** Let `K` be an `ι`-real Weil sheaf on the
affine plane `𝔸¹ ×_{k₀} 𝔸¹` such that `Rpr₂!K` has no cohomology sheaves outside degree one,
for the second projection `pr₂ : 𝔸¹ ×_{k₀} 𝔸¹ ⟶ 𝔸¹`. Then `R¹pr₂!K` is `ι`-real. This is the
case `f = pr₂` of `AlgebraicGeometry.WeilSheaf.isReal_higherLowerShriek_one`.
(blueprint: `lem-fd-realness-pushforward`) -/
theorem isReal_higherLowerShriek_snd_one {ι : PadicAlgCl l →+* ℂ}
    {K : WeilSheaf k₀ l (affinePlane k₀)} (hK : K.IsReal ι)
    (hvan : ∀ ν : ℕ, ν ≠ 1 → IsZero ((higherLowerShriek k₀ l (affinePlane.snd k₀) ν).obj K)) :
    ((higherLowerShriek k₀ l (affinePlane.snd k₀) 1).obj K).IsReal ι :=
  isReal_higherLowerShriek_one _ hK hvan

end WeilSheaf

end AlgebraicGeometry
