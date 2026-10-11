/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Curve.Kummer
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The curve estimate

For a smooth proper connected curve `C` of genus `g` over an algebraically closed field `k`
and `n` prime to the characteristic, the cohomology of the constant sheaf `ℤ/n` on `C_ét` is

`H⁰ = ℤ/n`, `H¹ = (ℤ/n)^{2g}`, `H² = ℤ/n`, `H^q = 0` for `q ≥ 3`.

A smooth proper connected curve is recorded by the class `AlgebraicGeometry.IsConnectedCurve`
together with `Smooth` and `IsProper`. Dimension exactly one is needed in degree two: `Spec k`
is a smooth proper connected scheme of dimension zero with `H² = 0`. Degree zero holds for every
connected scheme (`AlgebraicGeometry.Scheme.nonempty_addEquiv_sheafH_zero_constantZMod`). The
vanishing for `q ≥ 3` is `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le` applied to
`C.constantZMod n`.

In degrees one and two, a primitive `n`-th root of unity identifies `ℤ/n` with `μₙ`, and the
Kummer sequence gives `H¹(C, μₙ) ≅ Pic(C)[n]` and `H²(C, μₙ) ≅ Pic(C)/n`. The degree
`Pic(C) → ℤ` is surjective with kernel `Pic⁰(C) ≅ J(k)`, the `k`-points of the Jacobian `J` of
`C`, an abelian variety of dimension `g`; so `Pic(C)[n] = Pic⁰(C)[n] ≅ (ℤ/n)^{2g}` and, `J(k)`
being divisible, `Pic(C)/n ≅ ℤ/n`.

## Main statements

- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_zero`:
  `H⁰(C, ℤ/n) ≅ ℤ/n`.
- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_one`:
  `H¹(C, ℤ/n) ≅ (ℤ/n)^{2g}`.
- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_two`:
  `H²(C, ℤ/n) ≅ ℤ/n`.
- `AlgebraicGeometry.IsCurve.sheafH_constantZMod`: the four statements together.
-/

@[expose] public section

universe u

open CategoryTheory MonObj

namespace AlgebraicGeometry

/-- An isomorphism of abelian groups restricts to an isomorphism of `n`-torsion subgroups. -/
private def torsionByAddEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B)
    (n : ℤ) : AddSubgroup.torsionBy A n ≃+ AddSubgroup.torsionBy B n where
  toFun x := ⟨e x.1, by
    change n • e x.1 = 0
    rw [← map_zsmul, show n • (x : A) = 0 from x.2, map_zero]⟩
  invFun y := ⟨e.symm y.1, by
    change n • e.symm y.1 = 0
    rw [← map_zsmul, show n • (y : B) = 0 from y.2, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add e x.1 y.1)

section Setup

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- A smooth connected curve `C` over a field `k` is smooth of relative dimension one: it is
regular and connected, hence irreducible, and has dimension one. -/
theorem IsConnectedCurve.smoothOfRelativeDimension_one (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] : SmoothOfRelativeDimension 1 f := by
  have := IsConnectedCurve.connectedSpace' f
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := IsRegular.of_smooth f
  have := IsRegular.irreducibleSpace C
  exact (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).2
    (by simpa using IsConnectedCurve.krullDim_eq_one (f := f))

/-- A smooth connected curve over a separably closed field is geometrically integral: it is
geometrically connected, and smooth, hence geometrically reduced and, being geometrically
connected, geometrically irreducible. -/
theorem IsConnectedCurve.geometricallyIntegral [IsSepClosed k] (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] : GeometricallyIntegral f := by
  have := IsConnectedCurve.connectedSpace' f
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : GeometricallyConnected (C ↘ Spec (.of k)) := GeometricallyConnected.of_isSepClosed C
  have : Smooth (C ↘ Spec (.of k)) := ‹Smooth f›
  have := GeometricallyReduced.of_smooth (C ↘ Spec (.of k))
  have := GeometricallyIrreducible.of_smooth_of_geometricallyConnected (C ↘ Spec (.of k))
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible
    (C ↘ Spec (.of k))

end Setup

/-- A proper geometrically integral group scheme `A` over a field which is smooth of relative
dimension `g` is an abelian variety of dimension `g`. -/
theorem IsAbelianVariety.exists_dim_eq_of_smoothOfRelativeDimension {K : Type u} [Field K]
    (A : Over (Spec (.of K))) (g : ℕ) [IsProper A.hom] [SmoothOfRelativeDimension g A.hom]
    [GeometricallyIntegral A.hom] : ∃ _ : IsAbelianVariety A, IsAbelianVariety.dim A = g := by
  have : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  have := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsAbelianVariety A :=
    { toIsProper := inferInstance, toSmooth := inferInstance, toConnectedSpace := inferInstance }
  refine ⟨this, ?_⟩
  have h := IsAbelianVariety.topologicalKrullDim_eq A
  rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension A.hom g] at h
  exact_mod_cast h.symm

section Jacobian

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} [C.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))]
  [GeometricallyIntegral (C ↘ Spec (.of k))]

/-- **`Pic⁰` of a curve via its Jacobian.** Let `C` be a smooth proper geometrically integral
curve of genus `g` over an algebraically closed field `k`, and let `n ≥ 1` be prime to
`char k`. Then `Pic⁰(C)[n] ≅ (ℤ/n)^{2g}` and `Pic⁰(C)` is `n`-divisible: `Pic⁰(C) ≅ J(k)` for
the Jacobian `J` (`AlgebraicGeometry.exists_jacobian`), an abelian variety of dimension `g`,
and both statements hold for `J(k)`
(`AlgebraicGeometry.abelianVariety_estimate_of_isAlgClosed`). -/
theorem picardZero_torsionBy_and_divisible (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (AddSubgroup.torsionBy (Additive (picardZero k C)) n ≃+
      (Fin (2 * (C ↘ Spec (.of k)).genus) → ZMod n)) ∧
      ∀ p : picardZero k C, ∃ q, q ^ n = p := by
  obtain ⟨J, _, -, hp, hs, hg, -, ⟨ψ⟩⟩ := exists_jacobian (k := k) (X := C)
  obtain ⟨_, hdim⟩ :=
    IsAbelianVariety.exists_dim_eq_of_smoothOfRelativeDimension J (Scheme.arithmeticGenus k C)
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn Nat.cast_zero)
  have hchar : ¬ ringChar k ∣ n := fun h ↦ hn ((CharP.cast_eq_zero_iff k (ringChar k) n).2 h)
  obtain ⟨hc, -, hd, -⟩ := abelianVariety_estimate_of_isAlgClosed (ringChar k) J
  obtain ⟨e⟩ := hc n hn0 hchar
  rw [Scheme.genus_eq_arithmeticGenus, ← hdim]
  refine ⟨⟨(torsionByAddEquiv ψ.toAdditive n).trans e⟩, fun p ↦ ?_⟩
  obtain ⟨a, ha⟩ := hd n hn0 (ψ p)
  have ha' : a ^ n = ψ p := ha
  exact ⟨ψ.symm a, by rw [← map_pow, ha', MulEquiv.symm_apply_apply]⟩

omit [IsAlgClosed k] [GeometricallyIntegral (C ↘ Spec (.of k))] in
/-- An `n`-torsion class in `Pic(C)` with `n ≠ 0` has degree zero, since `ℤ` is torsion-free. -/
theorem mem_picardZero_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) {L : C.Pic} (hL : L ^ n = 1) :
    L ∈ picardZero k C := by
  rw [MonoidHom.mem_ker]
  have h : (Scheme.picDegreeHom k C L) ^ n = 1 := by rw [← map_pow, hL, map_one]
  rw [← ofAdd_toAdd (Scheme.picDegreeHom k C L), ← ofAdd_nsmul, ofAdd_eq_one,
    nsmul_eq_mul] at h
  rw [← ofAdd_toAdd (Scheme.picDegreeHom k C L), ofAdd_eq_one]
  exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast hn)

omit [IsAlgClosed k] [GeometricallyIntegral (C ↘ Spec (.of k))] in
/-- **`Pic(C)[n] = Pic⁰(C)[n]`.** On a smooth proper curve, an `n`-torsion class with `n ≠ 0`
has degree zero (`AlgebraicGeometry.mem_picardZero_of_pow_eq_one`). -/
noncomputable def torsionByPicardZeroAddEquiv {n : ℕ} (hn : n ≠ 0) :
    AddSubgroup.torsionBy (Additive (picardZero k C)) n ≃+
      AddSubgroup.torsionBy (Additive C.Pic) n where
  toFun x := ⟨.ofMul (x.1.toMul : C.Pic), AddSubgroup.torsionBy.nsmul_iff.2 <| by
    have hx := AddSubgroup.torsionBy.nsmul_iff.1 x.2
    exact congrArg (fun y : Additive (picardZero k C) ↦ Additive.ofMul (y.toMul : C.Pic)) hx⟩
  invFun y :=
    have hy : y.1.toMul ^ n = 1 := by
      rw [← toMul_nsmul, AddSubgroup.torsionBy.nsmul_iff.1 y.2]
      rfl
    ⟨.ofMul ⟨y.1.toMul, mem_picardZero_of_pow_eq_one hn hy⟩,
      AddSubgroup.torsionBy.nsmul_iff.2 <| by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact hy⟩
  left_inv x := rfl
  right_inv y := rfl
  map_add' x y := rfl

end Jacobian

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

omit [IsAlgClosed k] in
/-- **The curve estimate in degree zero.** Let `C` be a smooth proper connected curve over a
field `k`, and let `n ≥ 1` be prime to `char k`. Then `H⁰(C_ét, ℤ/n) ≅ ℤ/n`; this only uses
that `C` is connected, so `k` need not be algebraically closed.
(blueprint: `sk-thm-curveestimate`) -/
theorem IsCurve.nonempty_addEquiv_sheafH_constantZMod_zero (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f] (n : ℕ) (_hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.constantZMod n) 0 ≃+ ZMod n) :=
  have := IsConnectedCurve.connectedSpace' f
  Scheme.nonempty_addEquiv_sheafH_zero_constantZMod C n

/-- **The curve estimate in degree one.** Let `C` be a smooth proper connected curve of genus
`g` over an algebraically closed field `k`, and let `n ≥ 1` be prime to `char k`. Then
`H¹(C_ét, ℤ/n) ≅ (ℤ/n)^{2g}`.

The genus is `f.genus = dim_k H⁰(C, Ω¹_{C/k})`, the definition of the blueprint
(`sk-def-curve`). For a smooth proper curve it agrees, by Serre duality, with the arithmetic genus
`AlgebraicGeometry.Scheme.arithmeticGenus = dim_k H¹(C, 𝒪_C)` of the Riemann–Roch block
(`AlgebraicGeometry.Scheme.genus_eq_arithmeticGenus`), which is the dimension of the Jacobian.

After choosing a primitive `n`-th root of unity, `ℤ/n ≅ μₙ`, and `H¹(C, μₙ) ≅ Pic(C)[n]`
(`AlgebraicGeometry.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one_of_isProper`). Torsion
classes have degree zero, so `Pic(C)[n] = Pic⁰(C)[n]`, and `Pic⁰(C) ≅ J(k)` for the Jacobian
`J` gives `Pic⁰(C)[n] ≅ (ℤ/n)^{2g}` (`AlgebraicGeometry.picardZero_torsionBy_and_divisible`).
(blueprint: `sk-thm-curveestimate`) -/
theorem IsCurve.nonempty_addEquiv_sheafH_constantZMod_one (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.constantZMod n) 1 ≃+ (Fin (2 * f.genus) → ZMod n)) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have : NeZero (n : k) := ⟨hn⟩
  have : NeZero n := ⟨hn0⟩
  obtain ⟨-, -, ζ, hζ, -⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} k n
  let e₁ := ((Sheaf.functorH _ 1).mapIso
    (C.constantZModIsoRootsOfUnitySheaf n f hζ)).addCommGroupIsoToAddEquiv
  obtain ⟨e₂⟩ := nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one_of_isProper f n hn
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
    IsConnectedCurve.smoothOfRelativeDimension_one f
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  have : GeometricallyIntegral (C ↘ Spec (.of k)) := IsConnectedCurve.geometricallyIntegral f
  obtain ⟨⟨e₃⟩, -⟩ := picardZero_torsionBy_and_divisible (k := k) (C := C) n hn
  exact ⟨e₁.trans (e₂.trans ((torsionByAddEquiv
    (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C).symm n).trans
      ((torsionByPicardZeroAddEquiv hn0).symm.trans e₃)))⟩

/-- **The curve estimate in degree two.** Let `C` be a smooth proper connected curve over an
algebraically closed field `k`, and let `n ≥ 1` be prime to `char k`. Then
`H²(C_ét, ℤ/n) ≅ ℤ/n`.

The isomorphism depends on the choice of a primitive `n`-th root of unity, that is, of an
isomorphism `μₙ ≅ ℤ/n` of étale sheaves, so it is only asserted to exist. A connected curve has
dimension exactly one (`AlgebraicGeometry.IsConnectedCurve.krullDim_eq_one`); without this
`Spec k` would be a smooth proper connected curve with `H² = 0`.

After choosing a primitive `n`-th root of unity, `ℤ/n ≅ μₙ`, and `H²(C, μₙ) ≅ Pic(C)/n`
(`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two_of_smooth`). The
degree modulo `n` identifies `Pic(C)/n` with `ℤ/n`: the degree is surjective, and a class of
degree divisible by `n` is an `n`-th power since `Pic(C) ≅ ℤ × Pic⁰(C)` and `Pic⁰(C)` is
`n`-divisible.
(blueprint: `sk-thm-curveestimate`) -/
theorem IsCurve.nonempty_addEquiv_sheafH_constantZMod_two (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.constantZMod n) 2 ≃+ ZMod n) := by
  have := IsConnectedCurve.nonempty f
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have : NeZero (n : k) := ⟨hn⟩
  have : NeZero n := ⟨hn0⟩
  obtain ⟨-, -, ζ, hζ, -⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} k n
  let e₁ := ((Sheaf.functorH _ 2).mapIso
    (C.constantZModIsoRootsOfUnitySheaf n f hζ)).addCommGroupIsoToAddEquiv
  obtain ⟨e₂⟩ := nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two_of_smooth f n hn
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
    IsConnectedCurve.smoothOfRelativeDimension_one f
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  have : GeometricallyIntegral (C ↘ Spec (.of k)) := IsConnectedCurve.geometricallyIntegral f
  obtain ⟨-, hdiv⟩ := picardZero_torsionBy_and_divisible (k := k) (C := C) n hn
  obtain ⟨σ, hσ⟩ := Scheme.exists_mulEquiv_prod_ker_picDegreeHom (k := k) (C := C)
  let E := Scheme.Pic.toCohomologicalPicardGroupAddEquiv C
  -- the degree modulo `n`, on `H¹(C, 𝔾ₘ)`
  let φ : C.CohomologicalPicardGroup →+ ZMod n :=
    ((Int.castAddHom (ZMod n)).comp (Scheme.picDegreeHom k C).toAdditiveLeft).comp
      E.symm.toAddMonoidHom
  have hφ (x : C.CohomologicalPicardGroup) :
      φ x = ((Scheme.picDegreeHom k C (E.symm x).toMul).toAdd : ZMod n) := rfl
  have hsurj : Function.Surjective φ := by
    intro a
    obtain ⟨d, rfl⟩ := ZMod.intCast_surjective a
    obtain ⟨L, hL⟩ := Scheme.surjective_picDegreeHom (k := k) (C := C) (.ofAdd d)
    exact ⟨E (.ofMul L), by rw [hφ, E.symm_apply_apply, toMul_ofMul, hL, toAdd_ofAdd]⟩
  have hker : φ.ker = (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (n : ℤ)).range := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range, hφ, ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨m, hm⟩
      obtain ⟨q, hq⟩ := hdiv (σ (E.symm x).toMul).2
      have h : σ (E.symm x).toMul = (Multiplicative.ofAdd m, q) ^ n := by
        refine Prod.ext ?_ ?_
        · rw [Prod.pow_fst, hσ, ← ofAdd_nsmul, nsmul_eq_mul, ← hm, ofAdd_toAdd]
        · rw [Prod.pow_snd, hq]
      refine ⟨E (.ofMul (σ.symm (.ofAdd m, q))), ?_⟩
      rw [zsmulAddGroupHom_apply, ← map_zsmul, ← E.apply_symm_apply x]
      congr 1
      apply Additive.toMul.injective
      rw [toMul_zsmul, toMul_ofMul, zpow_natCast, ← σ.symm_apply_apply (E.symm x).toMul, h,
        map_pow]
    · rintro ⟨y, rfl⟩
      refine ⟨(Scheme.picDegreeHom k C (E.symm y).toMul).toAdd, ?_⟩
      rw [zsmulAddGroupHom_apply, map_zsmul, toMul_zsmul, map_zpow, toAdd_zpow, smul_eq_mul]
  rw [← hker] at e₂
  exact ⟨e₁.trans (e₂.trans (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj))⟩

/-- **The curve estimate.** Let `C` be a smooth proper connected curve of genus `g` over an
algebraically closed field `k`, and let `n ≥ 1` be prime to `char k`. Then

`H⁰(C_ét, ℤ/n) ≅ ℤ/n`, `H¹(C_ét, ℤ/n) ≅ (ℤ/n)^{2g}`, `H²(C_ét, ℤ/n) ≅ ℤ/n`, and
`H^q(C_ét, ℤ/n) = 0` for `q ≥ 3`.

Degree zero is `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_zero`; degree one
(`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_one`) is `Pic(C)[n]`, which is
`Pic⁰(C)[n] = J(k)[n] ≅ (ℤ/n)^{2g}`; degree two
(`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_two`) is
`Pic(C)/n = ℤ/n ⊕ J(k)/n = ℤ/n`; the vanishing is
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le` for the torsion sheaf `ℤ/n`.
(blueprint: `sk-the-final-theorem-the-curve-estimate--remark-1`,
`the-final-theorem-the-curve-estimate--remark-1`) -/
theorem IsCurve.sheafH_constantZMod (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    [IsProper f] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.constantZMod n) 0 ≃+ ZMod n) ∧
      Nonempty (Sheaf.H (C.constantZMod n) 1 ≃+ (Fin (2 * f.genus) → ZMod n)) ∧
      Nonempty (Sheaf.H (C.constantZMod n) 2 ≃+ ZMod n) ∧
      ∀ q, 3 ≤ q → Subsingleton (Sheaf.H (C.constantZMod n) q) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  exact ⟨nonempty_addEquiv_sheafH_constantZMod_zero f n hn,
    nonempty_addEquiv_sheafH_constantZMod_one f n hn,
    nonempty_addEquiv_sheafH_constantZMod_two f n hn,
    fun q hq ↦ subsingleton_sheafH_of_three_le f _ (C.isTorsion_constantZMod hn0) q hq⟩

end AlgebraicGeometry
