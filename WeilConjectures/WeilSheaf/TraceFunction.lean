/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PointCount
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseRank
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.StalkConstantTwist
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.StalkUpperStar
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Trace

/-!
# Computations of trace functions

The trace function `t_{F,n}(y)` of a Weil sheaf at an `𝔽_{qⁿ}`-rational point `y` over a closed
point `x` of degree `d` is the trace of `F_x^{n/d}` on the stalk at `x`
(`AlgebraicGeometry.WeilSheaf.traceFunction_eq_trace_frobeniusEnd_stalk_pow`). This file
computes it for constant twists, direct sums and duals, and bounds it for sheaves with upper
weight bounds.

## Main results

- `AlgebraicGeometry.WeilSheaf.traceFunction_constantTwist`: `t_{F ⊗ 𝓑_b, n} = bⁿ t_{F, n}`.
- `AlgebraicGeometry.WeilSheaf.traceFunction_biprod`: additivity in direct sums.
- `AlgebraicGeometry.WeilSheaf.map_traceFunction_dual`: for `F` punctually pure of weight `0`,
  the trace function of the dual is the complex conjugate.
- `AlgebraicGeometry.WeilSheaf.norm_map_traceFunction_le`: the bound
  `|ι t_{F,n}(y)| ≤ dim F_x · q^{nw/2}` for weights at most `w`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

/-- The image of a rational point with values in a finite field is a point with finite residue
field: its residue field embeds into the finite field. -/
theorem Scheme.Hom.base_mem_finitePoints_of_fieldPoints {X : Scheme.{u}} {k : Type u}
    [Field k] (f : X.Hom (Spec (.of k))) (K : Type u) [Field K] [Algebra k K] [Finite K]
    (p : f.fieldPoints K) (z : Spec (.of K)) : p.1.base z ∈ X.finitePoints := by
  have hz : p.1.base default = p.1.base z := congrArg p.1.base (Subsingleton.elim _ _)
  obtain ⟨φ, -⟩ := (f.exists_fieldPoints_base_eq_iff K (p.1.base z)).1 ⟨p, hz⟩
  exact X.mem_finitePoints.mpr (Finite.of_injective _ φ.hom.injective)

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The closed point under an `𝔽_{qⁿ}`-rational point. -/
noncomputable def finitePointOfFieldPoint {n : ℕ}
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    X.finitePoints :=
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  ⟨_, (X ↘ Spec (CommRingCat.of k₀)).base_mem_finitePoints_of_fieldPoints _ y
    (IsLocalRing.closedPoint _)⟩

/-- The degree of the closed point under an `𝔽_{qⁿ}`-rational point divides `n`. -/
theorem degreeOver_finitePointOfFieldPoint_dvd {n : ℕ}
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (X ↘ Spec (CommRingCat.of k₀)).degreeOver (finitePointOfFieldPoint y).1 ∣ n :=
  (X ↘ Spec (CommRingCat.of k₀)).degreeOver_dvd_of_fieldPoints n y

variable (F G : WeilSheaf k₀ l X)

/-- The trace function at `y` is the trace of the `n / d`-th power of the local Frobenius at
the closed point under `y`, of degree `d`. -/
theorem traceFunction_eq_trace (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    F.traceFunction n y = LinearMap.trace (PadicAlgCl l) _
      ((F.stalk (finitePointOfFieldPoint y)).frobeniusEnd ^
        (n / (X ↘ Spec (CommRingCat.of k₀)).degreeOver (finitePointOfFieldPoint y).1)) :=
  F.traceFunction_eq_trace_frobeniusEnd_stalk_pow n y _ rfl

/-- The trace function of the constant twist `F ⊗ 𝓑_b` is `bⁿ` times that of `F`: at a closed
point of degree `d` the twist multiplies the local Frobenius by `b^d`. -/
theorem traceFunction_constantTwist (b : (PadicAlgCl l)ˣ) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (F.constantTwist b).traceFunction n y = (b : PadicAlgCl l) ^ n * F.traceFunction n y := by
  rw [traceFunction_eq_trace, traceFunction_eq_trace]
  obtain ⟨e⟩ := F.nonempty_equiv_stalk_constantTwist b (finitePointOfFieldPoint y)
  rw [← e.trace_frobeniusEnd_pow, FrobeniusModule.trace_frobeniusEnd_rescale_pow _
    (pow_ne_zero _ b.ne_zero), ← pow_mul,
    Nat.mul_div_cancel' (degreeOver_finitePointOfFieldPoint_dvd y)]

/-- The trace function of a direct sum is the sum of the trace functions. -/
theorem traceFunction_biprod (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (F ⊞ G).traceFunction n y = F.traceFunction n y + G.traceFunction n y := by
  rw [traceFunction_eq_trace, traceFunction_eq_trace, traceFunction_eq_trace]
  obtain ⟨e⟩ := nonempty_equiv_stalk_biprod F G (finitePointOfFieldPoint y)
  rw [← e.trace_frobeniusEnd_pow, FrobeniusModule.trace_frobeniusEnd_prod_pow]

variable {F} in
/-- For a lisse sheaf `F` punctually `ι`-pure of weight `0`, the trace function of the dual
`F^∨` is the complex conjugate of that of `F`: the local eigenvalues of the dual are the inverses
of those of `F`, which have absolute value `1`. -/
theorem map_traceFunction_dual {ι : PadicAlgCl l →+* ℂ} (hF : F.IsLisse)
    (h : F.IsPunctuallyPureOfWeight ι 0) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ι ((F.dual hF).traceFunction n y) = (starRingEnd ℂ) (ι (F.traceFunction n y)) := by
  rw [traceFunction_eq_trace, traceFunction_eq_trace]
  obtain ⟨e⟩ := nonempty_equiv_stalk_dual hF (finitePointOfFieldPoint y)
  rw [← e.trace_frobeniusEnd_pow]
  exact (h _).map_trace_frobeniusEnd_dual_pow _

variable {F} in
/-- If `F` has weights at most `w`, then `|ι t_{F,n}(y)| ≤ dim F_x · q^{nw/2}`, `x` the closed
point under `y`: the trace of `F_x^{n/d}` is a sum of `dim F_x` eigenvalue powers, each of
absolute value at most `(q^{dw/2})^{n/d} = q^{nw/2}`. -/
theorem norm_map_traceFunction_le {ι : PadicAlgCl l →+* ℂ} {w : ℝ} (h : F.HasWeightsAtMost ι w)
    (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ‖ι (F.traceFunction n y)‖ ≤
      Module.finrank (PadicAlgCl l) (F.stalk (finitePointOfFieldPoint y)).carrier *
        ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ n := by
  rw [traceFunction_eq_trace]
  refine ((h _).norm_map_trace_frobeniusEnd_pow_le _).trans_eq ?_
  obtain ⟨c, hc⟩ := degreeOver_finitePointOfFieldPoint_dvd y
  set d := (X ↘ Spec (CommRingCat.of k₀)).degreeOver (finitePointOfFieldPoint y).1
  have hq : (0 : ℝ) ≤ Nat.card k₀ := Nat.cast_nonneg _
  congr 1
  rcases Nat.eq_zero_or_pos d with hd | hd
  · rw [hd, zero_mul] at hc
    rw [hd, Nat.div_zero, pow_zero]
    conv_rhs => rw [hc, pow_zero]
  · rw [show n / d = c by rw [hc, Nat.mul_div_cancel_left _ hd]]
    conv_rhs => rw [hc]
    rw [Scheme.Hom.residueCard, Nat.cast_pow,
      ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), ← Real.rpow_mul hq, ← Real.rpow_mul hq]
    congr 1
    push_cast
    ring

variable {F} in
/-- **The rank of a lisse Weil sheaf is bounded**: on a `k₀`-scheme quasi-compact over `k₀`, the
stalks of a lisse Weil sheaf have bounded dimension, the geometric fiber being quasi-compact
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_forall_finrank_le`). -/
theorem IsLisse.exists_forall_finrank_stalk_le [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (hF : F.IsLisse) :
    ∃ N : ℕ, ∀ x : X.finitePoints, Module.finrank (PadicAlgCl l) (F.stalk x).carrier ≤ N := by
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure := by
    unfold Scheme.Hom.geometricFiberToAlgebraicClosure Scheme.Hom.geometricFiber
    infer_instance
  have : CompactSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    QuasiCompact.compactSpace_of_compactSpace
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  obtain ⟨N, hN⟩ := ProEtale.IsAdicLisseSheaf.exists_forall_finrank_le hF
  exact ⟨N, fun x ↦ hN _ _⟩



/-- Isomorphic Weil sheaves have isomorphic stalks, with their Frobenius. -/
theorem nonempty_equiv_stalkAt_of_iso {F G : WeilSheaf k₀ l X} (e : F ≅ G)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s) :
    Nonempty ((F.stalkAt s m hs).Equiv (G.stalkAt s m hs)) := by
  have h₁ : (stalkAtMap s m hs e.hom).comp (stalkAtMap s m hs e.inv) = .id := by
    refine LinearMap.ext fun y ↦ ?_
    change stalkAtMap s m hs e.hom (stalkAtMap s m hs e.inv y) = y
    rw [← stalkAtMap_comp, e.inv_hom_id, stalkAtMap_id]
  have h₂ : (stalkAtMap s m hs e.inv).comp (stalkAtMap s m hs e.hom) = .id := by
    refine LinearMap.ext fun y ↦ ?_
    change stalkAtMap s m hs e.inv (stalkAtMap s m hs e.hom y) = y
    rw [← stalkAtMap_comp, e.hom_inv_id, stalkAtMap_id]
  let E : (F.stalkAt s m hs).carrier ≃ₗ[PadicAlgCl l] (G.stalkAt s m hs).carrier :=
    LinearEquiv.ofLinearMap _ _ h₁ h₂
  have hc : ⇑E = ⇑(stalkAtMap s m hs e.hom) := LinearEquiv.coe_ofLinearMap _ _ h₁ h₂
  -- passing through `LinearEquiv.coe_ofLinearMap` explicitly keeps the kernel check fast
  exact ⟨⟨E, fun x ↦ (congrFun hc _).trans
    ((stalkAtMap_frobenius s m hs e.hom x).trans
      (congrArg (G.stalkAt s m hs).frobenius (congrFun hc x).symm))⟩⟩

/-- Isomorphic Weil sheaves have the same trace function. -/
theorem traceFunction_eq_of_iso {F G : WeilSheaf k₀ l X} (e : F ≅ G) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    F.traceFunction n y = G.traceFunction n y := by
  rw [traceFunction_eq_trace, traceFunction_eq_trace]
  obtain ⟨e'⟩ := nonempty_equiv_stalkAt_of_iso e _ _
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
      (X ↘ Spec (CommRingCat.of k₀)) (finitePointOfFieldPoint y))
  exact (e'.trace_frobeniusEnd_pow _).symm

section UpperStar

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]

/-- The image of an `𝔽_{qⁿ}`-rational point under a morphism of `k₀`-schemes. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.Hom.mapFieldPoints (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] {K : Type u} [Field K] [Algebra k₀ K]
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    (Y ↘ Spec (CommRingCat.of k₀)).fieldPoints K :=
  ⟨y.1 ≫ φ, by rw [Category.assoc, comp_over]; exact y.2⟩

/-- Over an algebraically closed field the traces of the powers of an endomorphism depend only
on its characteristic polynomial. -/
lemma _root_.LinearMap.trace_pow_eq_of_charpoly_eq {K V W : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {f : Module.End K V} {g : Module.End K W}
    (h : f.charpoly = g.charpoly) (k : ℕ) :
    LinearMap.trace K V (f ^ k) = LinearMap.trace K W (g ^ k) := by
  rw [LinearMap.trace_pow_eq_sum_pow_roots_charpoly, LinearMap.trace_pow_eq_sum_pow_roots_charpoly,
    h]

/-- The local Frobenius of the pullback `φ^* F` at a closed point `z` over `x = φ z` has the
characteristic polynomial of `Fₓʳ`, `r = [κ(z) : κ(x)]`. -/
theorem charpoly_frobeniusEnd_stalk_upperStar (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l Y) (z : X.finitePoints) :
    (((WeilSheaf.upperStar φ).obj F).stalk z).frobeniusEnd.charpoly =
      ((F.stalk ⟨φ.base z.1, Scheme.Hom.map_mem_finitePoints φ z.2⟩).frobeniusEnd ^
        ((X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 /
          (Y ↘ Spec (CommRingCat.of k₀)).degreeOver (φ.base z.1))).charpoly := by
  have hφ := comp_over φ (Spec (CommRingCat.of k₀))
  let x : Y.finitePoints := ⟨φ.base z.1, Scheme.Hom.map_mem_finitePoints φ z.2⟩
  have hdvd : (Y ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ∣
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 := by
    have := Scheme.Hom.degreeOver_dvd_degreeOver_comp φ (Y ↘ Spec (CommRingCat.of k₀)) z.2
    rwa [hφ] at this
  set s := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint z
  have ht := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) z
  have ht' : (s ≫ Scheme.Hom.geometricFiberMap φ hφ) ≫
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1).hom =
      (specGeometricFrobenius k₀ ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1).hom ≫
        (s ≫ Scheme.Hom.geometricFiberMap φ hφ) := by
    rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow,
      ← Category.assoc, ht, Category.assoc]
  have : IsIso (𝟙 _ : (Scheme.Hom.geometricFiberMap φ hφ)^*[WeilCoefficients.{u} l].obj
      F.obj.carrier.X ⟶ ((WeilSheaf.upperStar φ).obj F).obj.carrier.X) :=
    inferInstanceAs (IsIso (𝟙 ((Scheme.Hom.geometricFiberMap φ hφ)^*[WeilCoefficients.{u} l].obj
      F.obj.carrier.X)))
  obtain ⟨e₁⟩ := nonempty_equiv_stalkAt_of_upperStar (G := (WeilSheaf.upperStar φ).obj F)
    (θ := 𝟙 _) (upperStar_frobeniusStr_compatible (φ := φ) F) s _ ht ht'
  have hbase : (((Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) ≫
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) = x.1 :=
    Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ x
  have hss' : (((Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) ≫
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      ((s ≫ Scheme.Hom.geometricFiberMap φ hφ) ≫
        (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
          (IsLocalRing.closedPoint (AlgebraicClosure k₀)) := by
    rw [hbase, Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Category.assoc]
    exact (congrArg φ.base
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ z)).symm
  have hc := F.charpoly_frobeniusEnd_stalkAt_of_dvd _ _ hss' (hbase ▸ x.2) hdvd
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow _ x) ht'
  exact e₁.charpoly_frobeniusEnd.trans hc

/-- The trace function of a pullback `φ^* F` at a rational point `y` is that of `F` at the image
`φ ∘ y`. -/
theorem traceFunction_upperStar (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l Y) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((WeilSheaf.upperStar φ).obj F).traceFunction n y = F.traceFunction n (φ.mapFieldPoints y) := by
  set z := finitePointOfFieldPoint y
  have hx : (φ.mapFieldPoints y).1.base (IsLocalRing.closedPoint _) = φ.base z.1 := rfl
  rw [traceFunction_eq_trace, F.traceFunction_eq_trace_frobeniusEnd_stalk_pow n _
    ⟨φ.base z.1, Scheme.Hom.map_mem_finitePoints φ z.2⟩ hx,
    LinearMap.trace_pow_eq_of_charpoly_eq (charpoly_frobeniusEnd_stalk_upperStar φ F z), ← pow_mul]
  have hφ := comp_over φ (Spec (CommRingCat.of k₀))
  have hdvd : (Y ↘ Spec (CommRingCat.of k₀)).degreeOver (φ.base z.1) ∣
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 := by
    have := Scheme.Hom.degreeOver_dvd_degreeOver_comp φ (Y ↘ Spec (CommRingCat.of k₀)) z.2
    rwa [hφ] at this
  have hdz := degreeOver_finitePointOfFieldPoint_dvd y
  congr 2
  obtain ⟨a, ha⟩ := hdvd
  obtain ⟨b, hb⟩ := hdz
  have hd0 : (Y ↘ Spec (CommRingCat.of k₀)).degreeOver (φ.base z.1) ≠ 0 :=
    Scheme.Hom.degreeOver_ne_zero _ (Scheme.Hom.map_mem_finitePoints φ z.2)
  have hz0 : (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 ≠ 0 :=
    Scheme.Hom.degreeOver_ne_zero _ z.2
  change (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 /
      (Y ↘ Spec (CommRingCat.of k₀)).degreeOver (φ.base z.1) *
      (n / (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1) =
    n / (Y ↘ Spec (CommRingCat.of k₀)).degreeOver (φ.base z.1)
  rw [ha] at hb hz0 ⊢
  conv_rhs => rw [hb]
  conv_lhs => rw [hb]
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0), Nat.mul_div_cancel_left _
    (Nat.pos_of_ne_zero hz0), mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]

end UpperStar

end WeilSheaf

end AlgebraicGeometry
