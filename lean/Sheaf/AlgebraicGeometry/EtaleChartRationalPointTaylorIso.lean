/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Inverse
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables
import WeilConjectures.RingTheory.PairHenselizationCompletionData
import Sheaf.AlgebraicGeometry.EtaleChartFiniteJets

/-!
# Taylor isomorphism at a rational point of an étale chart

Source: Stacks Project, etale.tex, Tag 039M (lemma-characterize-etale-completions)
and the following residue-degree remark; the polynomial-completion coordinate calculation
(blueprint: lem-trf-etale-chart-rational-point-taylor-iso).

The auxiliary declarations only spell out the base change, its structural scalar map,
the shifted coordinate germs, and the finite-level condition on the Taylor map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.EtaleChartTaylor

/-- The specified field-extension base change of the chart domain.
Source: Stacks Project, Tag 039M, applied after base change
(blueprint: lem-trf-etale-chart-rational-point-taylor-iso). -/
abbrev baseChange {k : Type u} [Field k] {U : Scheme.{u}}
    (p : U ⟶ Spec (.of k)) (L : Type u) [Field L] [Algebra k L] : Scheme.{u} :=
  pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L)))

/-- Scalars in the actual stalk, induced by the second projection of the base change.
Source: Stacks Project, Tag 039M and the structural map in its application to a chart
(blueprint: lem-trf-etale-chart-rational-point-taylor-iso). -/
def scalarMap {k L : Type u} [Field k] [Field L] [Algebra k L]
    {U : Scheme.{u}} (p : U ⟶ Spec (.of k)) (b : baseChange p L) :
    L →+* (baseChange p L).presheaf.stalk b :=
  ((Scheme.ΓSpecIso (.of L)).inv ≫
    (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L)))).appTop ≫
      (baseChange p L).presheaf.germ ⊤ b trivial).hom

/-- The structural residue-field map used to express rationality, without identifying
an abstractly isomorphic field with the structural extension.
Source: Stacks Project, Tag 039M, residue-degree remark
(blueprint: lem-trf-etale-chart-rational-point-taylor-iso). -/
def residueMap {k L : Type u} [Field k] [Field L] [Algebra k L]
    {U : Scheme.{u}} (p : U ⟶ Spec (.of k)) (b : baseChange p L) :
    L →+* (baseChange p L).residueField b :=
  ((baseChange p L).residue b).hom.comp (scalarMap p b)

/-- Pull back the chart coordinate and then take its germ at the specified point.
Source: Stacks Project, Tag 039M, polynomial coordinates in its chart application
(blueprint: lem-trf-etale-chart-rational-point-taylor-iso). -/
def coordinate {k L : Type u} [Field k] [Field L] [Algebra k L]
    {U : Scheme.{u}} (p : U ⟶ Spec (.of k)) {n : ℕ}
    (t : U ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)))
    (b : baseChange p L) (i : Fin n) : (baseChange p L).presheaf.stalk b :=
  (baseChange p L).presheaf.germ ⊤ b trivial
    ((pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫ t).appTop
      (AffineSpace.coord (Spec (.of k)) (ULift.up i)))

/-- The germ `t_i - c_i`, where `c_i` is the residue of `t_i` under the inverse of the
bijective structural residue-field map. No coefficient field is chosen in the local ring.
Source: Stacks Project, Tag 039M, translated polynomial coordinates
(blueprint: lem-trf-etale-chart-rational-point-taylor-iso). -/
def centeredCoordinate {k L : Type u} [Field k] [Field L] [Algebra k L]
    {U : Scheme.{u}} (p : U ⟶ Spec (.of k)) {n : ℕ}
    (t : U ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)))
    (b : baseChange p L) (hb : Function.Bijective (residueMap p b))
    (i : Fin n) : (baseChange p L).presheaf.stalk b :=
  coordinate p t b i - scalarMap p b
    ((RingEquiv.ofBijective (residueMap p b) hb).symm
      ((baseChange p L).residue b (coordinate p t b i)))

/-- The precise finite-level Taylor condition. The first conjunct says that the ring map
is an `L`-algebra map for the specified structural scalars; `truncTotal r` is exactly
`sum_{|E| < r} a_E T^E`, so evaluation is the finite sum in the statement.
Source: Stacks Project, Tag 039M and the polynomial-completion calculation
(blueprint: lem-trf-etale-chart-rational-point-taylor-iso). -/
def IsExpansion {L : Type u} [Field L] {A : Type v} [CommRing A] [IsLocalRing A]
    {n : ℕ} (ι : L →+* A) (z : Fin n → A)
    (θ : MvPowerSeries (Fin n) L →+* AdicCompletion (IsLocalRing.maximalIdeal A) A) :
    Prop :=
  (∀ a : L, θ (MvPowerSeries.C a) =
    algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) (ι a)) ∧
  ∀ (r : ℕ), 1 ≤ r → ∀ f : MvPowerSeries (Fin n) L,
    AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) r (θ f) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ r)
        (MvPolynomial.eval₂ ι z (MvPowerSeries.truncTotal r f))

private theorem taylor_of_finite_jets
    {L : Type u} [Field L] {A : Type v} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (n : ℕ) (ι : L →+* A) (z : Fin n → A)
    (hgen : Ideal.map (MvPolynomial.eval₂Hom ι z)
      (MvPolynomial.idealOfVars (Fin n) L) = IsLocalRing.maximalIdeal A)
    (hjets : ∀ r : ℕ, ∃ e :
        (MvPolynomial (Fin n) L ⧸ MvPolynomial.idealOfVars (Fin n) L ^ r) ≃+*
          (A ⧸ IsLocalRing.maximalIdeal A ^ r),
      ∀ a : MvPolynomial (Fin n) L,
        e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (MvPolynomial.eval₂ ι z a)) :
    ∃ θ : MvPowerSeries (Fin n) L →+*
        AdicCompletion (IsLocalRing.maximalIdeal A) A,
      IsExpansion ι z θ ∧
      (∀ θ' : MvPowerSeries (Fin n) L →+*
          AdicCompletion (IsLocalRing.maximalIdeal A) A,
        IsExpansion ι z θ' → θ' = θ) ∧
      Function.Bijective θ ∧ IsLocalHom θ ∧
      (∃ hlocal : IsLocalRing
          (AdicCompletion (IsLocalRing.maximalIdeal A) A),
        Ideal.map θ (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin n) (R := L)))) =
          @IsLocalRing.maximalIdeal
            (AdicCompletion (IsLocalRing.maximalIdeal A) A) _ hlocal) ∧
      (∀ i : Fin n, θ (MvPowerSeries.X i) =
        algebraMap A
          (AdicCompletion (IsLocalRing.maximalIdeal A) A) (z i)) ∧
      (∀ f : MvPowerSeries (Fin n) L,
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A)
          1 (θ f) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ 1)
          (ι (MvPowerSeries.constantCoeff f))) ∧
      (n = 0 → Function.Bijective ι ∧
        Function.Bijective
          ((algebraMap A
            (AdicCompletion (IsLocalRing.maximalIdeal A) A)).comp ι)) := by
  classical
  let m := IsLocalRing.maximalIdeal A
  let P := MvPolynomial (Fin n) L
  let I := MvPolynomial.idealOfVars (Fin n) L
  let f : P →+* A := MvPolynomial.eval₂Hom ι z
  have hbij (r : ℕ) (_hr : 1 ≤ r) : Function.Bijective
      (Ideal.quotientMap ((I ^ r).map f) f Ideal.le_comap_map) := by
    obtain ⟨e, he⟩ := hjets r
    have htransfer (K : Ideal A) (hK : K = m ^ r) (hle : I ^ r ≤ K.comap f) :
        Function.Bijective (Ideal.quotientMap K f hle) := by
      subst K
      have hq : Ideal.quotientMap (m ^ r) f hle = e.toRingHom := by
        apply RingHom.ext
        intro x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact (he a).symm
      rw [hq]
      exact e.bijective
    exact htransfer _ (by rw [Ideal.map_pow, hgen]) _
  have hcompletion := RingTheory.pair_henselization_completion_data P A I f hbij
  rw [hgen] at hcompletion
  obtain ⟨E, hE, _⟩ := hcompletion
  let S := (MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) L).toRingEquiv
  let θ : MvPowerSeries (Fin n) L →+* AdicCompletion m A :=
    E.toRingHom.comp S.toRingHom
  have hθbij : Function.Bijective θ := E.bijective.comp S.bijective
  have hθpoly (a : P) : θ a = algebraMap A (AdicCompletion m A) (f a) := by
    apply AdicCompletion.ext_evalₐ
    intro r
    apply (hE r _ a ?_).trans
    · exact (AdicCompletion.evalₐ_of m r (f a)).symm
    · change AdicCompletion.evalₐ I r (MvPowerSeries.toAdicCompletion (Fin n) L a) = _
      rw [MvPowerSeries.toAdicCompletion_coe]
      exact AdicCompletion.evalₐ_of I r a
  have hθC (a : L) : θ (MvPowerSeries.C a) =
      algebraMap A (AdicCompletion m A) (ι a) := by
    rw [← MvPolynomial.coe_C, hθpoly]
    exact congrArg (algebraMap A (AdicCompletion m A)) (MvPolynomial.eval₂Hom_C ι z a)
  have hθeval (r : ℕ) (F : MvPowerSeries (Fin n) L) :
      AdicCompletion.evalₐ m r (θ F) =
        Ideal.Quotient.mk (m ^ r) (MvPolynomial.eval₂ ι z (F.truncTotal r)) := by
    apply hE r _ (F.truncTotal r)
    change AdicCompletion.evalₐ I r (MvPowerSeries.toAdicCompletion (Fin n) L F) = _
    rw [← AdicCompletion.factor_eval_eq_evalₐ I _ (by simp)]
    change Ideal.Quotient.factor (show I ^ r • ⊤ ≤ I ^ r by simp)
      ((MvPowerSeries.toAdicCompletion (Fin n) L F).val r) = _
    rw [MvPowerSeries.toAdicCompletion_apply_eq_mk_truncTotal]
    rfl
  have hexp : IsExpansion ι z θ := ⟨hθC, fun r _ F ↦ hθeval r F⟩
  have hunique (θ' : MvPowerSeries (Fin n) L →+* AdicCompletion m A)
      (hθ' : IsExpansion ι z θ') : θ' = θ := by
    apply RingHom.ext
    intro F
    apply AdicCompletion.ext_evalₐ
    intro r
    cases r with
    | zero =>
      have : Subsingleton (A ⧸ m ^ 0) := by
        simp only [pow_zero, Ideal.one_eq_top]
        infer_instance
      exact Subsingleton.elim _ _
    | succ r =>
      exact (hθ'.2 _ (Nat.succ_le_succ (Nat.zero_le r)) F).trans (hθeval _ F).symm
  let : IsLocalHom θ := IsLocalHom.of_surjective θ hθbij.2
  have hmax : Ideal.span (Set.range (MvPowerSeries.X (σ := Fin n) (R := L))) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) L) := by
    rw [← (MvPowerSeries.quotient_first_variables_kernels L n 0 (Nat.zero_le n)).2]
    ext F
    simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  have hres (F : MvPowerSeries (Fin n) L) :
      AdicCompletion.evalₐ m 1 (θ F) =
        Ideal.Quotient.mk (m ^ 1) (ι (MvPowerSeries.constantCoeff F)) := by
    rw [hθeval]
    have htrunc : F.truncTotal 1 = MvPolynomial.C (MvPowerSeries.constantCoeff F) := by
      ext d
      by_cases hd : d = 0
      · subst d
        simp [MvPowerSeries.coeff_truncTotal_eq_ite,
          MvPowerSeries.coeff_zero_eq_constantCoeff]
      · rw [MvPowerSeries.coeff_truncTotal_eq_zero F (by
          have := (Finsupp.degree_eq_zero_iff d).not.mpr hd; omega)]
        simp [MvPolynomial.coeff_C, Ne.symm hd]
    rw [htrunc, MvPolynomial.eval₂_C]
  refine ⟨θ, hexp, hunique, hθbij, inferInstance, ?_, ?_, hres, ?_⟩
  · refine ⟨inferInstance, ?_⟩
    rw [hmax]
    exact IsLocalRing.map_maximalIdeal_of_surjective θ hθbij.2
  · intro i
    rw [← MvPolynomial.coe_X, hθpoly]
    exact congrArg (algebraMap A (AdicCompletion m A)) (MvPolynomial.eval₂Hom_X' ι z i)
  · intro hn
    subst n
    have hCbij : Function.Bijective
        (MvPowerSeries.C : L →+* MvPowerSeries (Fin 0) L) := by
      exact (MvPowerSeries.isEmptyEquiv (Fin 0) L).symm.bijective
    have hcomp : θ.comp MvPowerSeries.C =
        (algebraMap A (AdicCompletion m A)).comp ι := by
      apply RingHom.ext
      intro a
      exact hθC a
    have hcompleted : Function.Bijective ((algebraMap A (AdicCompletion m A)).comp ι) := by
      rw [← hcomp]
      exact hθbij.comp hCbij
    refine ⟨⟨ι.injective, ?_⟩, hcompleted⟩
    intro a
    obtain ⟨c, hc⟩ := hcompleted.2 (algebraMap A (AdicCompletion m A) a)
    refine ⟨c, AdicCompletion.of_injective m A ?_⟩
    exact hc


/-- The unique Taylor map of an étale chart at a structurally rational point after any
field extension is a local-ring isomorphism, with the prescribed maximal ideal and residue
normalization. In dimension zero both structural scalar maps are isomorphisms.

Source: Stacks Project, etale.tex, Tag 039M and its residue-degree remark
(blueprint: lem-trf-etale-chart-rational-point-taylor-iso).

Proof:
1. Base change the chart using lem-weil-pbc-etale-scheme-base-change. In the polynomial
   spectrum (def-sbc-affine-space), evaluation at the coordinate values has kernel generated
   by X_i-c_i. Translation identifies the affine stalk with the localization at that ideal
   (lem-weil-pbc-affine-open-stalk-localization).
2. The polynomial ring and its localization are Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian and lem-weil-pbc-localization-noetherian.
   The chart domain is locally Noetherian by pqf-def-locnoeth and pqf-lem-locnoeth-lft,
   so its stalk is Noetherian by the affine-stalk localization theorem.
3. Etaleness supplies flatness and unramifiedness (def-weil-etale-morphism,
   def-weil-flat-morphism, def-weil-unramified-morphism). Apply
   lem-trf-unramified-maximal-ideal-residue-criterion to identify the extended maximal ideal.
   Rationality identifies the residue map with the identity. Apply
   lem-weil-pbc-flat-local-completion-iso to the actual stalk map.
4. Specialize lem-trf-monoid-completion-coefficients to the free monoid N^n over L,
   with weight total degree and coefficient maximal ideal zero. Its coefficient ring is
   MvPowerSeries (Fin n) L (def-weil-pbc-multivariate-power-series), and its level-r map
   is precisely the finite total-degree truncation.
5. Localization does not change these polynomial quotients: an element outside the
   evaluation ideal has invertible constant term, and its inverse modulo the r-th power
   is the finite geometric series. The resulting quotient isomorphisms commute with
   reduction. Their inverse limit identifies the polynomial and localized completions.
6. Compose the three isomorphisms. Their level-r formulas give IsExpansion and the
   coordinate images. Any second map with these reductions agrees in every component,
   hence agrees as a map of compatible sequences (def-weil-pbc-adic-completion).
7. The centered germs generate the stalk maximal ideal. By
   lem-weil-pbc-local-completion-local-ring its extension is the completion maximal ideal.
   The level-one formula is constant-coefficient evaluation, hence the residue map is
   the identity on L. For n=0 the source stalk is L, its maximal ideal is zero, and
   unramifiedness forces the target maximal ideal to be zero. Rationality then makes
   L -> O_{U_L,b} an isomorphism, and likewise its completion. -/
theorem exists_unique_taylor_iso
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    {U : Scheme.{u}} (p : U ⟶ Spec (.of k)) (n : ℕ)
    (t : U ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k))) [Etale t]
    (ht : t ≫ (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)) ↘ Spec (.of k)) = p)
    (b : baseChange p L) (hb : Function.Bijective (residueMap p b)) :
    ∃ θ : MvPowerSeries (Fin n) L →+*
        AdicCompletion (IsLocalRing.maximalIdeal ((baseChange p L).presheaf.stalk b))
          ((baseChange p L).presheaf.stalk b),
      IsExpansion (scalarMap p b) (centeredCoordinate p t b hb) θ ∧
      (∀ θ' : MvPowerSeries (Fin n) L →+*
          AdicCompletion (IsLocalRing.maximalIdeal ((baseChange p L).presheaf.stalk b))
            ((baseChange p L).presheaf.stalk b),
        IsExpansion (scalarMap p b) (centeredCoordinate p t b hb) θ' → θ' = θ) ∧
      Function.Bijective θ ∧ IsLocalHom θ ∧
      (∃ hlocal : IsLocalRing
          (AdicCompletion (IsLocalRing.maximalIdeal ((baseChange p L).presheaf.stalk b))
            ((baseChange p L).presheaf.stalk b)),
        Ideal.map θ (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin n) (R := L)))) =
          @IsLocalRing.maximalIdeal
            (AdicCompletion (IsLocalRing.maximalIdeal ((baseChange p L).presheaf.stalk b))
              ((baseChange p L).presheaf.stalk b)) _ hlocal) ∧
      (∀ i : Fin n, θ (MvPowerSeries.X i) =
        algebraMap ((baseChange p L).presheaf.stalk b)
          (AdicCompletion (IsLocalRing.maximalIdeal ((baseChange p L).presheaf.stalk b))
            ((baseChange p L).presheaf.stalk b)) (centeredCoordinate p t b hb i)) ∧
      (∀ f : MvPowerSeries (Fin n) L,
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal ((baseChange p L).presheaf.stalk b))
          1 (θ f) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal ((baseChange p L).presheaf.stalk b) ^ 1)
          (scalarMap p b (MvPowerSeries.constantCoeff f))) ∧
      (n = 0 → Function.Bijective (scalarMap p b) ∧
        Function.Bijective
          ((algebraMap ((baseChange p L).presheaf.stalk b)
            (AdicCompletion (IsLocalRing.maximalIdeal ((baseChange p L).presheaf.stalk b))
              ((baseChange p L).presheaf.stalk b))).comp (scalarMap p b))) := by
  obtain ⟨hnoeth, hgen, hjets⟩ := rational_point_finite_jets p n t ht b hb
  let : IsNoetherianRing ((baseChange p L).presheaf.stalk b) := hnoeth
  exact taylor_of_finite_jets n (scalarMap p b) (centeredCoordinate p t b hb) hgen hjets

end AlgebraicGeometry.EtaleChartTaylor
