/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.RingTheory.PopescuCoefficientStart
import WeilConjectures.RingTheory.PopescuCoefficientStep
import WeilConjectures.RingTheory.EssentiallySmoothSmallLocalModel
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.RingTheory.EssentiallySmoothComp

/-!
# Coefficient enlargement along fixed parameters

Fixed polynomial parameters can be rescaled by units so that their `2N`-th powers lie in the
singular ideal with coefficients in an enlarged Artinian coefficient solution, and the
annihilator conditions hold in `Λ`.

## Implementation details

Induct on the parameters. Faithfully flat ideal contraction writes `π_i^N` in the singular ideal of
the coefficient ring; clearing denominators and Ogoma's lemma give the rescaling factor, and
Tag 07FI enlarges the coefficient ring to contain the needed powers. The span of the preceding
powered parameters is unchanged (`prefix_span_update`). Finally
`exists_essentiallySmooth_small_local_model` shrinks the coefficient ring into `Type (max u v)`.
No polynomial reindexing or polynomial kernel conclusion is asserted.

## References

* [Stacks, Tag 07FJ]
* [Stacks, Tag 07FI]
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

private theorem prefix_span_update
    {R : Type u} [CommRing R] {d : ℕ} (uΛ t : Fin d → R)
    (i : Fin d) (l : R) (e : ℕ) (j : Fin d) (hji : j.val ≤ i.val) :
    Ideal.span {y | ∃ k : Fin d, k.val < j.val ∧
      y = (uΛ k * Function.update t i l k) ^ e} =
    Ideal.span {y | ∃ k : Fin d, k.val < j.val ∧ y = (uΛ k * t k) ^ e} := by
  congr 1
  ext y
  constructor <;> rintro ⟨k, hk, hy⟩
  · have hki : k ≠ i := by intro h; subst k; omega
    exact ⟨k, hk, by simpa only [Function.update_of_ne hki] using hy⟩
  · have hki : k ≠ i := by intro h; subst k; omega
    exact ⟨k, hk, by simpa only [Function.update_of_ne hki] using hy⟩

/-- Rescale fixed polynomial parameters in `Λ` while retaining an Artinian coefficient
solution. -/
theorem exists_popescu_coefficient_induction
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (_hreg : IsGeometricallyRegular k Λ)
    (N : ℕ) (hN : 0 < N)
    (hpower : IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ N ≤
      (Ideal.map α.toRingHom (singularIdeal k A)).map
        (algebraMap Λ (Localization.AtPrime q.asIdeal)))
    (d : ℕ)
    (s : ℕ) (a : Fin s → A) (ha : Ideal.span (Set.range a) = singularIdeal k A)
    (c : ℕ) (hc : 0 < c)
    (r : ℕ) (f : MvPolynomial (Fin r) k →ₐ[k] A) (hf : Function.Surjective f)
    (m₀ : ℕ) (φ₀ : MvPolynomial (Fin m₀) k →ₐ[k] Λ)
    (ψ₀ : Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) →+*
      Localization.AtPrime q.asIdeal)
    (hψ₀ : ψ₀.comp (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom))) =
      (algebraMap Λ (Localization.AtPrime q.asIdeal)).comp φ₀.toRingHom)
    (_hideal₀ : q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal)) =
      (q.asIdeal.comap φ₀.toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q.asIdeal)).comp φ₀.toRingHom))
    (_hflat₀ : ψ₀.Flat)
    (D₀ : Type (max u w)) [CommRing D₀] [IsLocalRing D₀] [IsArtinianRing D₀]
    [Algebra (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
      ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^ (N + d * (8 * c))) D₀]
    (g₀ : D₀ →+* Localization.AtPrime q.asIdeal ⧸
      (q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
        (N + d * (8 * c)))
    [IsLocalHom (algebraMap (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
      ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
          (N + d * (8 * c))) D₀)]
    [IsLocalHom g₀]
    (hsmooth₀ : EssentiallySmooth
      (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
        ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            (N + d * (8 * c))) D₀)
    (hgflat₀ : g₀.Flat)
    (hfactor₀ : (g₀.comp (algebraMap
      (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
        ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            (N + d * (8 * c))) D₀)).comp
      (Ideal.Quotient.mk (((q.asIdeal.comap φ₀.toRingHom).map
        (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            (N + d * (8 * c)))) =
      (Ideal.Quotient.mk ((q.asIdeal.map
        (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
          (N + d * (8 * c)))).comp ψ₀)
    (hinc₀ : ∀ i : Fin r, Ideal.Quotient.mk
      ((q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
        (N + d * (8 * c)))
      (algebraMap Λ (Localization.AtPrime q.asIdeal) (α (f (MvPolynomial.X i)))) ∈
        Set.range g₀)
    (uP : Fin d → MvPolynomial (Fin m₀) k)
    (huP : ∀ i, uP i ∈ q.asIdeal.comap φ₀.toRingHom)
    (_hspan : Ideal.span (Set.range (fun i ↦
      algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)) (uP i))) =
      (q.asIdeal.comap φ₀.toRingHom).map
        (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom))))
    (hsequence : RingTheory.Sequence.IsRegular (Localization.AtPrime q.asIdeal)
      (List.ofFn (fun i ↦ algebraMap Λ (Localization.AtPrime q.asIdeal) (φ₀ (uP i))))) :
    let P := MvPolynomial (Fin m₀) k
    let p₀ := q.asIdeal.comap φ₀.toRingHom
    let B := P ⧸ p₀ ^ (N + d * (8 * c))
    let L := Localization.AtPrime q.asIdeal
    let K := IsLocalRing.maximalIdeal L ^ (N + d * (8 * c))
    ∃ (tΛ : Fin d → Λ) (ell : Fin d × Fin s → Λ),
      (∀ i, tΛ i ∉ q.asIdeal) ∧
      (∀ i, (φ₀ (uP i) * tΛ i) ^ (2 * N) =
        ∑ j : Fin s, ell (i, j) * α (a j)) ∧
      (∀ (i : Fin d)
        (x : Λ ⧸ Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧
          y = (φ₀ (uP j) * tΛ j) ^ (c * 8)}),
        (φ₀ (uP i) * tΛ i) • x = 0 ↔ (φ₀ (uP i) * tΛ i) ^ 2 • x = 0) ∧
      ∃ (D : Type (max u v)) (_ : CommRing D) (_ : IsLocalRing D)
        (_ : IsArtinianRing D) (_ : Algebra k D) (_ : Algebra B D)
        (_ : IsScalarTower k B D),
        EssentiallySmooth B D ∧
        ∃ (f₀ : A →ₐ[k] D) (g : D →+* L ⧸ K)
          (δ : Fin d → Dˣ) (coeff : Fin d × Fin s → D),
          IsLocalRing (L ⧸ K) ∧ IsLocalHom g ∧ g.Flat ∧
          (∀ z : P, g (algebraMap B D (Ideal.Quotient.mk (p₀ ^ (N + d * (8 * c))) z)) =
            Ideal.Quotient.mk K (algebraMap Λ L (φ₀ z))) ∧
          (∀ i, g (δ i : D) = Ideal.Quotient.mk K (algebraMap Λ L (tΛ i))) ∧
          (∀ x, g (f₀ x) = Ideal.Quotient.mk K (algebraMap Λ L (α x))) ∧
          (∀ ij, g (coeff ij) = Ideal.Quotient.mk K (algebraMap Λ L (ell ij))) := by
  classical
  let P := MvPolynomial (Fin m₀) k
  let p₀ := q.asIdeal.comap φ₀.toRingHom
  let n := N + d * (8 * c)
  let B := P ⧸ p₀ ^ n
  let L := Localization.AtPrime q.asIdeal
  let K := IsLocalRing.maximalIdeal L ^ n
  let uΛ : Fin d → Λ := fun i ↦ φ₀ (uP i)
  let res : Λ →+* L ⧸ K := (Ideal.Quotient.mk K).comp (algebraMap Λ L)
  have hn : 0 < n := by dsimp [n]; omega
  have hnN : N ≤ n := by dsimp [n]; omega
  have hu : ∀ i, uΛ i ∈ q.asIdeal := huP
  have hz : Ideal.span (Set.range (fun j ↦ α (a j))) =
      Ideal.map α.toRingHom (singularIdeal k A) := by
    rw [← ha, Ideal.map_span, ← Set.range_comp]
    rfl
  have hpower' : IsLocalRing.maximalIdeal L ^ N ≤
      (Ideal.span (Set.range (fun j ↦ α (a j)))).map (algebraMap Λ L) := by
    rw [hz]
    exact hpower
  let T (j : ℕ) : Prop :=
    ∃ (D : Type (max u v w)) (_ : CommRing D) (_ : IsLocalRing D)
      (_ : IsArtinianRing D) (_ : Algebra k D) (_ : Algebra B D)
      (_ : IsScalarTower k B D),
      EssentiallySmooth B D ∧
      ∃ (fA : A →ₐ[k] D) (g : D →+* L ⧸ K),
        IsLocalRing (L ⧸ K) ∧ IsLocalHom g ∧ g.Flat ∧
        (∀ z : P, g (algebraMap B D (Ideal.Quotient.mk (p₀ ^ n) z)) =
          res (φ₀ z)) ∧
        (∀ x, g (fA x) = res (α x)) ∧
        ∃ (t : Fin d → Λ) (ell : Fin d × Fin s → Λ),
          ∀ i, i.val < j →
            t i ∉ q.asIdeal ∧
            (uΛ i * t i) ^ (2 * N) = ∑ k : Fin s, ell (i, k) * α (a k) ∧
            (∀ x : Λ ⧸ Ideal.span {y | ∃ k : Fin d, k.val < i.val ∧
              y = (uΛ k * t k) ^ (c * 8)},
              (uΛ i * t i) • x = 0 ↔ (uΛ i * t i) ^ 2 • x = 0) ∧
            res (t i) ∈ Set.range g ∧
            (∀ k, res (ell (i, k)) ∈ Set.range g)
  have hT : ∀ j, j ≤ d → T j := by
    intro j
    induction j with
    | zero =>
      intro _
      obtain ⟨D, hD, hlocal, hart, hkD, hBD, htower, hsmooth, fA, g,
        hS, hg, hflat, hB, hA⟩ :=
        exists_popescu_coefficient_start α q n hn r f hf m₀ φ₀ ψ₀ hψ₀
          D₀ g₀ hsmooth₀ hgflat₀ hfactor₀ hinc₀
      refine ⟨D, hD, hlocal, hart, hkD, hBD, htower, hsmooth, fA, g,
        hS, hg, hflat, hB, hA, fun _ ↦ 1, fun _ ↦ 0, ?_⟩
      intro i hi
      omega
    | succ j ih =>
      intro hj
      obtain ⟨D, hD, hlocal, hart, hkD, hBD, htower, hsmooth, fA, g,
        hS, hg, hflat, hB, hA, t, ell, hprev⟩ := ih (by omega)
      let : CommRing D := hD
      let : Algebra k D := hkD
      let : Algebra B D := hBD
      have : IsLocalRing D := hlocal
      have : IsArtinianRing D := hart
      have : IsScalarTower k B D := htower
      have : IsLocalRing (L ⧸ K) := hS
      have : IsLocalHom g := hg
      have hgk (x : k) : g (algebraMap k D x) = algebraMap k (L ⧸ K) x := by
        rw [IsScalarTower.algebraMap_apply k B D]
        change g (algebraMap B D (Ideal.Quotient.mk (p₀ ^ n) (MvPolynomial.C x))) = _
        rw [hB]
        change Ideal.Quotient.mk K (algebraMap Λ L (φ₀ (algebraMap k P x))) = _
        rw [φ₀.commutes]
        rfl
      have hinc (i : Fin d) : res (uΛ i) ∈ Set.range g :=
        ⟨algebraMap B D (Ideal.Quotient.mk (p₀ ^ n) (uP i)), hB (uP i)⟩
      let i : Fin d := ⟨j, by omega⟩
      obtain ⟨l, e, hl, he, hker, D', hD', hlocal', hart', hkD', h, g',
        hg', hflat', hsmooth', hcomp, hlift, helift⟩ :=
        exists_popescu_coefficient_step p hp q N n hN hnN d s c hc uΛ hu hsequence
          (fun k ↦ α (a k)) hpower' D g hflat hgk (fun k ↦ fA (a k))
          (fun k ↦ hA (a k)) hinc i t (fun k hk ↦ (hprev k hk).1)
      let : CommRing D' := hD'
      let : Algebra k D' := hkD'
      let : Algebra B D' := (h.toRingHom.comp (algebraMap B D)).toAlgebra
      have : IsLocalRing D' := hlocal'
      have : IsArtinianRing D' := hart'
      have : IsScalarTower k B D' := IsScalarTower.of_algebraMap_eq fun x ↦ by
        change algebraMap k D' x = h (algebraMap B D (algebraMap k B x))
        rw [← IsScalarTower.algebraMap_apply k B D, h.commutes]
      have hAlg : (algebraMap B D).toAlgebra = (inferInstance : Algebra B D) :=
        Algebra.algebra_ext _ _ fun _ ↦ rfl
      have hsmooth0 : letI : Algebra B D := (algebraMap B D).toAlgebra;
          EssentiallySmooth B D := by
        rw [hAlg]
        exact hsmooth
      have hsm : EssentiallySmooth B D' :=
        RingHom.essentiallySmooth_comp (algebraMap B D) h.toRingHom hsmooth0 hsmooth'
      have hge (x : D) : g' (h x) = g x := congrArg (fun f ↦ f x) hcomp
      have preserve {x : L ⧸ K} (hx : x ∈ Set.range g) : x ∈ Set.range g' := by
        obtain ⟨y, rfl⟩ := hx
        exact ⟨h y, hge y⟩
      let t' := Function.update t i l
      let ell' : Fin d × Fin s → Λ := fun ij ↦ if ij.1 = i then e ij.2 else ell ij
      refine ⟨D', hD', hlocal', hart', hkD', inferInstance, inferInstance, hsm,
        h.comp fA, g', hS, hg', hflat', ?_, ?_, t', ell', ?_⟩
      · intro z
        exact (hge _).trans (hB z)
      · intro x
        exact (hge _).trans (hA x)
      · intro k hk
        have hkji : k.val ≤ i.val := by dsimp [i]; omega
        have hI := prefix_span_update uΛ t i l (c * 8) k hkji
        by_cases hki : k = i
        · subst k
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · simpa [t'] using hl
          · simpa [t', ell'] using he
          · change ∀ x : Λ ⧸ Ideal.span {y | ∃ k : Fin d, k.val < i.val ∧
                y = (uΛ k * Function.update t i l k) ^ (c * 8)}, _
            rw [hI]
            simpa only [t', Function.update_self] using hker
          · simpa [t', res] using hlift
          · simpa [ell', res] using helift
        · have hkj : k.val < j := by
            have : k.val ≠ i.val := fun heq ↦ hki (Fin.ext heq)
            dsimp [i] at hkji this
            omega
          obtain ⟨hkt, hke, hkk, hklift, hkell⟩ := hprev k hkj
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · simpa [t', Function.update_of_ne hki] using hkt
          · simpa [t', ell', hki, Function.update_of_ne hki] using hke
          · change ∀ x : Λ ⧸ Ideal.span {y | ∃ j : Fin d, j.val < k.val ∧
                y = (uΛ j * Function.update t i l j) ^ (c * 8)}, _
            rw [hI]
            simpa only [t', Function.update_of_ne hki] using hkk
          · simpa [t', Function.update_of_ne hki] using preserve hklift
          · intro a
            simpa [ell', hki] using preserve (hkell a)
  obtain ⟨D, hD, hlocal, hart, hkD, hBD, htower, hsmooth, fA, g,
    hS, hg, hflat, hB, hA, t, ell, hprev⟩ := hT d le_rfl
  let : CommRing D := hD
  let : Algebra k D := hkD
  let : Algebra B D := hBD
  have : IsLocalRing D := hlocal
  have : IsArtinianRing D := hart
  have : IsScalarTower k B D := htower
  have : IsLocalRing (L ⧸ K) := hS
  have : IsLocalHom g := hg
  obtain ⟨D', hD', hBD', hlocal', hart', hsmooth', ⟨e⟩⟩ :=
    exists_essentiallySmooth_small_local_model.{u, max u v w, v} D hsmooth
  let : CommRing D' := hD'
  let : Algebra B D' := hBD'
  let : Algebra k D' := ((algebraMap B D').comp (algebraMap k B)).toAlgebra
  have : IsLocalRing D' := hlocal'
  have : IsArtinianRing D' := hart'
  have : IsScalarTower k B D' := IsScalarTower.of_algebraMap_eq' rfl
  let ek := e.restrictScalars k
  let g' := g.comp e.symm.toRingHom
  have hg' : IsLocalHom g' := by dsimp [g']; infer_instance
  have hflat' : g'.Flat := (RingHom.Flat.of_bijective e.symm.bijective).comp hflat
  have preserve {x : L ⧸ K} (hx : x ∈ Set.range g) : x ∈ Set.range g' := by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨e y, by simp [g']⟩
  have htunit (i : Fin d) : IsUnit (res (t i)) := by
    apply (Ideal.Quotient.mk K).isUnit_map
    exact IsLocalization.map_units (M := q.asIdeal.primeCompl) L
      ⟨t i, (hprev i i.isLt).1⟩
  choose delta hdelta using fun i ↦ preserve (hprev i i.isLt).2.2.2.1
  choose coeff hcoeff using fun (ij : Fin d × Fin s) ↦
    preserve ((hprev ij.1 ij.1.isLt).2.2.2.2 ij.2)
  have hdeltaunit (i : Fin d) : IsUnit (delta i) :=
    isUnit_of_map_unit g' (delta i) (by rw [hdelta i]; exact htunit i)
  let δ : Fin d → D'ˣ := fun i ↦ (hdeltaunit i).unit
  refine ⟨t, ell, fun i ↦ (hprev i i.isLt).1,
    fun i ↦ (hprev i i.isLt).2.1, fun i ↦ (hprev i i.isLt).2.2.1,
    D', hD', hlocal', hart', inferInstance, hBD', inferInstance, hsmooth',
    ek.toAlgHom.comp fA, g', δ, coeff, hS, hg', hflat', ?_, ?_, ?_, hcoeff⟩
  · intro z
    change g (e.symm (algebraMap B D' (Ideal.Quotient.mk (p₀ ^ n) z))) = res (φ₀ z)
    rw [e.symm.commutes]
    exact hB z
  · intro i
    change g' ((hdeltaunit i).unit : D') = res (t i)
    rw [IsUnit.unit_spec]
    exact hdelta i
  · intro x
    change g (e.symm (e (fA x))) = res (α x)
    rw [e.symm_apply_apply]
    exact hA x

end Algebra
