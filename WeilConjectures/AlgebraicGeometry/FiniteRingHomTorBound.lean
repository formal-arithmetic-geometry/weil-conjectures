/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom
import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.SixFunctors.Etale.Derived.Stability.HomDevissage
import WeilConjectures.AlgebraicGeometry.FiniteRingGeometricDualityFiniteField
import WeilConjectures.AlgebraicGeometry.FiniteRingSitePerfectDualWindow

/-!
# Numerical internal-Hom Tor estimate for general finite coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-kunneth-formulas-and-external-duality/sk-lem-sf-kunneth-star/
`sk-rem-sf-typing.md`, RHom row, quantitative finite-A sub-step
(blueprint: lem-sf-finite-ring-hom-tor-bound); proof route:
literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors/
sec-the-remaining-operations/sk-thm-sf-ctf-stability/`det-thm-sf-hom-ctf.proof.md`.

For a finite or algebraically closed field `k` of characteristic `p ≠ ℓ`, a finite
`ℓ`-primary coefficient ring `A`, and a separated finite-type `k`-scheme `T` of dimension
`≤ m`, the derived internal Hom of two bounded constructible complexes with Tor amplitude in
`[a, b]` and `[c, d]` has Tor amplitude in `[c - b - 2m, d - a + 2m]`, and in `[c - b, d - a]`
when the first argument is site-perfect.

## Main statements

- `AlgebraicGeometry.Etale.finiteRingHomTorBound`.

## Implementation notes

The objects are those of the ordinary small étale site: `DerivedCategoryModule A T`, the
predicates `DerivedCategory.isBoundedConstructible` and `DerivedCategory.hasTorAmplitudeIn`,
the derived internal Hom `RHom(T)[ModuleCat A]` (`AlgebraicGeometry.Etale.derivedHom`) and
`DerivedCategory.IsSitePerfect` (étale-local bounded complexes of finite projective modules).
The existing `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom` covers only an algebraically
closed base and a dualizable first argument, so it is not this statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

/-- Numerical Tor-amplitude bound for internal Hom over finite coefficients.

Source: blueprint `sk-rem-sf-typing.md` (part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-lem-sf-kunneth-star), RHom row, quantitative
finite-A sub-step (blueprint: lem-sf-finite-ring-hom-tor-bound); the proof follows
`det-thm-sf-hom-ctf.proof.md` (part-six-operations/sec-six-functors/
sec-the-remaining-operations/sk-thm-sf-ctf-stability).

Proof (node steps):
1. Let `a : T ⟶ Spec k`, `ω_T = a^! A` and `D_T M = RHom(M, ω_T)`; `k` is perfect. The
   finite-coefficient Verdier bound (`lem-route-finite-verdier-tor-bound`) gives `D_T M`
   bounded constructible with Tor amplitude in `[-d - 2m, -c]`; biduality
   (`lem-sf-finite-ring-geometric-duality-finite-field` for finite `k`,
   `lem-sf-finite-ring-geometric-duality` for algebraically closed `k`) gives `D_T D_T M ≅ M`.
2. By the tensor interval lemma (`lem-sf-source-tensor-cohomology-interval`),
   `K ⊗ᴸ D_T M` has Tor amplitude in `[a - d - 2m, b - c]`; it is bounded constructible by
   `lem-asd-source-finite-etale-tensor-ctf`.
3. Closed tensor–Hom adjunction (`lem-sf-ringed-derived-closed-symmetric-monoidal`) and
   step 1 give `RHom(K, M) ≅ D_T (K ⊗ᴸ D_T M)`.
4. The Verdier bound applied to `K ⊗ᴸ D_T M` gives Tor amplitude
   `[c - b - 2m, d - a + 2m]` for its dual, which is `RHom(K, M)` by step 3.
5. If `K` is site-perfect, the finite-projective dual window
   (`lem-sf-finite-ring-site-perfect-dual-window`) gives `K^∨` in `[-b, -a]` and
   `K^∨ ⊗ᴸ M ≅ RHom(K, M)`, hence the interval `[c - b, d - a]`.
The zero ring and the empty scheme are included. -/
theorem finiteRingHomTorBound
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    {k : Type u} [Field k] [CharP k p]
    (hk : Finite k ∨ IsAlgClosed k) (hpell : p ≠ ell)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (r : ℕ) (hr : 1 ≤ r) (hkill : ∀ x : A, (ell ^ r) • x = 0)
    {T : Scheme.{u}} (aT : T ⟶ Spec (.of k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (m : ℕ) (hm : topologicalKrullDim T ≤ (m : WithBot ℕ∞))
    {a b c d : ℤ} (hab : a ≤ b) (hcd : c ≤ d)
    {K M : DerivedCategoryModule A T}
    (hK : DerivedCategory.isBoundedConstructible A T K)
    (hKt : DerivedCategory.hasTorAmplitudeIn A T a b K)
    (hM : DerivedCategory.isBoundedConstructible A T M)
    (hMt : DerivedCategory.hasTorAmplitudeIn A T c d M) :
    DerivedCategory.hasTorAmplitudeIn A T
        (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
      (((RHom(T)[ModuleCat.{u + 1} A]).obj (op K)).obj M) ∧
    (DerivedCategory.IsSitePerfect K →
      DerivedCategory.hasTorAmplitudeIn A T (c - b) (d - a)
        (((RHom(T)[ModuleCat.{u + 1} A]).obj (op K)).obj M)) := by
  letI : HasInvertibleExponent A (Spec (.of k)) := by
    refine ⟨ell ^ r, pow_pos (Fact.out : ell.Prime).pos r, ?_, ?_⟩
    · simpa [smul_eq_mul] using hkill (1 : A)
    · have hne : (ell : k) ≠ 0 := by
        intro hzero
        have heq : ringChar k = ell :=
          CharP.ringChar_of_prime_eq_zero (Fact.out : ell.Prime) hzero
        exact hpell ((ringChar.eq k p).symm.trans heq)
      have hu := ((isUnit_iff_ne_zero.mpr hne).pow r).map
        (Scheme.ΓSpecIso (.of k)).inv.hom
      simpa using hu
  have hbc (X : Scheme.{u}) (K : DerivedCategoryModule A X) :
      DerivedCategory.isBoundedConstructible A X K ↔
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
    constructor
    · rintro ⟨hc, x, y, _, hz⟩
      refine ⟨⟨⟨x, ?_⟩, ⟨y, ?_⟩⟩, fun i ↦
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)⟩
      · exact (_root_.DerivedCategory.isGE_iff K x).2 (fun i hi ↦ hz i (.inl hi))
      · exact (_root_.DerivedCategory.isLE_iff K y).2 (fun i hi ↦ hz i (.inr hi))
    · rintro ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hc⟩
      refine ⟨fun i ↦
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i),
        min x y, y, min_le_right _ _, fun i hi ↦ ?_⟩
      rcases hi with hi | hi
      · exact (_root_.DerivedCategory.isGE_iff K x).1 hx i
          (hi.trans_le (min_le_left _ _))
      · exact (_root_.DerivedCategory.isLE_iff K y).1 hy i hi
  letI : HasInvertibleExponent A T := .of_hom aT
  letI : PerfectField k := by
    rcases hk with hfin | hac
    · exact PerfectField.ofFinite
    · letI : IsAlgClosed k := hac
      infer_instance
  have hK' := (hbc T K).1 hK
  have hM' := (hbc T M).1 hM
  have hKt' := DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hKt
  have hMt' := DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hMt
  have hgen : DerivedCategory.hasTorAmplitudeIn A T
      (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
      (((RHom(T)[ModuleCat.{u + 1} A]).obj (op K)).obj M) := by
    let hMctf : DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} A) T M := ⟨hM', c, d, hMt'⟩
    have hDM := constructibleFiniteTor_and_torAmplitudeIn_verdierDual_of_perfectField
      A aT m hm c d hM' hMt'
    have hT := constructibleFiniteTor_tensor A T hDM.1 ⟨hK', a, b, hKt'⟩
    have hTt := torAmplitudeIn_tensor (ModuleCat.{u + 1} A) T _ _ _ _ hDM.2 hKt'
    have hDT := torAmplitudeIn_verdierDual A aT m hm _ _ hT.1 hTt
    have hbid : Nonempty (M ≅ (verdierDual A aT).obj (op
        ((verdierDual A aT).obj (op M)))) := by
      by_cases hka : IsAlgClosed k
      · letI : IsAlgClosed k := hka
        letI : IsIso ((verdierDualDoubleDual A aT).app M) :=
          isIso_verdierDualDoubleDual_app A aT hMctf
        exact ⟨asIso ((verdierDualDoubleDual A aT).app M)⟩
      · letI : Finite k := hk.resolve_right hka
        letI : HasCompactification aT := (NagataCompactification aT).hasCompactification
        letI : IsIso ((verdierDualDoubleDual A aT).app M) := by
          exact isIso_verdierDualDoubleDual_app_finiteField p ell hpell k A
            ⟨r, hr, fun x ↦ hkill x⟩ aT hMctf
        exact ⟨asIso ((verdierDualDoubleDual A aT).app M)⟩
    obtain ⟨e⟩ := nonempty_iso_derivedHom_verdierDual A aT K M hbid.some
    exact DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      ((torAmplitudeIn _ T _ _).prop_of_iso e.symm (hDT.mono (by omega) (by omega)))
  refine ⟨hgen, ?_⟩
  intro hperf
  exact finiteRingSitePerfectDualWindow A ell r hr hkill hperf hKt
    hM'.1 hMt |>.2.2

end AlgebraicGeometry.Etale
