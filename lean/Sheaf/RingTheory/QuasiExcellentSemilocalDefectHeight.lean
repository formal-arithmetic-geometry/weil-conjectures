/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.RingTheory.AdicRingCompletionMap
public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.Algebra.Algebra.Rat

/-! # Semilocal completion and formal singular boundary heights

Source: Kurano--Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber),
Theorem 5.1, Step 3, Claim 5.4, equations (5.8)--(5.11), pp.12--13
(blueprint: lem-per-qe-semilocal-defect-height).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace QuasiExcellentSemilocal

/-- The local principal completion appearing in Kurano--Shimomoto, Theorem 5.1, Step 3
(blueprint: lem-per-qe-semilocal-defect-height). -/
abbrev localCompletion (B : Type u) [CommRing B] (x : B) (n : MaximalSpectrum B) :=
  AdicCompletion (Ideal.span {algebraMap B (Localization.AtPrime n.asIdeal) x})
    (Localization.AtPrime n.asIdeal)

/-- Membership in the generic minimal singular family, Kurano--Shimomoto, (5.2), (5.7):
nonregularity, minimality among singular primes, and zero contraction to the integral closure
(blueprint: lem-per-qe-semilocal-defect-height). -/
def IsGenericMinimalSingular (B : Type u) [CommRing B] (x : B) (n : MaximalSpectrum B)
    (s : PrimeSpectrum (localCompletion B x n)) : Prop :=
  ¬ IsRegularLocalRing (Localization.AtPrime s.asIdeal) ∧
    (∀ t : PrimeSpectrum (localCompletion B x n), t.asIdeal < s.asIdeal →
      IsRegularLocalRing (Localization.AtPrime t.asIdeal)) ∧
    s.asIdeal.comap (algebraMap B (localCompletion B x n)) = ⊥

/-- The complement of the finite union of maximal ideals, as a submonoid.
Source: Kurano--Shimomoto, Theorem 5.3, notation preceding Claim 5.4
(blueprint: lem-per-qe-semilocal-defect-height). -/
def semilocalComplement (B : Type u) [CommRing B] (γ : Finset (MaximalSpectrum B)) :
    Submonoid B :=
  ⨅ a : {a : MaximalSpectrum B // a ∈ γ}, a.val.asIdeal.primeCompl

/-- The specified semilocalization, Kurano--Shimomoto, Theorem 5.3
(blueprint: lem-per-qe-semilocal-defect-height). -/
abbrev semilocalization (B : Type u) [CommRing B] (γ : Finset (MaximalSpectrum B)) :=
  Localization (semilocalComplement B γ)

/-- Its principal completion, Kurano--Shimomoto, Theorem 5.3
(blueprint: lem-per-qe-semilocal-defect-height). -/
abbrev semilocalCompletion (B : Type u) [CommRing B] (x : B)
    (γ : Finset (MaximalSpectrum B)) :=
  AdicCompletion (Ideal.span {algebraMap B (semilocalization B γ) x})
    (semilocalization B γ)

/-- The canonical semilocalization-to-localization map.
Source: Kurano--Shimomoto, Theorem 5.3
(blueprint: lem-per-qe-semilocal-defect-height). -/
noncomputable def localizationMap (B : Type u) [CommRing B]
    (γ : Finset (MaximalSpectrum B)) (n : MaximalSpectrum B) (hn : n ∈ γ) :
    semilocalization B γ →+* Localization.AtPrime n.asIdeal :=
  IsLocalization.map (M := semilocalComplement B γ) (T := n.asIdeal.primeCompl)
    (Localization.AtPrime n.asIdeal) (RingHom.id B)
    (fun _ hy ↦ (Submonoid.mem_iInf.mp hy) ⟨n, hn⟩)

/-- The canonical comparison of principal completions, formed by the residuewise map,
with the equality of the two images of the parameter transported explicitly.
Source: Kurano--Shimomoto, Theorem 5.3 and (5.8)
(blueprint: lem-per-qe-semilocal-defect-height). -/
noncomputable def completionMap (B : Type u) [CommRing B] (x : B)
    (γ : Finset (MaximalSpectrum B)) (n : MaximalSpectrum B) (hn : n ∈ γ) :
    semilocalCompletion B x γ →+* localCompletion B x n :=
  (RingEquiv.cast
    (R := fun y : Localization.AtPrime n.asIdeal ↦
      AdicCompletion (Ideal.span {y}) (Localization.AtPrime n.asIdeal))
    (by simp [localizationMap, IsLocalization.map_eq])).toRingHom.comp
    (AdicCompletion.principalRingMap (localizationMap B γ n hn)
      (algebraMap B (semilocalization B γ) x))

/-- The inverse image of the chosen formal singular prime.
Source: Kurano--Shimomoto, notation before Claim 5.4
(blueprint: lem-per-qe-semilocal-defect-height). -/
noncomputable def contractedPrime (B : Type u) [CommRing B] (x : B)
    (γ : Finset (MaximalSpectrum B)) (n : MaximalSpectrum B) (hn : n ∈ γ)
    (s : PrimeSpectrum (localCompletion B x n)) : PrimeSpectrum (semilocalCompletion B x γ) :=
  PrimeSpectrum.comap (completionMap B x γ n hn) s

/-- Normalization of the completed prime quotient in its fraction ring.
Source: Kurano--Shimomoto, definition of Delta before Claim 5.4
(blueprint: lem-per-qe-semilocal-defect-height). -/
abbrev boundaryNormalization (D : Type u) [CommRing D] (s : PrimeSpectrum D) :=
  integralClosure (D ⧸ s.asIdeal) (FractionRing (D ⧸ s.asIdeal))

/-- The canonical composite from the original ring to the normalization.
Source: Kurano--Shimomoto, definition of Delta before Claim 5.4
(blueprint: lem-per-qe-semilocal-defect-height). -/
noncomputable def boundaryMap {B D : Type u} [CommRing B] [CommRing D]
    (f : B →+* D) (s : PrimeSpectrum D) : B →+* boundaryNormalization D s :=
  (algebraMap (D ⧸ s.asIdeal) (boundaryNormalization D s)).comp
    ((Ideal.Quotient.mk s.asIdeal).comp f)

/-- The contracted normalized boundary set Delta.
Source: Kurano--Shimomoto, definition before Claim 5.4
(blueprint: lem-per-qe-semilocal-defect-height). -/
def boundary {B D : Type u} [CommRing B] [CommRing D]
    (f : B →+* D) (x : B) (s : PrimeSpectrum D) : Set (Ideal B) :=
  {q | ∃ Q : Ideal (boundaryNormalization D s),
    Q ∈ (Ideal.span {boundaryMap f s x}).minimalPrimes ∧
      Q.comap (boundaryMap f s) = q}

/-- The finite-extension integral-closure assumptions in Kurano--Shimomoto, Theorem 5.1,
Step 3, with the normal maximal-ideal completions used in Claim 5.4(2)
(blueprint: lem-per-qe-semilocal-defect-height). -/
def ExtensionConditions (B : Type u) [CommRing B] (x : B) : Prop :=
  (∀ (p : Ideal B) [p.IsPrime],
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ∧
  IsNagataRing B ∧ IsUniversallyCatenary B ∧ IsAdicComplete (Ideal.span {x}) B ∧
  IsQuasiExcellent (B ⧸ Ideal.span {x}) ∧
  ∀ n : MaximalSpectrum B,
    IsDomain (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal))
      (Localization.AtPrime n.asIdeal)) ∧
    IsIntegrallyClosed
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal))
        (Localization.AtPrime n.asIdeal)) ∧
    IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal))
      (Localization.AtPrime n.asIdeal))

/-- The conclusions of Claim 5.4 and its preceding completion comparisons.
The reduction equivalence is required to carry every residue of an element to its canonical
image, so an unrelated isomorphism does not suffice.
Source: Kurano--Shimomoto, Theorem 5.1, Step 3, Claim 5.4, (5.8)--(5.11)
(blueprint: lem-per-qe-semilocal-defect-height). -/
def Comparison (B : Type u) [CommRing B] (x : B) (h : ℕ)
    (γ : Finset (MaximalSpectrum B)) (n : MaximalSpectrum B) (hn : n ∈ γ)
    (s : PrimeSpectrum (localCompletion B x n)) : Prop :=
  IsNoetherianRing (semilocalCompletion B x γ) ∧
  (∀ (p : Ideal (semilocalCompletion B x γ)) [p.IsPrime],
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ∧
  IsNagataRing (semilocalCompletion B x γ) ∧
  IsUniversallyCatenary (semilocalCompletion B x γ) ∧
  IsGRing (semilocalCompletion B x γ) ∧
  (algebraMap B (semilocalCompletion B x γ)).Flat ∧
  (∃ e : (semilocalization B γ ⧸
      Ideal.span {algebraMap B (semilocalization B γ) x}) ≃+*
      (semilocalCompletion B x γ ⧸ Ideal.span {algebraMap B (semilocalCompletion B x γ) x}),
    ∀ b : semilocalization B γ,
      e (Ideal.Quotient.mk _ b) =
        Ideal.Quotient.mk _ (algebraMap (semilocalization B γ) (semilocalCompletion B x γ) b)) ∧
  (contractedPrime B x γ n hn s).asIdeal.comap
    (algebraMap B (semilocalCompletion B x γ)) = ⊥ ∧
  (contractedPrime B x γ n hn s).asIdeal.height = h ∧
  ¬ IsRegularLocalRing (Localization.AtPrime (contractedPrime B x γ n hn s).asIdeal) ∧
  boundary (algebraMap B (semilocalCompletion B x γ)) x (contractedPrime B x γ n hn s) =
    {q | ∃ Q : Ideal (semilocalCompletion B x γ),
      Q ∈ ((contractedPrime B x γ n hn s).asIdeal ⊔
        Ideal.span {algebraMap B (semilocalCompletion B x γ) x}).minimalPrimes ∧
      Q.comap (algebraMap B (semilocalCompletion B x γ)) = q} ∧
  ∀ q ∈ boundary (algebraMap B (semilocalCompletion B x γ)) x
    (contractedPrime B x γ n hn s), q.height = (h : ℕ∞) + 1

/-- Semilocal comparisons for a height-minimizing generic formal singular prime in
characteristic zero. Source: Kurano--Shimomoto, Theorem 5.1, Step 3, Claim 5.4,
(5.8)--(5.11), printed pp.12--13 (blueprint: lem-per-qe-semilocal-defect-height).

Proof: Apply lem-per-gabber-semilocal-defect-height to the underlying commutative ring R,
forgetting only its rational algebra structure. Keep x, all finite fraction-field extensions,
their integral closures, all local principal completions, and the chosen height-minimizing
triple unchanged. Consequently the family of generic minimal singular primes and its minimum
are unchanged. The semilocal complement, localization, completion, canonical comparison,
contracted prime, normalization and boundary set are likewise identical. The cited theorem
gives the five ring properties, flatness and the canonical reduction equivalence, the zero
contraction, height and nonregularity of the contracted prime, both boundary descriptions,
and height h+1 for every boundary prime, which are precisely Comparison. -/
theorem semilocal_defect_height
    (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] [IsDomain R]
    [IsIntegrallyClosed R] (hNagata : IsNagataRing R) (x : R) (hx : x ≠ 0)
    (hxunit : ¬ IsUnit x) [IsAdicComplete (Ideal.span {x}) R]
    (hcat : IsUniversallyCatenary R) (hnotqe : ¬ IsQuasiExcellent R)
    (hquot : ∀ K : Ideal R, K ≠ ⊥ → IsQuasiExcellent (R ⧸ K))
    (hext : ∀ (F : Type u) [Field F] [Algebra (FractionRing R) F]
      [Algebra R F] [IsScalarTower R (FractionRing R) F] [Module.Finite (FractionRing R) F],
      Module.Finite R (integralClosure R F) ∧
        ExtensionConditions (integralClosure R F) (algebraMap R (integralClosure R F) x))
    (h : ℕ) (hge : 2 ≤ h)
    (hmin : ∀ (F : Type u) [Field F] [Algebra (FractionRing R) F]
      [Algebra R F] [IsScalarTower R (FractionRing R) F] [Module.Finite (FractionRing R) F]
      (m : MaximalSpectrum (integralClosure R F))
      (t : PrimeSpectrum (localCompletion (integralClosure R F)
        (algebraMap R (integralClosure R F) x) m)),
      IsGenericMinimalSingular (integralClosure R F)
        (algebraMap R (integralClosure R F) x) m t → (h : ℕ∞) ≤ t.asIdeal.height)
    (L : Type u) [Field L] [Algebra (FractionRing R) L] [Algebra R L]
    [IsScalarTower R (FractionRing R) L] [Module.Finite (FractionRing R) L]
    (n : MaximalSpectrum (integralClosure R L))
    (s : PrimeSpectrum (localCompletion (integralClosure R L)
      (algebraMap R (integralClosure R L) x) n))
    (hs : IsGenericMinimalSingular (integralClosure R L)
      (algebraMap R (integralClosure R L) x) n s)
    (hheight : s.asIdeal.height = h)
    (γ : Finset (MaximalSpectrum (integralClosure R L))) (hn : n ∈ γ) :
    Comparison (integralClosure R L) (algebraMap R (integralClosure R L) x) h γ n hn s := by
  sorry

end QuasiExcellentSemilocal
