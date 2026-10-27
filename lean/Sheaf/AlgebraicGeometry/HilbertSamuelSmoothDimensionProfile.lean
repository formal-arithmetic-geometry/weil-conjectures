/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.AlgebraicGeometry.HilbertSamuelReachableLevels
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Order.PiLex
public import Mathlib.Data.Prod.Lex
public import Mathlib.Topology.KrullDimension

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Smooth invariant Hilbert--Samuel dimension heads

Source: ILO VIII 2.3.13, p. 94; Bierstone--Milman--Temkin, arXiv:0905.3580,
section 6.3 and Remark 6.2 (blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile).

The normalized head uses integer finite differences. The modified head uses a common
ambient dimension bound. Marked ideals and every geometric test operation are the existing
Hilbert--Samuel presentation interface; only the numerical retaining-level condition changes.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.HilbertSamuel

/-- Inclusive summation on integer sequences, allowing negative entries.
Source: ILO VIII 2.3.13, explicit finite-difference normalization in node proof step 1
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile). -/
def integerSummation (f : ℕ → ℤ) (n : ℕ) : ℤ := ∑ i ∈ Finset.range (n + 1), f i

/-- Finite difference, retaining entry zero instead of discarding an initial term.
Source: ILO VIII 2.3.13, explicit normalization in node proof step 1
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile). -/
def difference (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => f 0
  | n + 1 => f (n + 1) - f n

/-- The set of distinct local component dimensions, using the actual minimal-prime quotients.
Source: BMT 6.3, component-dimension correction, localized as in node proof steps 3 and 6
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile). -/
noncomputable def localComponentDimensions (X : Scheme.{u}) (x : X) : Set (WithBot ℕ∞) :=
  {d | ∃ P : Ideal (X.presheaf.stalk x), P ∈ minimalPrimes (X.presheaf.stalk x) ∧
    ringKrullDim ((X.presheaf.stalk x) ⧸ P) = d}

/-- Minimum local component dimension. In the finite-type applications the set is nonempty
and all its dimensions are finite, so neither default value is used.
Source: BMT 6.3 and node proof step 6
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile). -/
noncomputable def minimumComponentDimension (X : Scheme.{u}) (x : X) : ℕ :=
  ((sInf (localComponentDimensions X x)).unbotD 0).toNat

/-- Number of distinct component dimensions, rather than the number of components.
Source: BMT 6.3 (blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile). -/
noncomputable def componentDimensionCount (X : Scheme.{u}) (x : X) : ℕ :=
  (localComponentDimensions X x).ncard

/-- Lexicographic pairs, with lexicographic comparison also on integer sequences.
Source: BMT 6.3 and node proof step 1
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile). -/
abbrev DimensionHead := Lex (ℕ × Lex (ℕ → ℤ))

/-- The intrinsic smooth invariant head `(c_x, Δ^q_x h_x)`.
Source: ILO VIII 2.3.13; BMT 6.3 with common summation removed, node proof steps 1--6
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile). -/
noncomputable def normalizedHead (X : Scheme.{u}) (x : X) : DimensionHead :=
  toLex (componentDimensionCount X x,
    toLex ((difference^[minimumComponentDimension X x]) (fun n ↦ (localFunction X x n : ℤ))))

/-- Apply the same summation to the second entry of any head.
Source: node proof steps 1 and 6, finite-difference form of BMT 6.3
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile). -/
def sumHead (D : ℕ) (a : DimensionHead) : DimensionHead :=
  toLex ((ofLex a).1, toLex ((integerSummation^[D]) (ofLex (ofLex a).2)))

/-- Modified head for a fixed common dimension bound.
Source: BMT 6.3 and Remark 6.2, with the local-ring dimension shift of node proof step 6
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile). -/
noncomputable def modifiedHead (D : ℕ) (X : Scheme.{u}) (x : X) : DimensionHead :=
  sumHead D (normalizedHead X x)

/-- The normalized head at a regular point.
Source: node proof steps 4--5 (blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile). -/
def regularHead : DimensionHead := toLex (1, toLex (fun _ ↦ (1 : ℤ)))

/-- Retaining a modified level in the actual embedded scheme, as an ambient subset.
Source: BMT 6.3, common presentation assertion and node proof steps 11--13
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile). -/
noncomputable def modifiedLocus (D : ℕ) (a : DimensionHead)
    (S : Embedded (ULift.{u} ℚ)) : Set S.Z :=
  S.i '' {x | modifiedHead D S.X x = a}

/-- The existing marked-ideal tests with the modified numerical retaining-level locus.
The bound D stays fixed even at line tests: the normalized head is smooth invariant.
The geometric line test still sums `S.level`, exactly as the existing test interface requires.
Source: BMT 6.3, common presentation assertion and node proof step 13
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile). -/
noncomputable def ModifiedPresentsThrough (D : ℕ) (a : DimensionHead) :
    ℕ → (S : Embedded (ULift.{u} ℚ)) → Marked S → Prop
  | 0, S, M => M.cosupport = modifiedLocus D a S
  | n + 1, S, M => M.cosupport = modifiedLocus D a S ∧
      ∀ (T : Embedded (ULift.{u} ℚ)) (s : Step S T),
        s.Admissible (modifiedLocus D a S) →
          (∃ M' : Marked T, s.Transforms M M') ∧
          ∀ M' : Marked T, s.Transforms M M' → ModifiedPresentsThrough D a n T M'

/-- A modified-head presentation, with positive marking and coherent ideal already in `Marked`.
Its tests start with empty test boundary; earlier exceptional ideals remain history data.
Source: BMT 6.3, common presentation assertion and node proof step 13
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile). -/
noncomputable def ModifiedPresents (D : ℕ) (a : DimensionHead)
    {S : Embedded (ULift.{u} ℚ)} (M : Marked S) : Prop :=
  S.boundary = [] ∧ ∀ n : ℕ, ModifiedPresentsThrough D a n S M

private theorem difference_integerSummation (f : ℕ → ℤ) :
    difference (integerSummation f) = f := by
  funext n
  cases n with
  | zero => simp [difference, integerSummation]
  | succ n => simp [difference, integerSummation, Finset.sum_range_succ]

private theorem integerSummation_difference (f : ℕ → ℤ) :
    integerSummation (difference f) = f := by
  funext n
  induction n with
  | zero => simp [integerSummation, difference]
  | succ n ih =>
    change (∑ i ∈ Finset.range (n + 1 + 1), difference f i) = f (n + 1)
    rw [Finset.sum_range_succ]
    change integerSummation (difference f) n + (f (n + 1) - f n) = f (n + 1)
    rw [ih]
    omega

private theorem integerSummation_strictMono :
    StrictMono (fun f : Lex (ℕ → ℤ) ↦ toLex (integerSummation (ofLex f))) := by
  intro f g h
  obtain ⟨j, hj, hlt⟩ := h
  change (ofLex f j : ℤ) < ofLex g j at hlt
  refine ⟨j, ?_, ?_⟩
  · intro k hk
    change (∑ i ∈ Finset.range (k + 1), f i) = ∑ i ∈ Finset.range (k + 1), g i
    apply Finset.sum_congr rfl
    intro i hi
    exact hj i (Nat.lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hk)
  · change (∑ i ∈ Finset.range (j + 1), f i) < ∑ i ∈ Finset.range (j + 1), g i
    have heq : (∑ i ∈ Finset.range j, f i) = ∑ i ∈ Finset.range j, g i :=
      Finset.sum_congr rfl (fun i hi ↦ hj i (Finset.mem_range.mp hi))
    rw [Finset.sum_range_succ, Finset.sum_range_succ, heq]
    exact add_lt_add_of_le_of_lt le_rfl hlt

private theorem integerSummation_lt_iff (f g : ℕ → ℤ) :
    toLex (integerSummation f) < toLex (integerSummation g) ↔ toLex f < toLex g :=
  integerSummation_strictMono.lt_iff_lt

private theorem difference_lt_iff (f g : ℕ → ℤ) :
    toLex (difference f) < toLex (difference g) ↔ toLex f < toLex g := by
  simpa only [integerSummation_difference] using
    (integerSummation_lt_iff (difference f) (difference g)).symm

/-- Summation and difference are mutually inverse and preserve and reflect lexicographic order.
Source: node proof step 1, normalization of BMT 6.3
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile).

Proof: At zero both cancellations are immediate. At a successor, subtract consecutive partial
sums, or telescope the differences. If f and g first differ at j, both operators leave their
entries equal below j and leave the difference at j unchanged. Iterate this argument. -/
theorem integer_operators (f g : ℕ → ℤ) (r : ℕ) :
    difference (integerSummation f) = f ∧ integerSummation (difference f) = f ∧
    (toLex ((integerSummation^[r]) f) < toLex ((integerSummation^[r]) g) ↔
      toLex f < toLex g) ∧
    (toLex ((difference^[r]) f) < toLex ((difference^[r]) g) ↔ toLex f < toLex g) := by
  refine ⟨difference_integerSummation f, integerSummation_difference f, ?_, ?_⟩
  · induction r generalizing f g with
    | zero => rfl
    | succ r ih =>
      simp only [Function.iterate_succ_apply, ih, integerSummation_lt_iff]
  · induction r generalizing f g with
    | zero => rfl
    | succ r ih => simp only [Function.iterate_succ_apply, ih, difference_lt_iff]

/-- Finite nonempty dimension sets and finite lengths justify every natural-number extraction.
Source: node proof steps 2, 3 and 6
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile).

Proof: Finite type over Q gives Noetherian stalks and finitely many minimal primes. Their
quotients are domains essentially of finite type over Q, so their dimensions are finite by
the dimension/transcendence-degree formulas. Minimal primes exist in every nonzero local
ring. The maximal-ideal filtration has finite-dimensional residue-field factors; length
additivity proves finite length of every power quotient. The infimum is an attained minimum.
-/
theorem dimension_profile_finite {X : Scheme.{u}}
    (p : X ⟶ Spec (.of (ULift.{u} ℚ)))
    [IsReduced X] [LocallyOfFiniteType p] [QuasiCompact p] (x : X) :
    (localComponentDimensions X x).Finite ∧ (localComponentDimensions X x).Nonempty ∧
    (∀ d ∈ localComponentDimensions X x, ∃ n : ℕ, d = (n : WithBot ℕ∞)) ∧
    (minimumComponentDimension X x : WithBot ℕ∞) = sInf (localComponentDimensions X x) ∧
    ∀ n : ℕ, Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (n + 1)) < ⊤ := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let R := X.presheaf.stalk x
  have himage : localComponentDimensions X x =
      (fun P : Ideal R ↦ ringKrullDim (R ⧸ P)) '' minimalPrimes R := by
    rfl
  have hfinite : (localComponentDimensions X x).Finite := by
    rw [himage]
    exact (minimalPrimes.finite_of_isNoetherianRing R).image _
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes (R := R) bot_ne_top
  have hnonempty : (localComponentDimensions X x).Nonempty :=
    ⟨ringKrullDim (R ⧸ P), P, hP, rfl⟩
  have hnat : ∀ d ∈ localComponentDimensions X x, ∃ n : ℕ, d = (n : WithBot ℕ∞) := by
    rintro d ⟨P, hP, rfl⟩
    have : P.IsPrime := hP.isPrime
    have hbot : ringKrullDim (R ⧸ P) ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le (by simp) ringKrullDim_nonneg_of_nontrivial)
    have htop : ringKrullDim (R ⧸ P) < ⊤ :=
      (ringKrullDim_quotient_le P).trans_lt (ringKrullDim_lt_top (R := R))
    obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hbot
    have hetop : e ≠ ⊤ := by
      intro h
      rw [← he, h] at htop
      exact lt_irrefl _ htop
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hetop
    exact ⟨n, he.symm.trans (congrArg (fun e : ℕ∞ ↦ (e : WithBot ℕ∞)) hn.symm)⟩
  refine ⟨hfinite, hnonempty, hnat, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hnat _ (hnonempty.csInf_mem hfinite)
    simp only [minimumComponentDimension, hn, ← WithBot.coe_natCast,
      WithBot.unbotD_coe, ENat.toNat_natCast]
  · intro n
    let m := IsLocalRing.maximalIdeal R
    have hrad : (m ^ (n + 1)).radical = m := by
      rw [Ideal.radical_pow _ (Nat.succ_ne_zero n),
        Ideal.IsPrime.radical (inferInstance : m.IsPrime)]
    have hminimal : m ∈ (m ^ (n + 1)).minimalPrimes := by
      rw [← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton _
    have : IsArtinianRing (R ⧸ m ^ (n + 1)) :=
      IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hminimal
    have : IsArtinian R (R ⧸ m ^ (n + 1)) :=
      isArtinian_of_surjective_algebraMap (R := R ⧸ m ^ (n + 1))
        (M := R ⧸ m ^ (n + 1)) Ideal.Quotient.mk_surjective
    exact Module.length_ne_top.lt_top

/-- Smooth invariance using the local-ring dimension of the fibre, including nonclosed points.
No quasi-compactness or constant relative-dimension assumption is imposed on the smooth map.
Source: ILO VIII 2.3.13; node proof steps 2--3
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile).

Proof: Apply `lem-trf-smooth-local-tangent-cone-extension` to the smooth local stalk map.
The associated graded ring is the residue-field extension of the base graded ring with s
polynomial variables. Length additivity along the maximal-ideal filtration gives s summations
of the raw function. The same lemma translates the set of minimal-prime quotient dimensions
by s. Translation preserves cardinality and increases its minimum by s. Cancel s summations
against s differences by the preceding operator theorem. For a non-quasi-compact source,
perform the computation on finite-type neighborhoods of y. -/
theorem smooth_dimension_profile {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of (ULift.{u} ℚ))) (f : Y ⟶ X)
    [IsReduced X] [LocallyOfFiniteType p] [QuasiCompact p] [Smooth f] (y : Y) :
    IsRegularLocalRing ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) ∧
    ∃ s : ℕ,
      ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) = (s : WithBot ℕ∞) ∧
      localFunction Y y = (summation^[s]) (localFunction X (f y)) ∧
      localComponentDimensions Y y =
        (fun d : WithBot ℕ∞ ↦ d + (s : WithBot ℕ∞)) '' localComponentDimensions X (f y) ∧
      minimumComponentDimension Y y = minimumComponentDimension X (f y) + s ∧
      componentDimensionCount Y y = componentDimensionCount X (f y) ∧
      normalizedHead Y y = normalizedHead X (f y) := by
  sorry

/-- The regular head occurs exactly at regular points and is strictly below every other head.
Source: node proof steps 4--5 (blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile).

Proof: A regular local ring is a domain. Its regular parameters give polynomial associated
graded ring, hence h is the dimension-fold sum of the constant sequence one. Conversely,
c > 1 is already larger in the first coordinate. If c = 1, write d = q and let e be the
cotangent dimension. Entry zero of Δ^q h is one and entry one is 1 + e - q. The cotangent
dimension inequality has equality exactly for regular local rings, proving the assertion. -/
theorem normalizedHead_regular {X : Scheme.{u}}
    (p : X ⟶ Spec (.of (ULift.{u} ℚ)))
    [IsReduced X] [LocallyOfFiniteType p] [QuasiCompact p] (x : X) :
    (normalizedHead X x = regularHead ↔ IsRegularLocalRing (X.presheaf.stalk x)) ∧
    (¬ IsRegularLocalRing (X.presheaf.stalk x) → regularHead < normalizedHead X x) := by
  sorry

/-- Conversion to the positively summed head, with no loss of initial entries.
Source: node proof step 6 and BMT 6.3
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile).

Proof: Dimension of every local component is at most the global dimension of X. Thus q ≤ D,
and cancellation of summation with difference gives the displayed formula. Equivalently the
finite-type domain dimension formulas give q = d_min - trdeg_Q κ(x). -/
theorem modifiedHead_eq {X : Scheme.{u}}
    (p : X ⟶ Spec (.of (ULift.{u} ℚ)))
    [IsReduced X] [LocallyOfFiniteType p] [QuasiCompact p]
    (D : ℕ) (hD : topologicalKrullDim X ≤ (D : WithBot ℕ∞)) (x : X) :
    modifiedHead D X x = toLex (componentDimensionCount X x,
      toLex ((integerSummation^[D - minimumComponentDimension X x])
        (fun n ↦ (localFunction X x n : ℤ)))) := by
  obtain ⟨_, hnonempty, _, hminimum, _⟩ := dimension_profile_finite p x
  obtain ⟨d, P, hP, hd⟩ := hnonempty
  have hlocal : ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
    rw [ringKrullDim_stalk_eq_coheight]
    rw [← Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm x]
    exact Order.coheight_le_krullDim _
  have hq : minimumComponentDimension X x ≤ D := by
    have hle : (minimumComponentDimension X x : WithBot ℕ∞) ≤ (D : WithBot ℕ∞) :=
      calc
        _ = sInf (localComponentDimensions X x) := hminimum
        _ ≤ ringKrullDim ((X.presheaf.stalk x) ⧸ P) := sInf_le ⟨P, hP, rfl⟩
        _ ≤ ringKrullDim (X.presheaf.stalk x) := ringKrullDim_quotient_le P
        _ ≤ topologicalKrullDim X := hlocal
        _ ≤ (D : WithBot ℕ∞) := hD
    exact_mod_cast hle
  have hcancel :=
    Function.LeftInverse.iterate integerSummation_difference (minimumComponentDimension X x)
      (fun n ↦ (localFunction X x n : ℤ))
  unfold modifiedHead sumHead normalizedHead
  dsimp only [ofLex_toLex]
  rw [← Nat.sub_add_cancel hq, Function.iterate_add_apply, hcancel]
  simp only [Nat.add_sub_cancel]

/-- Upper semicontinuity, finite image, and the same irreducible level components as H.
Source: BMT 6.3 and Remark 6.2; node proof steps 7--10
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile).

Proof: Discarding a component through x strictly lowers the quotient lengths at some index:
Krull intersection detects a nonzero element of the omitted-component ideal, and length
additivity detects the kernel in a power quotient. Along a specialization, equality of H
therefore forces the same set of components. Locally remove components not through x and
use upper semicontinuity of H. Fewer distinct dimensions lowers the first head coordinate;
if the counts agree the profiles agree and summation preserves the comparison of H. A finite
open cover, finite image of H on each chart and finitely many component dimensions give
finite image of the head. Comparable points have equal heads exactly when they have equal H.
Each level is locally closed. Its generic points and maximality of irreducible components
therefore identify the components of the two stratifications in both directions. -/
theorem modifiedHead_properties {X : Scheme.{u}}
    (p : X ⟶ Spec (.of (ULift.{u} ℚ)))
    [IsReduced X] [LocallyOfFiniteType p] [QuasiCompact p]
    (D : ℕ) (hD : topologicalKrullDim X ≤ (D : WithBot ℕ∞)) :
    (Set.range (modifiedHead D X)).Finite ∧
    (∀ a : DimensionHead, IsClosed {x : X | a ≤ modifiedHead D X x}) ∧
    ∀ C : Set X,
      (∃ a : DimensionHead,
        ∃ K ∈ irreducibleComponents {x : X // modifiedHead D X x = a},
          Subtype.val '' K = C) ↔
      (∃ H : ℕ → ℕ,
        ∃ K ∈ irreducibleComponents {x : X // function p x = H},
          Subtype.val '' K = C) := by
  sorry

/-- Each point has a common local presentation for H and the modified head, including all
finite tests and a maximal-order ideal on the full chosen smooth envelope.
Source: BMT 6.2--6.3; node proof steps 11--13
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile).

Proof: Near x, remove the finitely many components of the H-level not containing x.
The specialization argument in the preceding theorem makes the H-level and the head level
identical there. Apply `lem-trf-hilbert-samuel-local-presentations` on a smooth local envelope.
At a singular point its full-envelope maximal-order clause applies after a further pointed
étale comparison. At a regular point shrink to a smooth germ and embed it as t = 0 in its
product with a line; the ideal (t) with marking one has order one on its cosupport. Its
controlled transform has the same retaining-level tests as the zero ideal on the germ:
in charts meeting the strict transform the normal coordinate becomes t/e, and in the
remaining charts both cosupport and strict transform are empty. Thus a regular zero ideal
does not require a finite-order claim. Under blowup, component dimensions can only disappear.
Equality of H forces equality of profiles by `lem-trf-hilbert-samuel-equality-component-rigidity`.
Thus equality of heads and equality of H persist together. Line products preserve the
normalized head and sum the H-level, including nonclosed points. Auxiliary intersection tests
use exactly the existing ordinary-pullback convention. Induction on test length gives both
presentation predicates with the same marked ideal and transforms. -/
theorem local_modified_presentations {X : Scheme.{u}}
    (p : X ⟶ Spec (.of (ULift.{u} ℚ)))
    [IsReduced X] [LocallyOfFiniteType p] [QuasiCompact p]
    (D : ℕ) (hD : topologicalKrullDim X ≤ (D : WithBot ℕ∞)) (x : X) :
    ∃ (S : Embedded (ULift.{u} ℚ)) (g : S.X ⟶ X) (a : S.X) (M : Marked S),
      Etale g ∧ g ≫ p = S.i ≫ S.p ∧ g a = x ∧
      S.level = function p x ∧ Presents M ∧ ModifiedPresents D (modifiedHead D X x) M ∧
      (∀ b : S.X, modifiedHead D S.X b ≤ modifiedHead D X x) ∧
      FullMaximalOrder M := by
  sorry

private theorem modifiedPresentsThrough_iff (D : ℕ) (a : DimensionHead) (n : ℕ)
    (S : Embedded (ULift.{u} ℚ)) (M P : Marked S) (h : EquivalentThrough n S M P) :
    ModifiedPresentsThrough D a n S M ↔ ModifiedPresentsThrough D a n S P := by
  induction n generalizing S M P with
  | zero =>
    change M.cosupport = P.cosupport at h
    change M.cosupport = modifiedLocus D a S ↔ P.cosupport = modifiedLocus D a S
    rw [h]
  | succ n ih =>
    obtain ⟨hcosupport, htests⟩ := h
    constructor
    · rintro ⟨hM, hnext⟩
      refine ⟨hcosupport.symm.trans hM, ?_⟩
      intro T s hs
      obtain ⟨hexM, hexP, heq⟩ := htests T s (by rwa [hM])
      obtain ⟨M', hM'⟩ := hexM
      refine ⟨hexP, ?_⟩
      intro P' hP'
      exact (ih T M' P' (heq M' P' hM' hP')).mp ((hnext T s hs).2 M' hM')
    · rintro ⟨hP, hnext⟩
      refine ⟨hcosupport.trans hP, ?_⟩
      intro T s hs
      obtain ⟨hexM, hexP, heq⟩ := htests T s (by rwa [hcosupport, hP])
      obtain ⟨P', hP'⟩ := hexP
      refine ⟨hexM, ?_⟩
      intro M' hM'
      exact (ih T M' P' (heq M' P' hM' hP')).mpr ((hnext T s hs).2 P' hP')

/-- The same finite tests also give the same presentation-equivalence classes.
Source: BMT 6.3 and node proof step 13
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile).

Proof: Induct on finite test depth. Equal cosupports give exactly the same next admissible
centers. The definition of `EquivalentThrough` supplies every controlled transform on both
sides, and induction identifies their subsequent cosupports. The empty-boundary condition
belongs to S and is shared. This uses the existing tests with their ordered boundary. -/
theorem modified_presentation_equivalence (D : ℕ) (a : DimensionHead)
    (S : Embedded (ULift.{u} ℚ)) (M P : Marked S) (h : Equivalent M P) :
    ModifiedPresents D a M ↔ ModifiedPresents D a P := by
  constructor
  · rintro ⟨hboundary, hM⟩
    exact ⟨hboundary, fun n ↦ (modifiedPresentsThrough_iff D a n S M P (h n)).mp (hM n)⟩
  · rintro ⟨hboundary, hP⟩
    exact ⟨hboundary, fun n ↦ (modifiedPresentsThrough_iff D a n S M P (h n)).mpr (hP n)⟩

/-- Common étale comparison retains the modified presentation and the ordered earlier-center
history. Earlier centers are history data, not new components of the initially empty test boundary.
Source: BMT 6.3, Remark 6.2 and node proof step 13
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile).

Proof: Use the history-comparison clause of
`lem-trf-hilbert-samuel-local-presentations` for the two common H-presentations. Smooth
invariance of the normalized head pulls the modified retaining-level locus back along the
étale comparison. Its cartesian squares pull the marked ideals and their controlled
transforms back. Induction on finite tests preserves the modified presentation on the first
side; equivalence gives it on the second side. The comparison's earlier-ideal equality
retains each ordered previous center and its induced boundary. -/
theorem modified_presentation_history_comparison (S T : Embedded (ULift.{u} ℚ))
    [IsReduced S.X] [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    [IsReduced T.X] [LocallyOfFiniteType (T.i ≫ T.p)] [QuasiCompact (T.i ≫ T.p)]
    (D : ℕ) (a : DimensionHead) (x : S.X) (y : T.X) (e : S.X ≅ T.X)
    (earlierS : List S.Z.IdealSheafData) (earlierT : List T.Z.IdealSheafData)
    (c : CommonComparison S T x y e earlierS earlierT)
    (M : Marked S) (P : Marked T) (hM : Presents M) (hP : Presents P)
    (hhead : ModifiedPresents D a M) :
    ∃ M' P' : Marked c.W,
      MarkedPullback c.f M M' ∧ MarkedPullback c.g P P' ∧ Equivalent M' P' ∧
      ModifiedPresents D a M' ∧ ModifiedPresents D a P' := by
  sorry

/-- A smooth center is locally head-constant exactly when it is locally H-constant.
Source: node proof steps 10--12 (blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile).

Proof: The finite locally closed level stratifications have the same components. Locally at
any point on a constant stratum remove the other components; the two equality loci agree.
Pull these neighborhoods back along the center map. Smoothness of the center and its
factorization through X are the unchanged conditions of `LocallyConstantCenter`. -/
theorem center_locallyConstant_iff (S : Embedded (ULift.{u} ℚ))
    [IsReduced S.X] [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    (D : ℕ) (hD : topologicalKrullDim S.X ≤ (D : WithBot ℕ∞)) (C : S.Z.IdealSheafData) :
    LocallyConstantCenter S C ↔
      Smooth (C.subschemeι ≫ S.p) ∧ ∃ c : C.subscheme ⟶ S.X,
        c ≫ S.i = C.subschemeι ∧ ∀ a : C.subscheme,
          ∃ U : C.subscheme.Opens, a ∈ U ∧ ∀ b : C.subscheme, b ∈ U →
            modifiedHead D S.X (c b) = modifiedHead D S.X (c a) := by
  sorry

/-- Nonincrease at every point of an admissible strict-transform blowup.
Source: BMT 6.3; node proof step 12
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile).

Proof: Every surviving strict-transform component is the closure of an open of an old
component, with the same function field and dimension. Its dimension profile is a subset
of the old profile. A smaller cardinality strictly lowers the first coordinate; otherwise
the profiles coincide and H-nonincrease gives head-nonincrease after the common sum.
The center condition is equivalently local head constancy by the preceding theorem. -/
theorem modifiedHead_nonincrease (S : Embedded (ULift.{u} ℚ))
    [IsReduced S.X] [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    (D : ℕ) (hD : topologicalKrullDim S.X ≤ (D : WithBot ℕ∞))
    (C : S.Z.IdealSheafData) (hC : LocallyConstantCenter S C) :
    ∀ x : C.strictTransform S.i,
      modifiedHead D (C.strictTransform S.i) x ≤
        modifiedHead D S.X (strictTransformToSource S.i C.blowupMap C.support.compl x) := by
  sorry

/-- The descending-chain condition applies to values encountered from one fixed initial X,
not to arbitrary integer sequences. Boundary lists are unrestricted and may record history.
Source: BMT 6.1 and 6.3; node proof step 14
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile).

Proof: In a strict descending chain the first coordinates eventually stabilize. Only finitely
many global component dimensions occur initially, and strict transforms inherit them. Pass
to a subsequence with the same minimum global dimension. Cancel the resulting common
summation to get infinitely many strict decreases of H, contrary to the descending-chain
clause `function_no_infinite_reachable_drops` of the presentation dependency in the fixed
ambient dimension. Reflexive transitive reachability permits passing to subsequences, even
when intervening blowups leave the value unchanged. -/
theorem modifiedHead_no_infinite_drops (S : Embedded (ULift.{u} ℚ))
    [IsReduced S.X] [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    (D : ℕ) (hD : topologicalKrullDim S.X ≤ (D : WithBot ℕ∞))
    (values : ℕ → DimensionHead)
    (hvalues : ∀ n : ℕ, ∃ T : Embedded (ULift.{u} ℚ),
      Relation.ReflTransGen BlowupTransition S T ∧
        ∃ x : T.X, modifiedHead D T.X x = values n) :
    ¬ ∀ n : ℕ, values (n + 1) < values n := by
  sorry

/-- Resolving a presentation removes its retained maximum head. All ordered exceptional
histories are allowed, with the exact existing normal-crossings and controlled transforms.
Source: BMT 6.3, first paragraph; node proof step 13
(blueprint: lem-trf-hilbert-samuel-smooth-dimension-profile).

Proof: Each finite stage identifies the retaining-head locus with the cosupport. After
emptying the final cosupport no point retains the old level. Nonincrease under the specified
admissible blowups excludes larger values, so all final values are strictly smaller.
The same argument on a finite presentation cover removes the head globally. -/
theorem modified_presentation_empty_maximum (S : Embedded (ULift.{u} ℚ))
    [IsReduced S.X] [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    (D : ℕ) (hD : topologicalKrullDim S.X ≤ (D : WithBot ℕ∞))
    (a : DimensionHead) (M : Marked S) (hM : ModifiedPresents D a M)
    (hmax : ∀ x : S.X, modifiedHead D S.X x ≤ a)
    (n : ℕ) (history : Fin (n + 1) → Embedded (ULift.{u} ℚ))
    (marks : ∀ j : Fin (n + 1), Marked (history j))
    (hstart : history 0 = S) (hstartMark : HEq (marks 0) M)
    (steps : ∀ j : Fin n, Step (history j.castSucc) (history j.succ))
    (hkinds : ∀ j : Fin n, (steps j).kind = .admissibleBlowup)
    (hadmissible : ∀ j : Fin n,
      (steps j).Admissible (modifiedLocus D a (history j.castSucc)))
    (htransforms : ∀ j : Fin n,
      (steps j).Transforms (marks j.castSucc) (marks j.succ))
    (hempty : (marks (Fin.last n)).cosupport = ∅) :
    ∀ x : (history (Fin.last n)).X, modifiedHead D (history (Fin.last n)).X x < a := by
  sorry

end AlgebraicGeometry.HilbertSamuel
