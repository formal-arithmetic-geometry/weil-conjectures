/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.AlgebraicGeometry.JetLevelBlowupHistory
public import Sheaf.AlgebraicGeometry.HilbertSamuelInvariant
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.StrictTransform
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.RingTheory.DiagonalJets
public import Sheaf.RingTheory.FormalInitialDiagram
public import Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum
public import Sheaf.AlgebraicGeometry.MarkedIdealOrder
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Sheaf.RingTheory.LengthOfSupportAtMaximalIdeal
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Jet minors, local level topology and reachable diagram bounds

Source: ILO VIII 2.3.11--2.3.13, pp.93--94; BM 1997, Remarks 9.1,
Theorem 9.2, Lemma 9.3 and Corollary 3.20; BMT §6.1
(blueprint: lem-trf-jet-level-topology-reachable-dcc).

The four statements give finite stalk lengths, affine jet presentations with all minor
loci, local finite variation and closed lexicographic upper levels, and the uniform
diagram bound and descending-chain condition across all finite blowup histories.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- The raw local lengths are finite, so the natural-valued encoding loses no information.
Source: ILO VIII 2.3.11--2.3.13; BM 1997, Remarks 9.1; BMT §6.1
(blueprint: lem-trf-jet-level-topology-reachable-dcc).

Proof (node step 1): finite type over the Noetherian field makes the scheme locally
Noetherian, by `lem-weil-pbc-finite-type-over-noetherian`. Its stalks are Noetherian
local rings. The cyclic quotient by the indicated power of the maximal ideal has
support only at that maximal ideal: at another prime a maximal-ideal element outside
the prime becomes an annihilating unit. Apply
`lem-sc-generic-stalk-finite-length` to obtain a finite length. -/
theorem jet_level_finite_lengths (S : JetLevelPair.{u}) [IsReduced S.X]
    [IsImmersion S.i] [Smooth S.p] [LocallyOfFiniteType (S.i ≫ S.p)]
    [QuasiCompact (S.i ≫ S.p)] :
    ∀ (x : S.X) (q : ℕ),
      Module.length (S.X.presheaf.stalk x)
        ((S.X.presheaf.stalk x) ⧸
          IsLocalRing.maximalIdeal (S.X.presheaf.stalk x) ^ (q + 1)) ≠ ⊤ := by
  have : IsLocallyNoetherian S.X :=
    LocallyOfFiniteType.isLocallyNoetherian (S.i ≫ S.p)
  intro x q
  let R := S.X.presheaf.stalk x
  let m := IsLocalRing.maximalIdeal R
  have hm : m ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hpow : m ^ (q + 1) ≠ ⊤ := by
    exact ne_top_of_le_ne_top hm (Ideal.pow_le_self (by omega))
  have : Nontrivial (R ⧸ m ^ (q + 1)) := Ideal.Quotient.nontrivial_iff.mpr hpow
  obtain ⟨n, _, hn⟩ := Module.length_eq_nat_of_support_subset_maximalIdeal
    R (R ⧸ m ^ (q + 1)) (by
      intro p hp
      have hle : m ^ (q + 1) ≤ p.asIdeal := by
        simpa only [Ideal.annihilator_quotient] using
          Module.mem_support_iff_of_finite.mp hp
      have hmle : m ≤ p.asIdeal := by
        intro a ha
        exact p.isPrime.mem_of_pow_mem (q + 1) (hle (Ideal.pow_mem_pow ha (q + 1)))
      exact (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le p.isPrime.ne_top hmle |>.symm)
  change Module.length R (R ⧸ m ^ (q + 1)) ≠ ⊤
  rw [hn]
  exact ENat.natCast_ne_top n

/-- Presentations and the determinantal descriptions on every affine open chart.
Integer thresholds retain the conventions for nonpositive and oversized thresholds.
Source: ILO VIII 2.3.11--2.3.13; BM 1997, Remarks 9.1; BMT §6.1
(blueprint: lem-trf-jet-level-topology-reachable-dcc).

Proof (node steps 1--2): `lem-weil-pbc-lft-affine-pairs` makes every affine coordinate
ring finite type over the ground field. `lem-weil-pbc-finite-type-algebra-noetherian`
makes it Noetherian. `lem-trf-jet-diagram-hilbert-control` gives finite jet modules and
identifies every fibre dimension, including at nonclosed points, with the extended
Hilbert--Samuel function. `lem-sc-noetherian-finite-module-finite-presentation` gives
the displayed finite presentation. Tensoring it with the residue field is right exact
by `lem-weil-pbc-tensor-right-exact`, so the fibre dimension is the number of generators
minus the specialized rank. A nonzero minor gives independent columns; conversely
`lem-weil-pbc-field-injective-matrix-nonzero-maximal-minor` gives a nonzero minor from
independent columns. Thus the upper locus is precisely the common vanishing of the
indicated minors. If there are too few columns all such minors vanish. Dimension lies
between zero and the number of generators, giving both endpoint conventions. -/
theorem jet_level_presentations (S : JetLevelPair.{u}) [IsReduced S.X]
    [IsImmersion S.i] [Smooth S.p] [LocallyOfFiniteType (S.i ≫ S.p)]
    [QuasiCompact (S.i ≫ S.p)]
    (A : Type u) [CommRing A] [Algebra (ULift.{u} ℚ) A]
    (j : Spec (.of A) ⟶ S.X) [IsOpenImmersion j]
    (hj : j ≫ S.i ≫ S.p = Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℚ) A)))
    (q : ℕ) :
    ∃ (r v : ℕ) (M : Matrix (Fin v) (Fin r) A)
      (π : (Fin v → A) →ₗ[A] DiagonalJets.principalParts (ULift.{u} ℚ) A q),
      Function.Surjective π ∧ LinearMap.range M.toLin' = LinearMap.ker π ∧
      (∀ c : ℤ, 1 ≤ c → c ≤ (v : ℤ) →
        {x : Spec (.of A) | c ≤ (function (k := ULift.{u} ℚ) (S.i ≫ S.p) (j x) q : ℤ)} =
          {x : Spec (.of A) |
            ∀ (rows : Fin (v - c.toNat + 1) → Fin v)
              (cols : Fin (v - c.toNat + 1) → Fin r),
              Function.Injective rows → Function.Injective cols →
                (M.submatrix rows cols).det ∈ x.asIdeal}) ∧
      (∀ c : ℤ, c ≤ 0 →
        {x : Spec (.of A) | c ≤ (function (k := ULift.{u} ℚ) (S.i ≫ S.p) (j x) q : ℤ)} = Set.univ) ∧
      (∀ c : ℤ, (v : ℤ) < c →
        {x : Spec (.of A) | c ≤ (function (k := ULift.{u} ℚ) (S.i ≫ S.p) (j x) q : ℤ)} = ∅) := by
  sorry

/-- Local finite variation, finite first-difference bounds, and closed lexicographic upper levels.
Source: ILO VIII 2.3.11--2.3.13; BM 1997, Theorem 9.2 and Lemma 9.3; BMT §6.1
(blueprint: lem-trf-jet-level-topology-reachable-dcc).

Proof (node steps 2--4): the minor loci make every coordinate sublevel open. Work where
the immersion is closed in a smooth affine ambient. The coordinate assertion of
`lem-trf-smooth-pair-blowup-local-models`, applied to the identity immersion, gives etale
coordinates. `lem-trf-jet-diagram-hilbert-control` gives locally finitely many Taylor
diagrams and identifies their counts with the extended function; its etale compatibility
includes nonclosed points. Shrink to an affine neighbourhood of the point and take its
finite image as F. Bound the first differing indices of the finitely many unequal pairs
in F, taking zero if there are none. The intersection of the coordinate sublevels up to
that bound is an open neighbourhood. Any distinct value there has a smaller entry at
its first difference, proving the lexicographic inequality. For any threshold sequence,
these neighbourhoods cover its strict sublevel, so its complementary upper level is closed. -/
theorem jet_level_topology (S : JetLevelPair.{u}) [IsReduced S.X]
    [IsImmersion S.i] [Smooth S.p] [LocallyOfFiniteType (S.i ≫ S.p)]
    [QuasiCompact (S.i ≫ S.p)] :
    (∀ a : S.X, ∃ (U : S.X.Opens) (F : Finset (ℕ → ℕ)) (q₀ : ℕ),
      a ∈ U ∧ IsAffineOpen U ∧
      (∀ x : S.X, x ∈ U → function (k := ULift.{u} ℚ) (S.i ≫ S.p) x ∈ F) ∧
      (∀ f ∈ F, ∀ g ∈ F, f ≠ g → ∃ n : ℕ, n ≤ q₀ ∧ f n ≠ g n ∧
        ∀ i : ℕ, i < n → f i = g i) ∧
      IsOpen {x : S.X | x ∈ U ∧ ∀ q : ℕ, q ≤ q₀ →
        function (k := ULift.{u} ℚ) (S.i ≫ S.p) x q ≤ function (k := ULift.{u} ℚ) (S.i ≫ S.p) a q} ∧
      (∀ x : S.X, x ∈ U →
        (∀ q : ℕ, q ≤ q₀ →
          function (k := ULift.{u} ℚ) (S.i ≫ S.p) x q ≤
            function (k := ULift.{u} ℚ) (S.i ≫ S.p) a q) →
          le (function (k := ULift.{u} ℚ) (S.i ≫ S.p) x)
            (function (k := ULift.{u} ℚ) (S.i ≫ S.p) a))) ∧
    ∀ v : ℕ → ℕ, IsClosed {x : S.X | le v (function (k := ULift.{u} ℚ) (S.i ≫ S.p) x)} := by
  sorry

/-- A fixed finite ambient coordinate cover bounds diagrams after all finite histories.
The geometry is a conclusion, including for empty centers and whole-component centers.
The last clause compares arbitrary reached values, regardless of history lengths or plateaus.
Source: ILO VIII 2.3.11--2.3.13; BM 1997, Corollary 3.20 and Lemma 9.3; BMT §6.1
(blueprint: lem-trf-jet-level-topology-reachable-dcc).

Proof (node steps 5--7): track each initial coordinate chart and induct on the finite
history. On affine restrictions `lem-trf-smooth-center-blowup-geometry` preserves ambient
smoothness and reduced strict transforms. `lem-trf-strict-transform-flat-etale-base-change`
identifies these local restrictions with the global transforms. Near a center,
`lem-trf-smooth-pair-blowup-local-models` gives an etale coordinate-subspace model.
`lem-trf-coordinate-subspace-blowup-charts` uses a+b coordinates on every nonempty chart:
a old coordinates, one distinguished center coordinate, and b-1 ratios. For b=0 the
blowup is empty; off the center it is unchanged. `sbc-lem-affine-space-smooth` and
`lem-sbc-smooth-relative-dimension-permanence` show that the coordinate number equals the
original local relative dimension, hence remains at most d. The jet-diagram theorem
represents the extended function of each reduced transform by the count of a Taylor
diagram in that many variables. Pad such a diagram to d variables by placing all
monomials involving an extra variable in the ideal. Its complement is exactly the old
complement with zero extra coordinates, so its count is unchanged. An infinite strict
descent anywhere in the reachable value family contradicts the fixed-dimension
no-descent clause of `lem-trf-jet-diagram-hilbert-control`. Diagrams are chosen separately
for each value, so no relation between the different histories is required. -/
theorem jet_level_reachable_diagrams_dcc (S : JetLevelPair.{u}) [IsReduced S.X]
    [IsImmersion S.i] [Smooth S.p] [LocallyOfFiniteType (S.i ≫ S.p)]
    [QuasiCompact (S.i ≫ S.p)]
    (d m : ℕ) (U : Fin m → S.Z.Opens) (e : Fin m → ℕ)
    (c : ∀ t : Fin m, (U t).toScheme ⟶
      Spec (.of (MvPolynomial (Fin (e t)) (ULift.{u} ℚ))))
    (haff : ∀ t : Fin m, IsAffineOpen (U t))
    (het : ∀ t : Fin m, Etale (c t))
    (hbase : ∀ t : Fin m, c t ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℚ)
        (MvPolynomial (Fin (e t)) (ULift.{u} ℚ)))) = (U t).ι ≫ S.p)
    (hcover : ∀ x : S.X, ∃ t : Fin m, S.i x ∈ U t)
    (hbound : ∀ t : Fin m, e t ≤ d) :
    (∀ T : JetLevelPair.{u}, JetLevelReachable S T →
      Smooth T.p ∧ IsReduced T.X ∧
      ∀ x : T.X, ∃ (a : ℕ) (_ : a ≤ d) (V : T.Z.Opens) (y : V.toScheme)
        (coord : MvPolynomial (Fin a) (ULift.{u} ℚ) →+* Γ(V.toScheme, ⊤))
        (τ : V.toScheme.presheaf.stalk y →+*
          MvPowerSeries (Fin a) (V.toScheme.residueField y)),
        V.ι y = T.i x ∧ IsAffineOpen V ∧
        Etale (V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom coord)) ∧
        V.toScheme.toSpecΓ ≫
          Spec.map (CommRingCat.ofHom (coord.comp MvPolynomial.C)) = V.ι ≫ T.p ∧
        HilbertCoefficient.isTaylorMap
          ((V.toScheme.presheaf.germ ⊤ y (by trivial)).hom.comp coord)
          (V.toScheme.residue y).hom τ ∧
        function (k := ULift.{u} ℚ) (T.i ≫ T.p) x =
          MonomialDiagram.hilbertCount (MonomialDiagram.initialDiagram
            (HilbertCoefficient.taylorIdeal (stalkIdeal (T.i.ker.comap V.ι) y) τ))) ∧
    (∀ values : ℕ → ℕ → ℕ,
      (∀ n : ℕ, ∃ T : JetLevelPair.{u}, JetLevelReachable S T ∧
        ∃ x : T.X, function (k := ULift.{u} ℚ) (T.i ≫ T.p) x = values n) →
          ¬ ∀ n : ℕ, lt (values (n + 1)) (values n)) := by
  sorry

end AlgebraicGeometry.HilbertSamuel
