/-
Formalization of Chapter 3, Section 4 of `weil_conjectures_chapter3.tex`:
"Finite geometric-Frobenius orbits" (`sec:weil-finite-orbits`).

Every declaration below is annotated with the LaTeX label it formalizes.
Design notes, following the conventions of the earlier section files:

* No coefficient ring is in scope in this purely combinatorial section, so
  the file is independent of the power-series development; Euler products
  resume in the next section.
* `F^{[n]}(x)` of the text is `(⇑D.frobenius)^[n] x` (`Function.iterate`),
  and `F^z` for `z : ℤ` is the group power in `Equiv.Perm D.points`,
  applied to points through the coercion, exactly as prescribed by the
  section preamble.
* The orbit set `|O|` of the text is `MulAction.orbitRel.Quotient.orbit O`,
  and `[x]_F` is `Quotient.mk'' x` (bundled as `orbitClass` at its tex
  position `def:weil-frobenius-orbit-class`).
* Orbit quotients carry no decidable equality, so the finsets built from
  them (`pointFinset`, `boundedOrbitFinset`, ...) are defined under
  `open scoped Classical in`; the whole file is a `noncomputable section`
  as prescribed by the chapter preamble.
* Two-part tex statements (`lemma:weil-frobenius-orbit-representative-class`)
  are provided as separate component lemmas together with the bundled
  conjunction under the tex name.
* `lemma:weil-relevant-orbits-regroup-by-degree` is proved by decomposing
  `relevantOrbitFinset` as a `Finset.biUnion` of the one-degree orbit
  finsets; the sigma-type equivalence demanded by
  `lemma:weil-relevant-orbit-degree-sigma-equiv` is provided as stated.
-/
module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic

@[expose] public section

namespace Weil

noncomputable section

universe u

/-- `def:weil-finite-orbit-frobenius-datum`.  A finite-orbit
geometric-Frobenius datum: a type of points with a permutation `frobenius`
modeling geometric Frobenius, a positive period function certifying that
every point is periodic, and, for every positive `n`, a finset of the
`n`-fold fixed points with its membership characterization. -/
structure FiniteOrbitFrobeniusData where
  points : Type u
  frobenius : Equiv.Perm points
  period : points → ℕ
  period_pos : ∀ x, 0 < period x
  iterate_period : ∀ x, (⇑frobenius)^[period x] x = x
  positiveFixedPoints : (n : ℕ) → 0 < n → Finset points
  mem_positiveFixedPoints : ∀ (n : ℕ) (h : 0 < n) (x : points),
    x ∈ positiveFixedPoints n h ↔ (⇑frobenius)^[n] x = x

namespace FiniteOrbitFrobeniusData

/-- `def:weil-frobenius-fixed-point-finset`.  The total fixed-point finset
`Fix_D(n)`, extending `positiveFixedPoints` by the empty finset at `n = 0`;
by proof irrelevance the positive branch is independent of the witness. -/
def fixedPointFinset (D : FiniteOrbitFrobeniusData) (n : ℕ) : Finset D.points :=
  if h : 0 < n then D.positiveFixedPoints n h else ∅

/-- `lemma:weil-frobenius-fixed-point-finset-mem`.  Membership in the total
fixed-point finset at a positive index. -/
theorem mem_fixedPointFinset (D : FiniteOrbitFrobeniusData) {n : ℕ}
    (hn : 0 < n) (x : D.points) :
    x ∈ D.fixedPointFinset n ↔ (⇑D.frobenius)^[n] x = x := by
  rw [fixedPointFinset, dif_pos hn]
  exact D.mem_positiveFixedPoints n hn x

/-- `def:weil-frobenius-orbit-length`.  The Frobenius orbit length
`d_F(x) = Function.minimalPeriod F x`. -/
def orbitLength (D : FiniteOrbitFrobeniusData) (x : D.points) : ℕ :=
  Function.minimalPeriod (⇑D.frobenius) x

/-- `lemma:weil-frobenius-orbit-length-positive`.  Positivity of the
Frobenius orbit length: the stored period data makes every point a periodic
point. -/
theorem orbitLength_pos (D : FiniteOrbitFrobeniusData) (x : D.points) :
    0 < D.orbitLength x :=
  Function.minimalPeriod_pos_of_mem_periodicPts
    ⟨D.period x, D.period_pos x, D.iterate_period x⟩

/-- `lemma:weil-frobenius-fixed-iff-orbit-length-divides`.  Fixed-point
criterion from the minimal period: `F^{[n]}(x) = x ↔ d_F(x) ∣ n`. -/
theorem isPeriodicPt_iff_dvd (D : FiniteOrbitFrobeniusData) {n : ℕ}
    (_hn : 1 ≤ n) (x : D.points) :
    (⇑D.frobenius)^[n] x = x ↔ D.orbitLength x ∣ n :=
  Function.isPeriodicPt_iff_minimalPeriod_dvd

/-- `def:weil-frobenius-cyclic-subgroup`.  The cyclic subgroup
`Γ_F = Subgroup.zpowers F` of `Equiv.Perm points`, acting on points by
evaluation. -/
abbrev cyclicSubgroup (D : FiniteOrbitFrobeniusData) :
    Subgroup (Equiv.Perm D.points) :=
  Subgroup.zpowers D.frobenius

/-- `def:weil-frobenius-orbit-type`.  The type of Frobenius orbits,
`Orb_F(Ω) = MulAction.orbitRel.Quotient Γ_F Ω`. -/
def Orbit (D : FiniteOrbitFrobeniusData) :=
  MulAction.orbitRel.Quotient D.cyclicSubgroup D.points

/-- `def:weil-frobenius-orbit-representative`.  The selected representative
`rep(O) = Quotient.out O` of a Frobenius orbit. -/
def Orbit.representative {D : FiniteOrbitFrobeniusData} (O : D.Orbit) :
    D.points :=
  Quotient.out O

/-- `lemma:weil-frobenius-orbit-representative-class`, class part:
`[rep(O)]_F = O`. -/
theorem Orbit.mk_representative_class {D : FiniteOrbitFrobeniusData}
    (O : D.Orbit) :
    (Quotient.mk'' O.representative : D.Orbit) = O :=
  Quotient.out_eq' O

/-- `lemma:weil-frobenius-orbit-representative-class`, membership part:
`rep(O) ∈ |O|`. -/
theorem Orbit.representative_mem_orbit {D : FiniteOrbitFrobeniusData}
    (O : D.Orbit) :
    O.representative ∈ MulAction.orbitRel.Quotient.orbit O :=
  MulAction.orbitRel.Quotient.mem_orbit.mpr O.mk_representative_class

/-- `lemma:weil-frobenius-orbit-representative-class`, bundled as in the
text. -/
theorem Orbit.mk_representative {D : FiniteOrbitFrobeniusData} (O : D.Orbit) :
    (Quotient.mk'' O.representative : D.Orbit) = O ∧
      O.representative ∈ MulAction.orbitRel.Quotient.orbit O :=
  ⟨O.mk_representative_class, O.representative_mem_orbit⟩

/-- `def:weil-frobenius-orbit-degree`.  The intrinsic degree
`deg_F(O) = ncard |O|` of a Frobenius orbit; finiteness and positivity are
proved separately below, not silently included here. -/
def Orbit.degree {D : FiniteOrbitFrobeniusData} (O : D.Orbit) : ℕ :=
  (MulAction.orbitRel.Quotient.orbit O).ncard

/-- Helper for `lemma:weil-frobenius-orbit-finite`: the
`Subgroup.zpowers`-orbit of any point is finite, by transporting finiteness
of `ZMod d` (`d = d_F(x) > 0`) across `MulAction.orbitZPowersEquiv`. -/
theorem orbit_zpowers_finite (D : FiniteOrbitFrobeniusData) (x : D.points) :
    (MulAction.orbit D.cyclicSubgroup x).Finite := by
  have : NeZero (Function.minimalPeriod (D.frobenius • ·) x) :=
    ⟨(D.orbitLength_pos x).ne'⟩
  exact Set.finite_coe_iff.mp
    (Finite.of_equiv _ (MulAction.orbitZPowersEquiv D.frobenius x).symm)

/-- Helper for the degree lemmas: the cardinality of the
`Subgroup.zpowers`-orbit of `x` is the minimal period of `x`, by
`MulAction.minimalPeriod_eq_card`. -/
theorem ncard_orbit_zpowers (D : FiniteOrbitFrobeniusData) (x : D.points) :
    (MulAction.orbit D.cyclicSubgroup x).ncard = D.orbitLength x := by
  have := (D.orbit_zpowers_finite x).fintype
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    ← MulAction.minimalPeriod_eq_card]
  rfl

/-- `lemma:weil-frobenius-orbit-finite`.  Every Frobenius orbit is finite. -/
theorem Orbit.finite {D : FiniteOrbitFrobeniusData} (O : D.Orbit) :
    (MulAction.orbitRel.Quotient.orbit O).Finite := by
  rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq']
  exact D.orbit_zpowers_finite (Quotient.out O)

/-- `lemma:weil-frobenius-orbit-degree-representative`.  The orbit degree is
the minimal period of the selected representative. -/
theorem Orbit.degree_eq_minimalPeriod {D : FiniteOrbitFrobeniusData}
    (O : D.Orbit) :
    O.degree = D.orbitLength O.representative := by
  show (MulAction.orbitRel.Quotient.orbit O).ncard = D.orbitLength O.representative
  rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq']
  exact D.ncard_orbit_zpowers (Quotient.out O)

/-- `lemma:weil-frobenius-orbit-degree-positive`.  Every Frobenius orbit has
positive degree. -/
theorem Orbit.degree_pos {D : FiniteOrbitFrobeniusData} (O : D.Orbit) :
    0 < O.degree := by
  rw [O.degree_eq_minimalPeriod]
  exact D.orbitLength_pos O.representative

/-- `lemma:weil-frobenius-orbit-degree-point`.  The degree of the orbit
containing a point is the orbit length of that point. -/
theorem degree_mk (D : FiniteOrbitFrobeniusData) (x : D.points) :
    Orbit.degree (Quotient.mk'' x : D.Orbit) = D.orbitLength x := by
  show (MulAction.orbitRel.Quotient.orbit (Quotient.mk'' x : D.Orbit)).ncard =
    D.orbitLength x
  rw [MulAction.orbitRel.Quotient.orbit_mk]
  exact D.ncard_orbit_zpowers x

/-- `lemma:weil-frobenius-fixed-iff-orbit-degree-divides`.  Fixed-point
criterion in terms of intrinsic orbit degree. -/
theorem fixed_iff_degree_dvd (D : FiniteOrbitFrobeniusData) {n : ℕ}
    (hn : 1 ≤ n) (x : D.points) :
    (⇑D.frobenius)^[n] x = x ↔ Orbit.degree (Quotient.mk'' x : D.Orbit) ∣ n := by
  rw [D.degree_mk x]
  exact D.isPeriodicPt_iff_dvd hn x

open scoped Classical in
/-- `def:weil-frobenius-orbit-point-finset`.  The explicit finset
`P(O) = (range d_F(rep O)).image (j ↦ F^{[j]}(rep O))` of points of an
orbit. -/
def Orbit.pointFinset {D : FiniteOrbitFrobeniusData} (O : D.Orbit) :
    Finset D.points :=
  (Finset.range (D.orbitLength O.representative)).image
    fun j => (⇑D.frobenius)^[j] O.representative

/-- `lemma:weil-frobenius-zpow-bounded-representative`.  Every integer
iterate of a point agrees with a natural iterate of bounded exponent. -/
theorem zpow_eq_iterate_val (D : FiniteOrbitFrobeniusData) (x : D.points)
    (z : ℤ) :
    ∃ j < D.orbitLength x, (D.frobenius ^ z) x = (⇑D.frobenius)^[j] x := by
  have hd : 0 < D.orbitLength x := D.orbitLength_pos x
  have hd' : ((D.orbitLength x : ℤ)) ≠ 0 := by exact_mod_cast hd.ne'
  have h0 : (0 : ℤ) ≤ z % (D.orbitLength x : ℤ) := Int.emod_nonneg z hd'
  have hlt : z % (D.orbitLength x : ℤ) < (D.orbitLength x : ℤ) :=
    Int.emod_lt_of_pos z (by exact_mod_cast hd)
  refine ⟨(z % (D.orbitLength x : ℤ)).toNat, by omega, ?_⟩
  have hmod := MulAction.zpow_smul_mod_minimalPeriod D.frobenius x z
  have hj : (((z % (D.orbitLength x : ℤ)).toNat : ℤ)) =
      z % (D.orbitLength x : ℤ) := Int.toNat_of_nonneg h0
  calc (D.frobenius ^ z) x
      = D.frobenius ^ z • x := rfl
    _ = D.frobenius ^ (z % (D.orbitLength x : ℤ)) • x := hmod.symm
    _ = D.frobenius ^ (((z % (D.orbitLength x : ℤ)).toNat : ℕ) : ℤ) • x := by
        rw [hj]
    _ = (D.frobenius ^ (z % (D.orbitLength x : ℤ)).toNat) • x := by
        rw [zpow_natCast]
    _ = (⇑D.frobenius)^[(z % (D.orbitLength x : ℤ)).toNat] x := by
        rw [Equiv.Perm.smul_def, Equiv.Perm.coe_pow]

/-- `lemma:weil-frobenius-orbit-point-finset-mem`.  The explicit orbit finset
has exactly the members of `|O|`. -/
theorem Orbit.mem_pointFinset {D : FiniteOrbitFrobeniusData} (O : D.Orbit)
    (y : D.points) :
    y ∈ O.pointFinset ↔ y ∈ MulAction.orbitRel.Quotient.orbit O := by
  classical
  constructor
  · intro hy
    rw [pointFinset, Finset.mem_image] at hy
    obtain ⟨j, -, rfl⟩ := hy
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq']
    refine MulAction.mem_orbit_iff.mpr
      ⟨⟨D.frobenius ^ (j : ℤ), Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), rfl⟩⟩, ?_⟩
    show D.frobenius ^ (j : ℤ) • O.representative =
      (⇑D.frobenius)^[j] O.representative
    rw [zpow_natCast, Equiv.Perm.smul_def, Equiv.Perm.coe_pow]
  · intro hy
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq',
      MulAction.mem_orbit_iff] at hy
    obtain ⟨g, hgy⟩ := hy
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp g.2
    obtain ⟨j, hj, hzj⟩ := D.zpow_eq_iterate_val (Quotient.out O) z
    rw [pointFinset, Finset.mem_image]
    refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
    show (⇑D.frobenius)^[j] (Quotient.out O) = y
    have hgz : g • Quotient.out O = (D.frobenius ^ z) (Quotient.out O) := by
      rw [Subgroup.smul_def, hz, Equiv.Perm.smul_def]
    rw [← hgy, hgz, hzj]

/-- `lemma:weil-frobenius-orbit-point-finset-card`.  The explicit orbit
finset has cardinality `deg_F(O)`. -/
theorem Orbit.card_pointFinset {D : FiniteOrbitFrobeniusData} (O : D.Orbit) :
    O.pointFinset.card = O.degree := by
  rw [degree, ← Set.ncard_coe_finset O.pointFinset]
  congr 1
  ext y
  rw [Finset.mem_coe, O.mem_pointFinset y]

/-- `lemma:weil-frobenius-orbit-point-finsets-disjoint`.  Distinct orbits
have disjoint point finsets. -/
theorem Orbit.pointFinset_disjoint {D : FiniteOrbitFrobeniusData}
    {O O' : D.Orbit} (h : O ≠ O') :
    Disjoint O.pointFinset O'.pointFinset := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  apply h
  have h1 := MulAction.orbitRel.Quotient.mem_orbit.mp ((O.mem_pointFinset y).mp hy)
  have h2 := MulAction.orbitRel.Quotient.mem_orbit.mp ((O'.mem_pointFinset y).mp hy')
  exact h1.symm.trans h2

/-- `def:weil-frobenius-orbit-class`.  The orbit class `cl_F(x) = [x]_F` of a
point. -/
def orbitClass (D : FiniteOrbitFrobeniusData) (x : D.points) : D.Orbit :=
  Quotient.mk'' x

open scoped Classical in
/-- `def:weil-bounded-frobenius-orbit-finset`.  The finset `𝒪_{≤ r}` of
orbits of degree at most `r`, carved out of the image of `Fix_D(r!)` under
`cl_F`. -/
def boundedOrbitFinset (D : FiniteOrbitFrobeniusData) (r : ℕ) :
    Finset D.Orbit :=
  ((D.fixedPointFinset (Nat.factorial r)).image D.orbitClass).filter
    fun O => Orbit.degree O ≤ r

/-- `lemma:weil-bounded-frobenius-orbit-finset-mem`.  Membership criterion
for the bounded orbit finsets at positive bounds. -/
theorem mem_boundedOrbitFinset (D : FiniteOrbitFrobeniusData) {r : ℕ}
    (_hr : 1 ≤ r) (O : D.Orbit) :
    O ∈ D.boundedOrbitFinset r ↔ Orbit.degree O ≤ r := by
  classical
  rw [boundedOrbitFinset, Finset.mem_filter]
  constructor
  · exact fun hO => hO.2
  · intro hO
    refine ⟨Finset.mem_image.mpr ⟨O.representative, ?_, ?_⟩, hO⟩
    · refine (D.mem_fixedPointFinset (Nat.factorial_pos r) _).mpr ?_
      refine (D.fixed_iff_degree_dvd (Nat.factorial_pos r) O.representative).mpr ?_
      rw [O.mk_representative_class]
      exact Nat.dvd_factorial O.degree_pos hO
    · exact O.mk_representative_class

open scoped Classical in
/-- `def:weil-degree-frobenius-orbit-finset`.  The finset `𝒪_m` of orbits of
one degree `m`. -/
def degreeOrbitFinset (D : FiniteOrbitFrobeniusData) (m : ℕ) :
    Finset D.Orbit :=
  (D.boundedOrbitFinset m).filter fun O => Orbit.degree O = m

/-- `lemma:weil-degree-frobenius-orbit-finset-mem`.  Membership criterion for
the one-degree orbit finsets at positive degrees. -/
theorem mem_degreeOrbitFinset (D : FiniteOrbitFrobeniusData) {m : ℕ}
    (hm : 1 ≤ m) (O : D.Orbit) :
    O ∈ D.degreeOrbitFinset m ↔ Orbit.degree O = m := by
  rw [degreeOrbitFinset, Finset.mem_filter]
  constructor
  · exact fun hO => hO.2
  · exact fun hO => ⟨(D.mem_boundedOrbitFinset hm O).mpr hO.le, hO⟩

/-- `def:weil-frobenius-orbit-count`.  The number `a_m(D) = #𝒪_m` of
Frobenius orbits of one degree. -/
def orbitCount (D : FiniteOrbitFrobeniusData) (m : ℕ) : ℕ :=
  (D.degreeOrbitFinset m).card

open scoped Classical in
/-- `def:weil-relevant-frobenius-orbit-finset`.  The finset `𝒪(n)` of orbits
relevant for the `n`-th Frobenius power: bounded orbits whose degree divides
`n`. -/
def relevantOrbitFinset (D : FiniteOrbitFrobeniusData) (n : ℕ) :
    Finset D.Orbit :=
  (D.boundedOrbitFinset n).filter fun O => Orbit.degree O ∣ n

/-- `lemma:weil-relevant-frobenius-orbit-finset-mem`.  Membership criterion
for the relevant orbit finsets at positive indices. -/
theorem mem_relevantOrbitFinset (D : FiniteOrbitFrobeniusData) {n : ℕ}
    (hn : 1 ≤ n) (O : D.Orbit) :
    O ∈ D.relevantOrbitFinset n ↔ Orbit.degree O ∣ n := by
  rw [relevantOrbitFinset, Finset.mem_filter]
  constructor
  · exact fun hO => hO.2
  · intro hO
    exact ⟨(D.mem_boundedOrbitFinset hn O).mpr (Nat.le_of_dvd hn hO), hO⟩

open scoped Classical in
/-- `def:weil-fixed-point-orbit-union`.  The orbitwise union
`U_n = ⋃_{O ∈ 𝒪(n)} P(O)` of fixed points. -/
def fixedPointOrbitUnion (D : FiniteOrbitFrobeniusData) (n : ℕ) :
    Finset D.points :=
  (D.relevantOrbitFinset n).biUnion fun O => Orbit.pointFinset O

/-- `lemma:weil-fixed-point-orbit-union-eq`.  The orbitwise union is exactly
the fixed-point finset at positive indices. -/
theorem fixedPointOrbitUnion_eq (D : FiniteOrbitFrobeniusData) {n : ℕ}
    (hn : 1 ≤ n) :
    D.fixedPointOrbitUnion n = D.fixedPointFinset n := by
  classical
  ext x
  rw [fixedPointOrbitUnion, Finset.mem_biUnion, D.mem_fixedPointFinset hn x]
  constructor
  · rintro ⟨O, hO, hx⟩
    have hxO : (Quotient.mk'' x : D.Orbit) = O :=
      MulAction.orbitRel.Quotient.mem_orbit.mp ((O.mem_pointFinset x).mp hx)
    rw [D.fixed_iff_degree_dvd hn x, hxO]
    exact (D.mem_relevantOrbitFinset hn O).mp hO
  · intro hx
    refine ⟨Quotient.mk'' x, ?_, ?_⟩
    · exact (D.mem_relevantOrbitFinset hn _).mpr
        ((D.fixed_iff_degree_dvd hn x).mp hx)
    · exact (Orbit.mem_pointFinset _ x).mpr
        (MulAction.orbitRel.Quotient.mem_orbit.mpr rfl)

/-- `def:weil-frobenius-fixed-point-count`.  The number of fixed points
`N_n(D) = #Fix_D(n)`. -/
def fixedPointCount (D : FiniteOrbitFrobeniusData) (n : ℕ) : ℕ :=
  (D.fixedPointFinset n).card

/-- `lemma:weil-fixed-point-count-relevant-orbits`.  Fixed points counted by
relevant orbits: `N_n(D) = ∑_{O ∈ 𝒪(n)} deg_F(O)`. -/
theorem fixedPointCount_eq_sum_orbits (D : FiniteOrbitFrobeniusData) {n : ℕ}
    (hn : 1 ≤ n) :
    D.fixedPointCount n = ∑ O ∈ D.relevantOrbitFinset n, Orbit.degree O := by
  classical
  have hdisj : ∀ O ∈ D.relevantOrbitFinset n, ∀ O' ∈ D.relevantOrbitFinset n,
      O ≠ O' → Disjoint (Orbit.pointFinset O) (Orbit.pointFinset O') :=
    fun O _ O' _ hne => Orbit.pointFinset_disjoint hne
  rw [fixedPointCount, ← D.fixedPointOrbitUnion_eq hn, fixedPointOrbitUnion,
    Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl fun O _ => O.card_pointFinset

/-- `lemma:weil-relevant-orbit-degree-sigma-equiv`.  Relevant orbits as a
sigma type over divisors: `O ↦ (deg_F(O), O)`. -/
def relevantOrbitDegreeSigmaEquiv (D : FiniteOrbitFrobeniusData) {n : ℕ}
    (hn : 0 < n) :
    {O : D.Orbit // O ∈ D.relevantOrbitFinset n} ≃
      Σ m : {m : ℕ // m ∈ n.divisors},
        {O : D.Orbit // O ∈ D.degreeOrbitFinset m.1} where
  toFun O :=
    ⟨⟨Orbit.degree O.1,
        Nat.mem_divisors.mpr ⟨(D.mem_relevantOrbitFinset hn O.1).mp O.2, hn.ne'⟩⟩,
      ⟨O.1, (D.mem_degreeOrbitFinset O.1.degree_pos O.1).mpr rfl⟩⟩
  invFun p :=
    ⟨p.2.1, by
      have hm : p.1.1 ∣ n := (Nat.mem_divisors.mp p.1.2).1
      have hm0 : 0 < p.1.1 := Nat.pos_of_dvd_of_pos hm hn
      have hdeg : Orbit.degree p.2.1 = p.1.1 :=
        (D.mem_degreeOrbitFinset hm0 p.2.1).mp p.2.2
      exact (D.mem_relevantOrbitFinset hn p.2.1).mpr (by rw [hdeg]; exact hm)⟩
  left_inv O := Subtype.ext rfl
  right_inv p := by
    obtain ⟨⟨m, hm⟩, ⟨O, hO⟩⟩ := p
    have hm0 : 0 < m := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hm).1 hn
    have hdeg : Orbit.degree O = m := (D.mem_degreeOrbitFinset hm0 O).mp hO
    subst hdeg
    rfl

/-- `lemma:weil-relevant-orbits-regroup-by-degree`.  Regrouping relevant
orbits by degree: `∑_{O ∈ 𝒪(n)} deg_F(O) = ∑_{m ∣ n} m · a_m(D)`. -/
theorem sum_relevant_eq_sum_divisors (D : FiniteOrbitFrobeniusData) {n : ℕ}
    (hn : 1 ≤ n) :
    ∑ O ∈ D.relevantOrbitFinset n, Orbit.degree O =
      ∑ m ∈ n.divisors, m * D.orbitCount m := by
  classical
  have hunion : D.relevantOrbitFinset n =
      n.divisors.biUnion fun m => D.degreeOrbitFinset m := by
    ext O
    rw [Finset.mem_biUnion, D.mem_relevantOrbitFinset hn O]
    constructor
    · intro hdvd
      exact ⟨Orbit.degree O, Nat.mem_divisors.mpr ⟨hdvd, by omega⟩,
        (D.mem_degreeOrbitFinset O.degree_pos O).mpr rfl⟩
    · rintro ⟨m, hm, hO⟩
      rw [(D.mem_degreeOrbitFinset (Nat.pos_of_mem_divisors hm) O).mp hO]
      exact (Nat.mem_divisors.mp hm).1
  have hdisj : (↑n.divisors : Set ℕ).PairwiseDisjoint
      fun m => D.degreeOrbitFinset m := by
    intro m hm m' hm' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro O hO hO'
    apply hne
    rw [← (D.mem_degreeOrbitFinset (Nat.pos_of_mem_divisors hm) O).mp hO,
      ← (D.mem_degreeOrbitFinset (Nat.pos_of_mem_divisors hm') O).mp hO']
  rw [hunion, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : 1 ≤ m := Nat.pos_of_mem_divisors hm
  calc ∑ O ∈ D.degreeOrbitFinset m, Orbit.degree O
      = ∑ _O ∈ D.degreeOrbitFinset m, m :=
        Finset.sum_congr rfl fun O hO => (D.mem_degreeOrbitFinset hm1 O).mp hO
    _ = (D.degreeOrbitFinset m).card * m := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = m * D.orbitCount m := by rw [orbitCount, mul_comm]

/-- `prop:weil-fixed-points-orbit-count`.  Fixed points counted orbit by
orbit: `N_n(D) = ∑_{m ∣ n} m · a_m(D)`. -/
theorem fixedPointCount_eq_divisorSum (D : FiniteOrbitFrobeniusData) {n : ℕ}
    (hn : 1 ≤ n) :
    D.fixedPointCount n = ∑ m ∈ n.divisors, m * D.orbitCount m := by
  rw [D.fixedPointCount_eq_sum_orbits hn, D.sum_relevant_eq_sum_divisors hn]

/-- `def:weil-orbit-count-mobius-numerator`.  The Möbius numerator
`M_m(D) = ∑_{r ∣ m} μ(r) N_{m/r}(D)` of an orbit count, as an integer. -/
def mobiusNumerator (D : FiniteOrbitFrobeniusData) (m : ℕ) : ℤ :=
  ∑ r ∈ m.divisors,
    ArithmeticFunction.moebius r * (D.fixedPointCount (m / r) : ℤ)

/-- `lemma:weil-divisors-antidiagonal-reindex`.  Reindexing the divisors
antidiagonal; the hypothesis `0 < n` is not needed by the underlying library
theorem but is retained from the text. -/
theorem _root_.Weil.sum_divisorsAntidiagonal_moebius {n : ℕ} (_hn : 0 < n)
    (g : ℕ → ℤ) :
    ∑ rs ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.moebius rs.1 * g rs.2 =
      ∑ r ∈ n.divisors, ArithmeticFunction.moebius r * g (n / r) :=
  Nat.sum_divisorsAntidiagonal fun r s => ArithmeticFunction.moebius r * g s

/-- `lemma:weil-orbit-count-mobius-numerator-eq`.  The Möbius numerator
equals degree times orbit count: `M_m(D) = m · a_m(D)` in `ℤ`. -/
theorem mobiusNumerator_eq (D : FiniteOrbitFrobeniusData) {m : ℕ}
    (hm : 1 ≤ m) :
    D.mobiusNumerator m = (m : ℤ) * (D.orbitCount m : ℤ) := by
  have hsum : ∀ n : ℕ, 0 < n →
      ∑ i ∈ n.divisors, ((i : ℤ) * (D.orbitCount i : ℤ)) =
        (D.fixedPointCount n : ℤ) := by
    intro n hn
    have h := congrArg (fun k : ℕ => (k : ℤ)) (D.fixedPointCount_eq_divisorSum hn)
    push_cast at h
    exact h.symm
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
    (f := fun i => (i : ℤ) * (D.orbitCount i : ℤ))
    (g := fun n => (D.fixedPointCount n : ℤ))).mp hsum m hm
  simp only [Int.cast_id] at key
  have hre := Weil.sum_divisorsAntidiagonal_moebius (n := m) hm
    fun s => (D.fixedPointCount s : ℤ)
  show ∑ r ∈ m.divisors,
    ArithmeticFunction.moebius r * (D.fixedPointCount (m / r) : ℤ) = _
  exact hre.symm.trans key

/-- `cor:weil-orbit-count-mobius-recovery`.  Möbius recovery of orbit counts
in `ℚ`. -/
theorem orbitCount_eq_mobius (D : FiniteOrbitFrobeniusData) {m : ℕ}
    (hm : 1 ≤ m) :
    (D.orbitCount m : ℚ) =
      1 / (m : ℚ) *
        ∑ r ∈ m.divisors,
          (ArithmeticFunction.moebius r : ℚ) *
            (D.fixedPointCount (m / r) : ℚ) := by
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h := congrArg (fun z : ℤ => (z : ℚ)) (D.mobiusNumerator_eq hm)
  simp only [mobiusNumerator] at h
  push_cast at h
  rw [h, one_div, inv_mul_cancel_left₀ hm0]

/-- `cor:weil-orbit-count-mobius-integrality`.  Divisibility and
nonnegativity of the Möbius recovery: `m ∣ M_m(D)` in `ℤ`, with quotient the
nonnegative integer `a_m(D)`. -/
theorem mobius_divisible_nonnegative (D : FiniteOrbitFrobeniusData) {m : ℕ}
    (hm : 1 ≤ m) :
    (m : ℤ) ∣ D.mobiusNumerator m ∧
      D.mobiusNumerator m / (m : ℤ) = (D.orbitCount m : ℤ) ∧
        (0 : ℤ) ≤ (D.orbitCount m : ℤ) := by
  have hm0 : (m : ℤ) ≠ 0 := by
    have : m ≠ 0 := by omega
    exact_mod_cast this
  refine ⟨⟨(D.orbitCount m : ℤ), D.mobiusNumerator_eq hm⟩, ?_,
    Int.natCast_nonneg _⟩
  rw [D.mobiusNumerator_eq hm, Int.mul_ediv_cancel_left _ hm0]

end FiniteOrbitFrobeniusData

end

end Weil
