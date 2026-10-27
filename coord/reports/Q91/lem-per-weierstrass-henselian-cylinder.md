## Worker report

The module `Sheaf.RingTheory.WeierstrassHenselianCylinder` states
`RingTheory.exists_weierstrass_henselian_cylinder` with a single `sorry` proof.
No definitions or additional nodes are needed. The existing node is changed only in `lean`.
Its earlier module was deleted as dead code (`lean_removed`); searches of the present
library found no surviving declaration, so this delivery supplies the statement again.

Source read: ILO, Travaux de Gabber, Exposé V, printed pp. 63–65, Theorem 1.1.1(i),(ii),
Lemma 1.1.3 and its proof, Lemma 1.2.3, and proof 2.2.3. The PDF was read through
`pdftotext -layout`. The first gives triangular changes and preparation, 1.1.3 identifies
the principal-ideal completion, 1.2.3 gives the henselian pair, and 2.2.3 explicitly says
the horizontal maps are completions for both the principal and maximal-ideal topologies.
No source or node correction is made.

Clause-by-clause correspondence (write D = `MvPowerSeries (Fin s) Λ` and R = `PowerSeries D`
in this report only; the Lean signature writes the actual types):

- Complete Noetherian local domain Λ: `(Λ : Type u) [CommRing Λ] [IsDomain Λ]
  [IsNoetherianRing Λ] [IsLocalRing Λ]
  [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ]`.
- r ≥ 1: `(s : ℕ)` is s = r−1, so r = s+1. The node itself identifies the original
  multivariate ring with D[[T]]. Mathlib's `MvPowerSeries.finSuccEquiv Λ s` gives
  this regrouping, after naming its distinguished coordinate T. That equivalence
  singles out index zero rather than the last index; a permutation of variable names
  exchanges the conventions. No coordinate or ring is dropped.
- f in the maximal ideal: `(f : PowerSeries D)` and hypothesis `hf`.
- Nonzero reduction modulo m_Λ R: `hred : f ∉ Ideal.map (algebraMap Λ R)
  (IsLocalRing.maximalIdeal Λ)`. This is exactly quotient nonvanishing, without
  replacing it by a stronger coefficient hypothesis.
- Continuous Λ[[T]]-algebra automorphism: `c : R ≃ₐ[PowerSeries Λ] R` and the explicit
  `@Continuous` clause with both topologies equal to `(maximalIdeal R).adicTopology`.
  `PowerSeries.algebraPowerSeries` makes the base map coefficientwise Λ→D, so this
  fixes every series in T with coefficients in Λ, not just constants.
- Positive exponents and triangular shape: `N : Fin s → ℕ`, `∀ i, 0 < N i`, and
  `c (PowerSeries.C (MvPowerSeries.X i)) = PowerSeries.C (MvPowerSeries.X i) +
  PowerSeries.X ^ N i`.
- Identity when r=1: `s = 0 → c = AlgEquiv.refl` inside the same existential.
- Unit factorization: `unit : Rˣ`, `g : Polynomial D`, and `c f = ↑unit * (g : R)`.
- g = T^n + sum_{i<n} b_i T^i, n>0, b_i in m_D: `g.Monic`, `0 < g.natDegree`,
  and `∀ i, i < g.natDegree → g.coeff i ∈ maximalIdeal D`. A polynomial is finite
  and monicity gives exactly the leading coefficient 1. Here n is `g.natDegree`.
- R₀ = D[T] and q = (m_D,T): the type `Polynomial D` and ideal
  `Ideal.comap Polynomial.constantCoeff (IsLocalRing.maximalIdeal D)`. A polynomial
  belongs to this comap exactly when its constant coefficient is in m_D, which
  is precisely membership in (m_D,T). Its prime instance is inherited by comap.
- H = (R₀)_q^h: for every `(H : Type v) [CommRing H]` with the specified localized
  algebra structure and `[HenselianLocalRing H]`, assume the recorded
  `Algebra.IsHenselizationAtPrime' (Polynomial D) q H`. This is the existing
  universal-property encoding of the specified henselization, not an extra
  restriction on the mathematical ring. It avoids choosing an arbitrary model.
- H Noetherian local henselian: `IsNoetherianRing H` in the conclusion, with local
  henselian structure already part of the recorded henselization interface.
- Residue field D/m_D: the existential ring equivalence to `IsLocalRing.ResidueField H`.
  Its displayed equality on every x:D requires compatibility with the canonical
  map D→D[T]→(D[T])_q→H→κ(H); this is the specified residue-field identification.
- Henselian pair (H,gH): `HenselianRing H (Ideal.span {a(g)})`, with `a` written
  explicitly as the composite polynomial→localization→H. This uses the recorded
  root-lifting predicate, equivalent to the node's idempotent formulation.
- Canonical map H→R: `∃ φ : H →+* R, IsLocalHom φ ∧ ...`, with the next clause
  requiring `φ (a p) = (p : R)` for every polynomial p. Thus φ extends the actual
  inclusion of D[T]; it is not a free map used in place of the canonical map.
  The henselization universal property makes this local extension unique.
- Faithfully flat: `φ.FaithfullyFlat`, the recorded ring-map notion.
- Both completions: ring equivalences `AdicCompletion (maximalIdeal H) H ≃+* R`
  and `AdicCompletion (Ideal.span {a g}) H ≃+* R`. Each equivalence is required
  to send `AdicCompletion.of ... H x` to `φ x` for every x:H. Therefore the same
  map φ is the completion map in both assertions; abstract ring isomorphisms alone
  would not suffice. No assertion equating the two ideal topologies is made.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`, `AdicCompletion`,
  `AdicCompletion.of`; the ring structure comes from `AdicCompletion.Algebra`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`; `Equiv` supplies
  `finSuccEquiv` and the Noetherian instance. `MvPowerSeries.Inverse` and
  `PowerSeries.Inverse` supply the local-ring structures.
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`; its canonical embedding in R
  comes from `Mathlib.RingTheory.PowerSeries.Basic`.
- `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`:
  `Algebra.IsHenselizationAtPrime'`, including its entire local-map universal property
  with independent ring universes u,v and test objects in their common universe.
- `WeilConjectures.Mathlib.RingTheory.Henselian` exposes Mathlib's `HenselianRing`
  and `HenselianLocalRing` (the strict variant from that node is not needed).
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`;
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`.

The already stated proof dependencies are imported as plain proof imports. The one
unstated proof dependency, `lem-per-local-pair-henselization-comparison`, has no module
to import; its use is retained explicitly in the ten-step proof docstring. The
Mathlib leaves use their actual recorded modules, notably `WeierstrassPreparation`
for both preparation and the distinguished quotient isomorphism. No proof dependency
is assumed as a hypothesis of the theorem.

Edge cases checked before and after writing:

- s=0 (r=1): D is the zero-variable power series ring canonically equal to Λ; the
  two clauses quantified over `Fin 0` are empty and the identity requirement remains.
- Λ a field: its maximal ideal is zero, so hred is just nonvanishing; arbitrary
  characteristic is retained. No infinitude or characteristic-zero assumption appears.
- f=0 is excluded by hred; f a unit is excluded by hf. Thus n=0 cannot accidentally
  satisfy the conclusion; positivity is explicit and rules out g=1.
- A pure nonzero element of the base maximal ideal fails hred, as required.
- q is proper and maximal since constant coefficient is surjective onto local D;
  the comap construction supplies its prime instance without an assumed new prime.
- H is nonzero because it is henselian local. The proof's finite-algebra argument
  includes the zero algebra as the empty product, without a nonzero-algebra hypothesis.
- Independent u,v are retained for Λ and H; there is no forced universe equality.
- Completion equivalences have canonical-map compatibility, so neither completion
  assertion is silently replaced by abstract isomorphism of the underlying rings.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Weierstrass coordinate change and henselization polynomial
  cylinder completion"`: eight hits, mostly elliptic-curve changes and single-variable
  Weierstrass division; no combined cylinder statement.
- `msearch.py ... loogle "PowerSeries, AlgEquiv"`: twelve hits, including
  `MvPowerSeries.finSuccEquiv` and its coefficient/variable formulas; these provide
  the regrouping, not the theorem.
- `msearch.py ... grep "henselian_cylinder|finSuccEquiv|algebraPowerSeries" RingTheory`:
  twenty-five hits, including the existing regrouping; no cylinder theorem.
- `msearch.py ... leansearch "henselization distinguished polynomial completion power
  series coordinate change"`: eight hits including `PowerSeries.weierstrassDistinguished`
  and `Polynomial.IsDistinguishedAt.algEquivQuotient`, not the full assertion.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `weierstrass_henselian_cylinder|WeierstrassHenselianCylinder|henselian cylinder`:
  no surviving declaration. `grep -rn` for the exact blueprint id in
  `lean/WeilConjectures`: no hit. Searches for `IsHenselizationAtPrime` located the
  recorded generalized interface, which is reused.
- Direct Mathlib searches for `algebraPowerSeries`, `finSuccEquiv`, local power series,
  `IsAdicComplete`, `AdicCompletion`, and faithful flatness located the definitions
  listed above. Full signatures and docstrings of every statement dependency were read.

Validation: `scompile.py Q91 lem-per-weierstrass-henselian-cylinder
<module path>` compiled the sandbox and library forms cleanly (1.8 s and 1.7 s).
All variables and universes are explicit, both auto-implicit options are disabled,
and every source line is at most 100 characters. No statement dispute or node fault.

## Second reading by Q91

No independent second worker was started: this was a single-worker dispatcher task
with explicit instructions not to start agents. The clause comparison above is the
worker's own audit; the maintainer performs the independent delivery review.
