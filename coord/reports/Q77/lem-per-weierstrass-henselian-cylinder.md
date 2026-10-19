## Worker report

The module `Sheaf.RingTheory.WeierstrassHenselianCylinder` states
`RingTheory.exists_weierstrass_henselian_cylinder`, with one `sorry` and no definitions.
Only the item's `lean` field changes. There are no new nodes, dependency repairs,
statement corrections, or disputed statements.

Source read directly: Travaux de Gabber, Expose V, Theorem 1.1.1(i),(ii), Lemmas
1.1.3 and 1.2.3, and proof 2.2.3, printed pages 63--66. In particular, 1.1.3
identifies the distinguished-polynomial completion, and the last paragraph of
2.2.3 explicitly specifies both completion topologies. The PDF was extracted
inside this sandbox for reading. All ten proof steps of the node are retained
in the declaration's docstring.

Clause-by-clause translation (write D = MvPowerSeries (Fin s) Λ and R = PowerSeries D
only in this report, not as file-local Lean notation):

- Complete Noetherian local domain Λ: `CommRing Λ`, `IsDomain Λ`,
  `IsNoetherianRing Λ`, `IsLocalRing Λ`, and
  `IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ`.
- r ≥ 1 and the power-series ring: `s : ℕ` represents r = s+1; the function's
  argument is `f : PowerSeries (MvPowerSeries (Fin s) Λ)`. Mathlib's
  `MvPowerSeries.finSuccEquiv Λ s` is the canonical coefficient regrouping.
  Mathlib labels its distinguished variable 0, and its other variables `i.succ`;
  this is just reindexing t_r and t_1,...,t_{r-1}, with no mathematical restriction.
- f in the maximal ideal: `hf : f ∈ IsLocalRing.maximalIdeal R`.
- Nonzero reduction modulo m_Λ R: `hred : f ∉ Ideal.map (algebraMap Λ R)
  (IsLocalRing.maximalIdeal Λ)`. This uses exactly the extended ideal, without
  replacing it by a condition requiring an unstated identification.
- Continuous Λ[[T]]-algebra automorphism: `c : R ≃ₐ[PowerSeries Λ] R` uses
  Mathlib's coefficientwise `PowerSeries.algebraPowerSeries` inclusion. The
  quantified ideal-power condition says that for every target maximal-ideal
  power some source maximal-ideal power maps into it. For an additive ring
  map this is precisely continuity for the maximal-ideal adic topology. No
  default topology on the coefficient type is imposed.
- Positive triangular exponents: `N : Fin s → ℕ`, `∀ i, 0 < N i`, and
  `c (PowerSeries.C (MvPowerSeries.X i)) =
  PowerSeries.C (MvPowerSeries.X i) + PowerSeries.X ^ N i`.
- r=1 identity: `s = 0 → c = AlgEquiv.refl`, as a clause of the same witnesses.
- Unit factorization: `unit : Rˣ`, `g : Polynomial D`, and
  `c f = (unit : R) * (g : PowerSeries D)`.
- Distinguished polynomial of positive degree: `g.Monic`, `0 < g.natDegree`,
  and `∀ i, i < g.natDegree → g.coeff i ∈ IsLocalRing.maximalIdeal D`.
  These express exactly T^n plus the stated lower coefficients, with n=g.natDegree.
- R_0=D[T], q=(m_D,T): q is an ideal of `Polynomial D` satisfying
  `q = Ideal.comap Polynomial.constantCoeff (IsLocalRing.maximalIdeal D)`.
  Evaluation at zero has kernel (T), so this is exactly the specified ideal.
  Its prime-ideal proof is supplied existentially, rather than assumed.
- H is the henselization: the clause is universal in any representative
  `(H : Type v) [CommRing H] [HenselianLocalRing H]`
  `[Algebra (Localization.AtPrime q) H]` satisfying the dependency's exact
  `Algebra.IsHenselizationAtPrime' (Polynomial D) q H`. The henselian local
  structure is part of that recorded definition, not an extra assumption on
  the base ring. This standard arbitrary-representative formulation covers
  the H named by the node; no existence construction is chosen using `sorry`.
- Noetherian local henselian: locality and henselianity are carried by the
  henselization representative's structure, and `IsNoetherianRing H` is asserted.
- Residue field D/m_D: an explicit ring equivalence to
  `IsLocalRing.ResidueField H`, commuting with the residue maps from D. This
  also specifies the canonical identification, rather than merely asserting
  an unrelated field isomorphism.
- The map a from D[T] to H equals the composite of the localization map and
  henselization algebra map. The principal ideal is `Ideal.span {a g}` = gH.
- Henselian pair: `HenselianRing H (Ideal.span {a g})`, the dependency's
  existing Mathlib notion, equivalent to its idempotent formulation.
- Canonical H→R: `φ : H →+* R`, `IsLocalHom φ`, and
  `φ.comp a = Polynomial.coeToPowerSeries.ringHom`. The localization
  property extends this compatibility to the local polynomial ring, and
  the supplied henselization universal property makes the local map unique.
  Thus this existential map is fully constrained to be the canonical map.
- Faithful flatness: `φ.FaithfullyFlat`, exactly `RingHom.FaithfullyFlat`.
- g-adic completion: a ring equivalence `AdicCompletion (Ideal.span {a g}) H ≃+* R`
  whose composite with the completion structure map equals the same φ.
- Maximal-ideal completion: likewise
  `AdicCompletion (IsLocalRing.maximalIdeal H) H ≃+* R`, again commuting with φ.
  Both are the actual inverse-limit completion objects in the dependency,
  with their canonical algebra maps, not completeness of an unrelated algebra.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `IsAdicComplete`,
  `AdicCompletion`, its ring and algebra structures and canonical map.
- `Mathlib.RingTheory.MvPowerSeries.Basic`, `.Equiv`, `.Inverse`:
  `MvPowerSeries`, `MvPowerSeries.finSuccEquiv`, `MvPowerSeries.isEmptyEquiv`,
  and the existing local-ring and Noetherian instances.
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`; the existing coefficients,
  monicity and degree API describe the distinguished polynomial without a new notion.
- `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`:
  `Algebra.IsHenselizationAtPrime'`, including its entire local-map universal
  property and common-universe test rings. It imports the upstream henselian module.
- `WeilConjectures.Mathlib.RingTheory.Henselian` and Mathlib's
  `RingTheory.Henselian`: `HenselianLocalRing`, `HenselianRing`. The node's
  `IsStrictlyHenselianLocalRing` is the third notion of that dependency and is
  not needed for this statement.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` and
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `Module.FaithfullyFlat` and
  its ring-map formulation `RingHom.FaithfullyFlat`.

Every already recorded proof-dependency module is imported. Mathlib matches
supply the preparation and polynomial-quotient lemmas, finite-type and
localization Noetherianity, local completion faithful flatness, and power-series
locality/Noetherianity. The local-pair henselization comparison proof dependency
has neither a Lean record nor a Mathlib match, so there is no module to import;
it is a future proof input, not a missing notion in this statement. The existing
pair-henselization modules and quotient-at-prime module are imported as the
node's proof plan, without copying or changing their interfaces.

Edge cases checked: s=0 (r=1) has an empty exponent family and retains the
explicit identity conclusion; D is canonically Λ by `isEmptyEquiv`. No empty
variable case is excluded. Degree zero is explicitly excluded, as required
by f being a nonunit. f=0 does not satisfy hred. The zero coefficient ring
is excluded by the node's domain assumption. A field coefficient ring has
maximal ideal zero and is included. No characteristic restriction occurs.
Completion uses all powers including power zero. H may be in an independent
universe v, and its recorded henselization predicate tests in max u v, so
no small test-ring universe restriction has been introduced.

Searches made on 2026-10-19:

- `msearch.py ... leanfinder "Weierstrass coordinate change formal power series
  henselization distinguished polynomial adic completion"`: eight hits, led by
  `PowerSeries.weierstrassDistinguished`,
  `PowerSeries.algEquivQuotientWeierstrassDistinguished`, and
  `PowerSeries.exists_isWeierstrassFactorization`; none states the combined result.
- `msearch.py ... loogle "MvPowerSeries.finSuccEquiv,
  PowerSeries.exists_isWeierstrassFactorization"`: zero hits for the combined query;
  the declarations themselves were read directly in Mathlib.
- `msearch.py ... grep "henseli.*complet|weierstrass|finSuccEquiv"
  RingTheory/PowerSeries`: five hits in WeierstrassPreparation, no cylinder result.
- `msearch.py ... leansearch "A continuous coordinate change of a multivariate
  power series gives a distinguished polynomial whose henselization has power
  series ring as adic completion"`: eight hits, mainly continuous substitution
  and evaluation, plus `IsAdicComplete.henselianRing`; no combined result.
- `rg` for `finSucc|weierstrass|HenselianCylinder|henselianCylinder|henselian_cylinder`
  in `lean/Sheaf` and upstream `WeilConjectures`: unrelated finite-variable
  equivalences and no cylinder statement. The node id search upstream returned none.
- `rg` for `exists_weierstrass_henselian_cylinder|weierstrass.*hensel|hensel.*cylinder`
  in `dag/lean_names_upstream.json`, Mathlib, upstream and `lean/Sheaf`: no hits.

Validation: prescribed `scompile.py Q77 lem-per-weierstrass-henselian-cylinder`
compiled the file as both the sandbox module and its library module with no
errors or warnings (2.5 s and 2.3 s respectively). No global build was run.

## Second reading by Q77

This dispatcher assigned one worker and explicitly prohibited spawning other
agents. The maintainer provides the independent reading after delivery. This
section records the worker's separate final clause audit, not a claim that a
second independent agent has reviewed it.

Reopened the node and complete Lean signature after compilation. The hypotheses
match complete Noetherian local domain, arbitrary r≥1, maximal-ideal membership
and nonzero reduction. The regrouped representation has all r variables and fixes
the correct Λ[[T]] subalgebra. The existential witnesses include the positive
triangular exponents, continuity, identity for r=1, a unit, and the monic
positive-degree polynomial with all lower coefficients in m_D. The q formula
matches (m_D,T). The henselization uses the recorded universal property; no
arbitrary algebra replaces it. Its residue identification commutes with the
coefficient map. Both completion equivalences extend the same local canonical
map, and that map is faithfully flat. The henselian-pair ideal uses the actual
g image under the polynomial structural map. No missing clause or added
mathematical hypothesis was found; no statement change was made.
