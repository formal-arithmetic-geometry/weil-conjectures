## Worker report

The module `Sheaf.RingTheory.SupportedCoordinateCoverUnitsPrimes` states
`ToricMonoid.supportedCoordinateCover_units_primes`, with one `sorry` and no new
definitions. Its docstring gives all seven proof steps of the accepted split.
The accepted natural-language statement, proof, and proof dependencies are unchanged.

This is a stage-2 statement assignment. The live node is stage-1 split, reviewed PASS
for Q98 on 2026-10-23, has no `lean` record, and appears at stage 2 in coord/queue.tsv.
The maintenance handoff in coord/brief-stage2.md §0 explicitly says an old stage-1
unchanged-item BLOCKED report does not block stage 2. This delivery preserves that
accepted split; it does not resplit it. There is no released repair note for the item.

Hypotheses, clause by clause:

- `P : Type u`, `[AddCommMonoid P]` and `hfs` use the recorded
  `AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative P)` to impose finite
  generation, integrality, and saturation. `hsharp` states that a sum equaling zero
  has both summands zero, exactly the additive sharpness condition.
- `Lattice P` and `latticePoint` are the published canonical group completion and
  its canonical map. `r n : ℕ` include zero. `lam` is the group homomorphism into
  `Fin r → ℤ`, and `hlam` asserts injectivity. `horthant` states that the nonnegative
  elements of its image are exactly the images of P, i.e. the stipulated
  equality lam(P) = lam(G) ∩ ℕ^r. It does not assume primitivity of the lattice image.
- `L : Type v`, `[CommRing L]`, `[IsLocalRing L]` give the local coefficient ring.
  `Complete L P n` is exactly B_L(P,n), using the published adic completion of
  `MvPolynomial (Fin n) (AddMonoidAlgebra L P)` at the specified ideal. This is
  real completion data, not an abstract ring carrying unspecified chart elements.
- The ambient series ring is `MvPowerSeries (Fin r ⊕ Fin n) L`, with the two
  explicitly labeled blocks X and t. The disjoint sum has r+n variables and
  gives the same ring as the notation in the statement, including empty blocks.
- `ι` is an L-algebra homomorphism and `hι` asserts injectivity. `hsupport` says
  its image consists exactly of those series whose coefficients outside
  `(lam(G) ∩ ℕ^r) × ℕ^n` vanish. `hmonomial` gives the coefficient formula for
  z^q ↦ X^{lam(q)}, including zero exponents in the t block. `hvariable` specifies
  that each completed polynomial variable t_j maps to the second-block variable.
  Constants are fixed because ι is an L-algebra homomorphism. These express the
  specified supported identification, not an arbitrary inclusion.
- `ρ` is additive, and `hρ` says coefficientwise that ι(ρ(f)) keeps exactly the
  allowed coefficients and deletes all others. Injectivity of ι makes this the
  stated deletion map read through its inverse on the supported image.
- `qB` and `qA` present R and D, with `hqB` and `hqA` asserting surjectivity.
  `hcase` has precisely two alternatives: IsField L with both kernels zero, or
  IsCohenRing p L with theta-p in the published completed chart ideal and kernels
  `(theta)` and `(ι theta)`. A surjective ring homomorphism with zero kernel is
  an isomorphism; a surjection with the given kernel presents exactly that
  principal quotient by the first isomorphism theorem. Thus in the field case
  these are B and A, and in the Cohen case they are B/(theta) and A/(Theta).
  The presentations merely allow isomorphic realizations of the exact rings;
  the node's literal rings are obtained by taking identities or quotient maps.
  This introduces neither an extra mathematical hypothesis nor an additional
  model case. No arbitrary quotient ideal is allowed.
- `j`, `hj`, `hcommute` are the induced inclusion R ↪ D and its formula on
  representatives. `ρbar`, `hdescend` give the descended deletion map with its
  representative formula. `hretract` and `hlinear` assert precisely the given
  R-linear retraction, expressing scalar multiplication through j as multiplication.
  Additive maps are used for the retractions: multiplicativity is not assumed.

Conclusions, clause by clause:

- Three existential `IsLocalRing` instances assert locality of B, R, and D.
- `resB`, `resR`, and `resD` are ring homomorphisms to the fixed common field
  `IsLocalRing.ResidueField L`, which is L modulo its maximal ideal. The formula
  for resB is residue after constant coefficient after ι; `resR.comp qB = resB`
  and the formula for `resD (qA f)` specify the induced quotient residue maps
  on every representative. Surjectivity and kernel equal to each maximal ideal
  say exactly that this field is each ring's residue field; the first isomorphism
  theorem identifies each maximal-ideal quotient with it.
- Each `∀ b, IsUnit b ↔ resB b ≠ 0` (and resR/resD variants) is the corresponding
  residue unit criterion. `resR (ρbar b) = resD b` is residue preservation, and
  `IsUnit b → IsUnit (ρbar b)` is preservation of every unit.
- `IsNoetherianRing D ∧ IsDomain D ∧ IsIntegrallyClosed D` says D is a
  Noetherian normal domain, using the node's recorded definitions.
- For every i in Fin r, `Prime (qA (MvPowerSeries.X (Sum.inl i)))` means the
  coordinate is nonzero, a nonunit, and divides a factor whenever it divides a
  product. The next clauses assert its principal ideal is prime and nonzero.
  The assertion for every prime I below that principal ideal says I is zero or
  the whole coordinate ideal, exactly the specified absence of intermediate
  prime ideals. Finally injectivity of the family of principal ideals asserts
  pairwise distinctness. Only first-block coordinates have these assertions.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup` exposes
  `AlgebraicGeometry.IsFineSaturatedMonoid` (defined in its public dependency
  `Sheaf.AlgebraicGeometry.LogRegularPair`); its definition was read in full.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion` and its compatible
  inverse-limit sequences, as used by the published completed model.
- `WeilConjectures.RingTheory.CohenRing`: `IsCohenRing`; read its definition,
  including prime p, domain, discrete valuation ring, maximal ideal pC and
  p-adic completeness. No perfection is required.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `coeff`, `constantCoeff`,
  and `X`, with their genuine coefficientwise series construction.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  `IsDomain` is used alongside it as the recorded normal-domain encoding.
- Added the existing landed definition node `def-trf-complete-toric-model` to
  stmt_deps to cite the reused `Sheaf.RingTheory.CompleteToricModel` interface:
  `ToricMonoid.Complete`, `PolynomialRing`, `monomial`, `completedChartIdeal`,
  `Lattice`, and `latticePoint`. Their full definitions and docstrings were read.
  That module reuses `AddMonoidAlgebra.CompletedLocalModel`,
  `localModelCompletionIdeal`, `localModelBoundaryIdeal`, and
  `completedLocalModelBoundaryIdeal` from LogRegularSaturationNormality; these
  definitions were also read. No private copy of any of these notions is made.
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic`: the canonical `ResidueField`
  and `residue` construction, read in its Defs public dependency.

Proof imports are `WeilConjectures.RingTheory.PowerSeriesQuotientVariables`
(`MvPowerSeries.quotient_first_variables`),
`Mathlib.RingTheory.MvPowerSeries.Inverse` (the unit criterion and local instance),
and `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`
(`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`). The proof dependency
`lem-trf-power-series-cohen-hypersurface-normality` currently has no Lean module,
so it cannot yet be imported; its future import belongs to the maintainer's
proof-dependency backfill. It is not needed to type this statement.

Source and edge checks:

Read ILO Exposé VI 1.4 and 1.6(i)--(ii) directly using pdftotext on PDF pages 75--76,
printed pages 69--70. These give the local model presentations and theta congruence,
not this auxiliary theorem. No unread Kato theorem is attributed as its source.
Checked r=0: the coordinate conjunction is universal over an empty type and the
ideal-family injectivity is vacuous; the lattice condition forces P to be trivial
by hfs and injectivity. Checked n=0 and both blocks empty: coefficient rings in
the field case and C/pC in the Cohen case, with no coordinate assertions. Checked
P={0} and r>0: the supported subring is the series ring on the t block while
ambient X coordinates remain valid. Checked theta=p+X_1 and theta=p+X_1X_2 where
these monomials lie in the supported chart: the constant is still p and the
coordinate-primality assertions remain valid; no assumption that theta has no
linear terms was imposed. Nonperfect residue fields are allowed. All ring and
monoid universes u,v,w,x are explicit and independent. No auto-bound variables.
No STATEMENT-DISPUTED issue or statement correction is needed.

Searches:

- msearch.py leanfinder, "supported complete monoid power series ring retraction
  units residue field coordinate prime ideals": 8 hits, including
  PowerSeries.residueFieldOfPowerSeries and Weierstrass unit constructions;
  none states the supported multivariate/Cohen quotient result.
- msearch.py loogle, "MvPowerSeries.isUnit_iff_constantCoeff,
  IsLocalRing.residue_ne_zero_iff_isUnit": 0 hits.
- msearch.py grep, "supported.*[Uu]nit|coordinate.*[Pp]rime|prime_X" in
  RingTheory/MvPowerSeries: 0 hits.
- msearch.py leansearch, "Residue units and prime coordinates of a supported
  complete toric cover": 8 hits, including IsLocalRing.residue_ne_zero_iff_isUnit,
  residue and valuation-subring residue lemmas. These presuppose locality or
  handle only a proper part of the statement, so are not existing matches.
- rg searches for supported/Toric/toric in lean/Sheaf/RingTheory and relevant
  fs files found CompleteToricModel, CompleteToricLocalModel,
  CompletedMonoidSupportProjection and LogRegularSaturationNormality. All were
  read; none states this lemma. The former supplies the reused model notation.
- rg over lean/WeilConjectures and lean/Sheaf for supported-coordinate names,
  coordinate prime and supported residue found no exact existing statement.
  The exact node-id and proposed declaration-name searches found no existing
  upstream match. Existing hypotheses and definitions are reused as above.

Validation: the prescribed scompile.py server wrapper compiled both its sandbox
probe and the real library module cleanly (2.1 and 2.0 seconds). An initial parser
error from using reserved lambda as a binder name was fixed by naming it `lam`.
There are no diagnostic commands or proved lemmas in the module. Delivery preflight
and its separate compile are run below through deliver2.py.

## Second reading by Q82

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
