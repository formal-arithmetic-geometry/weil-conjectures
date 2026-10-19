## Worker report

I stated `lem-trf-nearby-cycle-sheaf-finiteness` in
`Sheaf.Paper.NearbyCycleSheafFiniteness`.  The module defines the canonical
pullback projection `AlgebraicGeometry.nearbyCycleProjection` from the geometric
generic fibre to the generic fibre, then states (with `sorry`) the theorem
`AlgebraicGeometry.nearbyCycleSheafFiniteness`.  The projection is constructed by
`Limits.pullback.map`; its compatibility square is discharged by the scalar-tower
identity, so it has real data and is not a choice or an arbitrary map.

The theorem renders the node clause by clause as follows.  `R` has
`CommRing`, `IsNoetherianRing`, `IsDomain`, and
`IsStrictlyHenselianLocalRing` instances, and the explicit hypotheses
`ringKrullDim R = 1`, principal maximal ideal, and nonzero maximal ideal give the
strictly henselian DVR description.  `X` and `f : X ⟶ Spec (.of R)` are the
scheme and its structure morphism; the `IsSeparated`, `LocallyOfFiniteType`, and
`QuasiCompact` typeclasses are the node's separated finite-type hypothesis.
`ell`, `Fact ell.Prime`, and `Invertible (ell : R)` render an invertible prime;
`n`, `1 ≤ n`, the finite commutative ring `Λ`, and
`hΛ : ∀ a, (ell : Λ)^n * a = 0` render finite `ell`-power torsion
coefficients.  `K` with `Field`, `Algebra R K`, and `IsFractionRing R K` is
`Frac(R)`; `Kbar` with `Field`, `Algebra K Kbar`, `Algebra R Kbar`,
`IsSepClosure K Kbar`, and `IsScalarTower R K Kbar` is the chosen separable
closure and its compatible scalar structure.  `F` is a sheaf of
`ModuleCat.{u+1} Λ` on the small etale site of the generic pullback
`pullback f (Spec.map (algebraMap R K))`.

The explicit hypothesis
`hF : Scheme.IsConstructibleEtaleModuleSheaf F` renders the source condition
that `F` is constructible on the generic fibre.  For each integer `q` with
`0 ≤ q`, the first conjunct applies
`Scheme.IsConstructibleEtaleModuleSheaf` to the upper-star (inverse-image)
pullback along the closed-fibre map `pullback.fst f (Spec.map (algebraMap R
(IsLocalRing.ResidueField R)))` of the degree-`q` higher direct image along the
geometric-generic map `pullback.fst f (Spec.map (algebraMap R Kbar))`, applied to
the upper-star pullback of `F` along `nearbyCycleProjection`.  This is exactly
`i^* R^q \bar j_*(\pi^*F)`.  The second conjunct gives one integer `N` and,
for every `q` with `N < q`, the categorical `IsZero` statement for that same
sheaf, rendering eventual vanishing uniformly in `q`.

The recorded dependency declarations used are:

- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`
  (Mathlib.AlgebraicGeometry.Morphisms.FiniteType; `QuasiCompact` is in the
  companion Mathlib module).
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsSeparated` and
  `AlgebraicGeometry.IsProper` from `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `def-weil-pbc-etale-constructible-sheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` from
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
- `prop-weil-pbc-inverse-image-modules-exact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact` from
  `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar` from
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; the corresponding
  higher direct image is `Etale.higherDirectImage` in the imported
  `SmoothBaseChange.Defs`.
- `def-weil-pbc-henselian-terminology`:
  `IsStrictlyHenselianLocalRing` from
  `WeilConjectures.Mathlib.RingTheory.Henselian`.

I searched for an existing nearby-cycle finiteness declaration with the required
three search families.  LeanFinder was queried for “higher direct image nearby
cycles of a constructible finite torsion etale sheaf over a strictly henselian
discrete valuation ring are constructible and eventually zero”; its eight hits
were unrelated limit identities, etale-locus facts, or constructible subsets.
Loogle was queried for `Etale.higherDirectImage, IsConstructibleEtaleModuleSheaf`
and returned no hits (and reported `Etale.higherDirectImage` as unknown to that
service).  Grep over Mathlib/AlgebraicGeometry and the project searched
`nearby.?cycle|higherDirectImage|constructible`; it returned no matching
nearby-cycle finiteness declaration.  The existing node search and blueprint
search likewise found no duplicate node.  These receipts are retained in
`searches.jsonl` and the node's `mathlib_searches`.

Edge cases checked before writing: `X` may be empty; the generic or closed fibre
may be empty; `F` may be the zero sheaf; `q = 0` is included; eventual vanishing
allows any integer bound `N`; and the statement does not require finite Tor
dimension.  The separable-closure binder is not restricted to an algebraically
closed field, and the explicit scalar tower preserves the residue-characteristic
and imperfect-residue-field cases.

No statement correction or dispute was needed.  No new DAG definition node or
dependency repair was needed: all six recorded statement dependencies have the
interfaces used above.  The module compiles cleanly under `scompile.py` with no
errors or warnings.

## Second reading by Q96

I reread the current node JSON and this module after the repair and
compilation.  The strict henselian DVR hypotheses, separated finite-type
morphism, invertible prime, finite torsion coefficient ring, and the generic
fibre sheaf are bound in the theorem signature.  Its explicit
`hF : Scheme.IsConstructibleEtaleModuleSheaf F` hypothesis is the Lean
rendering of the source's constructibility condition; it is now present after
the `F` binder.  The geometric-generic projection, constructibility-for-each-
`q` clause, and one uniform vanishing bound are also rendered by the displayed
types.  The only added constituent is the named canonical `pullback.map`
helper, which supplies the projection object introduced by the source statement
and carries no additional hypothesis.  The theorem proof remains `sorry`, as
required for stage 2.
