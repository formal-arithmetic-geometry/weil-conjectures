## Worker report

The module `Sheaf.RingTheory.GabberAdicQuasiExcellence` states
`isQuasiExcellent_of_quotient_of_isAdicComplete`, with its proof `sorry`.
It is Gabber's unrestricted-characteristic lifting theorem, not the existing
rational-algebra complete-pair equivalence. No definitions, new nodes or
dependency repairs are needed. Only the item's `lean` field changes.

### Source and exact statement correspondence

I read the local PDF of Illusie--Laszlo--Orgogozo, Travaux de Gabber,
Exposé I, Théorème 9.2, printed p.17 (PDF p.23), using `pdftotext`.
It states that an I-adically complete Noetherian ring A is quasi-excellent
if A/I is quasi-excellent. The following paragraph explicitly distinguishes
excellence from quasi-excellence; it gives no characteristic restriction.
The node and Lean both retain exactly quasi-excellence.

Each hypothesis and conclusion is represented as follows:

- A commutative ring R: `(R : Type u) [CommRing R]`. The universe `u` is
  explicitly declared; R may be any size and need not be nontrivial or a domain.
- Noetherian: `[IsNoetherianRing R]`, exactly the recorded dependency predicate.
- An arbitrary ideal J of R: `(J : Ideal R)`; no properness, principality or
  finite-generation assumption is separately imposed.
- The canonical map to the J-adic inverse limit is an isomorphism:
  `[IsAdicComplete J R]`. The recorded dependency explicitly includes this
  predicate. In `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion.of_bijective_iff` identifies it with
  `Function.Bijective (AdicCompletion.of J R)`. I read the construction of
  `AdicCompletion` and `AdicCompletion.of`: they are compatible quotient
  sequences and the canonical map sending an element to all its residues.
  For M = R, the submodules J^n times the whole ring are precisely J^n.
  Mathlib includes n = 0; that quotient is the zero ring and adds no data or
  constraint to the inverse limit indexed by n >= 1. The canonical map is
  multiplicative for the usual componentwise ring structure, so bijectivity
  says exactly that this canonical ring map is an isomorphism. This is not
  an arbitrary isomorphism between the two rings.
- R/J quasi-excellent: `(hquot : IsQuasiExcellent (R ⧸ J))`.
- R quasi-excellent: conclusion `IsQuasiExcellent R`, using the same predicate.
- No assumptions on characteristic, universal catenarity or dimension: the
  signature has no rational algebra, characteristic, catenarity or dimension
  binders. It does not use `IsExcellent` in place of `IsQuasiExcellent`.

### Dependency declarations used

I read the recorded definitions and their docstrings/signatures:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`; the abbreviation is Noetherianity as a
  module over itself, equivalently every ideal finitely generated.
- `def-weil-pbc-adic-completion`: `AdicCompletion` and `IsAdicComplete`,
  `Mathlib.RingTheory.AdicCompletion.Basic`, including the canonical map
  `AdicCompletion.of` and `AdicCompletion.of_bijective_iff` just discussed.
- `def-exc-excellent-ring`: `IsQuasiExcellent`,
  `Sheaf.RingTheory.ExcellentRing`. Although the main recorded declaration is
  `IsExcellent`, its `declarations` includes `IsQuasiExcellent`; this definition
  is Noetherian plus G-ring plus open regular locus in every finite type algebra.
  It is usable directly and is not duplicated here.

The already stated proof dependencies are imported without `public`:
`Mathlib.AlgebraicGeometry.Morphisms.Flat` (flatness, base change, the affine
criterion, flatness over fields), `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
`Mathlib.AlgebraicGeometry.PullbackCarrier` (surjectivity under base change),
`Mathlib.RingTheory.FiniteType` (Noetherian finite type algebras),
`Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian` (finite minimal primes),
`Mathlib.RingTheory.Localization.Submodule` (Noetherian localization),
`Mathlib.Topology.Inseparable` (`IsClosedMap.specializingMap`), and the upstream
modules `WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber`,
`WeilConjectures.RingTheory.FlatUnderRegular`, and
`WeilConjectures.RingTheory.RegularLocalLocalization` for the recorded
regular-local ascent, descent and localization theorems.

Five proof dependencies currently have no recorded Lean module:
`lem-per-gabber-normal-counterexample-reduction`,
`lem-per-gabber-minimal-formal-defect`,
`lem-per-gabber-semilocal-defect-height`,
`lem-per-qe-alteration-regular-neighbourhood`, and
`lem-per-qe-rotthaus-finite-boundary`.
They are not needed to type the statement and therefore need no speculative
imports or dependency modules in this delivery. Their role is spelled out
in the nine-step proof docstring, which follows every step of the node.
There are no omitted imports caused by an import cycle.

The node's detailed proof cites Kurano--Shimomoto, Ideal-adic completion of
quasi-excellent rings (after Gabber), Theorem 5.1, Steps 1--3,
https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf.
Its local bibliographic copy remains WANTED as recorded by the existing node.
The proof docstring preserves the normalized boundary, height argument,
closed-fibre residue-field identification and generic-fibre flatness of that
node; this delivery postpones the proof rather than claiming to verify it in Lean.

### Edge cases checked before writing

- J = 0: every ring is 0-adically complete; R/0 is canonically R, so the
  theorem reduces to the given quasi-excellence hypothesis.
- J = R: completeness forces R to be the zero ring, since the inverse limit
  is zero (also `IsHausdorff.subsingleton` for the unit ideal). No improper-ideal
  case is excluded by adding a properness condition.
- The zero ring is allowed by `[CommRing R]`; its spectrum and the spectra of
  its unital algebras are empty, consistent with the quasi-excellent predicate.
- Positive characteristic and mixed characteristic rings remain in scope:
  there is no `[Algebra ℚ R]` or characteristic restriction.
- Neither finite dimension, being local, being a domain, nor universal
  catenarity is required. The single universe is the arbitrary ring universe;
  no smaller independent universe makes the J-2 quantification vacuous.

### Searches for an existing declaration

All remote searches used the prescribed `msearch.py` wrapper for Q81 and this item:

- LeanFinder query: `A Noetherian ring complete for an ideal whose quotient is
  quasi excellent is quasi excellent`. Eight hits, including
  `AdicCompletion.flat_of_isNoetherian`, `IsHausdorff.of_isDomain` and
  `Ideal.Quotient.isNoetherianRing`; none states quasi-excellence lifting.
- Loogle query: `IsQuasiExcellent, IsAdicComplete, AdicCompletion`.
  Zero hits; the service reports unknown identifier `IsQuasiExcellent`.
- Mathlib grep query: `IsQuasiExcellent|quasi.excellent|Gabber.*completion`,
  restricted to `RingTheory`: zero hits.
- Project searches used `rg -n` over `lean/WeilConjectures` and `lean/Sheaf`
  for quasi-excellence and adic lifting, and `grep -rn` over
  `lean/WeilConjectures` for `lem-per-gabber-adic-quasi-excellence`.
  The identifier search found no upstream declaration. Focused searches also
  covered both RingTheory directories and `dag/lean_names_upstream.json`.
- The project definition `IsQuasiExcellent` was found and reused. The closest
  theorem is `isQuasiExcellent_iff_quotient_of_isAdicComplete` in
  `Sheaf.RingTheory.QuasiExcellentCompletePair`, belonging to
  `lem-per-qe-complete-pair-lifting`. I read its whole declaration: it requires
  `[Algebra ℚ A]`, so it cannot supply this node's arbitrary-characteristic
  statement. The formal-affine theorem in
  `Sheaf.AlgebraicGeometry.QuasiExcellentFormalAffines` uses the current node
  in its proof docstring and does not already state the lifting theorem.
- No collision was found for `isQuasiExcellent_of_quotient_of_isAdicComplete`.

No statement dispute or source-based correction is required.

### Validation

The prescribed `scompile.py` command compiled this module both in its private
sandbox and at its intended library module path against the live published
build. Both passed in approximately 1.5 seconds with no errors or warnings.
The delivered theorem has only `sorry` as its proof. All variables and universes
are explicitly bound, and all Lean lines are at most 100 characters.

## Second reading by Q81

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
