## Worker report

The module `Sheaf.RingTheory.QuasiExcellentOfClosedFibre` states
`isQuasiExcellent_of_quotient_of_isGRing`, with `sorry` as its entire proof. It defines
no new notions. The node is unchanged except for its `lean` record.

Source read: Kurano--Shimomoto, *Ideal-adic completion of quasi-excellent rings
(after Gabber)*, https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf,
Theorem 4.1 on printed p.4 and its proof on printed pp.6--7. The source assumes
commutative unital rings throughout. Theorem 4.1 has exactly the node's hypotheses
and concludes J-2, equivalently quasi-excellence under the given G-ring hypothesis.
No statement correction or STATEMENT-DISPUTED issue was found.

Hypothesis and conclusion correspondence:

- A commutative ring A: `(A : Type u) [CommRing A]`, with explicit arbitrary universe `u`.
- A is Noetherian: `[IsNoetherianRing A]`.
- A is a G-ring: `(hG : IsGRing A)`. This is an explicit proposition, not a class.
- I is an ideal of A: `(I : Ideal A)`.
- I is contained in every maximal ideal: `(hI : ∀ m : Ideal A, m.IsMaximal → I ≤ m)`.
  This directly renders the maximal-ideal condition; it does not assume that A itself
  is a Jacobson ring. It permits equality with the Jacobson radical.
- The quotient A/I is quasi-excellent: `(hquot : IsQuasiExcellent (A ⧸ I))`.
- A is quasi-excellent: the conclusion `IsQuasiExcellent A`.
- No adic completeness, characteristic, dimension or universal catenarity restriction:
  none appears among the binders. No domain, nonzero or local-ring restriction appears.

Dependency declarations used, with full source definitions/docstrings read:

- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`: Noetherian as a module over
  itself, equivalently every ideal finitely generated. This is the declaration of
  `def-weil-pbc-noetherian-ring`.
- `WeilConjectures.RingTheory.GRing`, `IsGRing`: Noetherianity and regularity of the
  canonical completion map at every prime localization. Also read its supporting
  `Algebra.IsGeometricallyRegular` and `RingHom.IsRegular` definitions. This is the
  recorded upstream declaration of `def-weil-pbc-g-ring`; no retired Sheaf twin is imported.
- `Sheaf.RingTheory.ExcellentRing`, `IsQuasiExcellent`: the conjunction of Noetherianity,
  `IsGRing`, and open regular locus for every finite type algebra. It is listed in
  `def-exc-excellent-ring.lean.declarations`. The node's principal declaration is
  `IsExcellent`, but the same module supplies precisely the quasi-excellent predicate
  needed here. Its `IsUniversallyCatenary` clause is not required by this statement.

Statement imports are public. Already stated proof dependencies are imported privately:
`Sheaf.RingTheory.JTwoFiniteAlgebraCriterion` (finite-algebra criterion),
`Sheaf.RingTheory.RegularLocusOpenFromPrimeQuotients` (prime-quotient criterion),
`WeilConjectures.AlgebraicGeometry.GenericFlatness`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper`,
`WeilConjectures.RingTheory.FiniteTypeGRing`,
`WeilConjectures.RingTheory.FlatUnderRegular`, and
`WeilConjectures.RingTheory.RegularLocalLocalization`.
Mathlib leaves in the proof are supplied by `Morphisms.Flat`, `AffineScheme`,
`FiniteType`, `Localization.Submodule`, `Nakayama`, `Noetherian.Basic`, and
`Spectrum.Prime.Topology` in their recorded topic directories. The genuine proof
prerequisite `lem-per-g-ring-alteration-closed-fibre-neighbourhood` has no recorded
Lean module at the time of writing, so there is no module for it to import. Its
role remains explicit in the proof docstring; it is not needed to type the statement.
The docstring gives all seven DAG proof steps and names their dependencies, including
the common flat open and the two-point specialization argument.

Edge cases checked before writing:

- I = 0 is allowed; the implication then has the expected identity-quotient case.
- I = top is excluded by hI in a nonzero ring because maximal ideals are proper;
  in the zero ring the maximal-ideal quantification is vacuous, as required.
- The zero ring is allowed: its spectrum is empty and the regular-locus condition
  is vacuous; no `Nontrivial` or `IsDomain` assumption accidentally excludes it.
- Nonlocal rings and arbitrary characteristics are permitted. Neither reducedness nor
  any dimension bound is imposed. The universe of A is arbitrary and the quotient
  lives in that same universe. The theorem introduces no smaller test-algebra universe.
- No completeness is silently inferred or assumed, and quasi-excellence is not
  replaced by excellence (which would impose universal catenarity).

Searches actually run using the prescribed `msearch.py` wrapper:

- LeanFinder: "A Noetherian G-ring with quasi-excellent quotient by an ideal contained
  in the Jacobson radical is quasi-excellent". Eight hits on Jacobson quotients,
  Noetherian quotients, quasi-finite algebras, and adic separatedness; none states this theorem.
- Loogle: `"IsQuasiExcellent"`. Zero hits.
- Mathlib grep, subdirectory `RingTheory`:
  `QuasiExcellent|quasi.?excellent|IsG.?Ring|G-ring`. Zero hits.
- LeanSearch: "Noetherian G-ring quasi-excellent quotient ideal Jacobson radical implies
  quasi-excellent ring". Eight hits on Jacobson radicals and Jacobson-ring definitions;
  none states the theorem.
- `rg` on the project `lean/WeilConjectures` and `lean/Sheaf` for `IsQuasiExcellent`,
  `quasiExcellent`, `quasi_excellent`, `QuasiExcellent`, G-ring vocabulary, and
  `isQuasiExcellent_of_quotient_of_isGRing|isQuasiExcellent_of_quotient`. Found the
  canonical definitions above and the distinct complete-pair theorem, which assumes
  a rational algebra and adic completeness and therefore is not an exact match.
- Searched `lean/WeilConjectures` for the item id: no attachment. Searched
  `dag/lean_names_upstream.json` for `IsQuasiExcellent|IsGRing`: no matching indexed row.
- The requested example `Sheaf.CategoryTheory.CompactObject` is withdrawn. Read its
  node record and the replacement `WeilConjectures.CategoryTheory.CompactObject`:
  the delivered module follows its module/header/public-section conventions.

Validation: compiled the delivered file with `scompile.py` against the live published
library in both sandbox and library module contexts. Both passed, without errors or
unexpected warnings. No direct Lean, Lake or global build was run; all authored
files are confined to the assigned sandbox.

## Second reading by Q78

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
