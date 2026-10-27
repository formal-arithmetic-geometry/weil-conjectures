## Worker report

The module `Sheaf.RingTheory.QuasiExcellentCompletePair` states
`isQuasiExcellent_iff_quotient_of_isAdicComplete`. Its sole theorem has proof `sorry`;
no definitions, auxiliary theorems, new nodes, or dependency repairs are needed.
The item JSON changes only in `lean`.

Hypothesis and conclusion correspondence:

- “A commutative ring A”: `(A : Type u) [CommRing A]`, with explicitly declared
  universe `u`, arbitrary throughout.
- “Noetherian”: `[IsNoetherianRing A]`, the recorded Mathlib predicate from
  `def-weil-pbc-noetherian-ring`.
- “Q-algebra”: `[Algebra ℚ A]`. This retains the actual rational algebra structure;
  mere characteristic zero is not substituted.
- “J an ideal of A”: `(J : Ideal A)`, without any properness, maximality,
  principality, or nonzero condition.
- “A is J-adically complete, the canonical map to lim A/J^n is an isomorphism”:
  `[IsAdicComplete J A]`, the recorded declaration for
  `def-weil-pbc-adically-complete-ring`. In
  `Mathlib.RingTheory.AdicCompletion.Basic`, `AdicCompletion.of_bijective_iff`
  identifies this with bijectivity of the canonical map to the inverse limit.
  The module definition includes Hausdorffness as well as precompleteness;
  it does not silently replace separated completeness by precompleteness.
  The n=0 quotient contributes a zero ring and does not change the n>=1 limit.
- “A is quasi-excellent if and only if A/J is quasi-excellent”:
  `IsQuasiExcellent A ↔ IsQuasiExcellent (A ⧸ J)`. Both sides use exactly the
  `IsQuasiExcellent` declaration recorded among the declarations of
  `def-exc-excellent-ring`. This is not `IsExcellent`, which has an extra
  universal catenarity condition.

Statement dependencies, read in their source with their signatures and docstrings:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` is the abbreviation
  `IsNoetherian R R`; `isNoetherianRing_iff_ideal_fg` identifies the ideals condition.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` extends
  `IsHausdorff I M` and `IsPrecomplete I M`, specialized to `M = A`.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent (R : Type u) [CommRing R]`
  is Noetherianity, `IsGRing R`, and openness of the regular locus of every finite
  type R-algebra. Although the node's primary record is `IsExcellent`, the same
  record explicitly lists and the module publicly provides `IsQuasiExcellent`.

The file publicly imports these statement modules and
`Mathlib.Algebra.Algebra.Rat` for the rational algebra structure. It privately
imports all currently recorded proof-dependency modules, including Mathlib matches:
`Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`Mathlib.AlgebraicGeometry.Morphisms.Proper`,
`Mathlib.AlgebraicGeometry.PullbackCarrier`, `Mathlib.RingTheory.FiniteType`,
`Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`, `Mathlib.Topology.Inseparable`,
`WeilConjectures.RingTheory.FiniteTypeGRing`,
`WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber`,
`WeilConjectures.RingTheory.FlatUnderRegular`, and
`WeilConjectures.RingTheory.RegularLocalLocalization`.
The five proof nodes `lem-per-qe-normal-counterexample-reduction`,
`lem-per-qe-minimal-formal-defect`, `lem-per-qe-semilocal-defect-height`,
`lem-per-qe-alteration-regular-neighbourhood`, and
`lem-per-qe-rotthaus-finite-boundary` have no recorded declarations yet. They are
not needed to type this statement; the theorem docstring retains their entire
proof route, including the normalized boundary and final contradiction.

Source checked: the local PDF of Illusie--Laszlo--Orgogozo, Travaux de Gabber,
Exposé I, Théorème 9.2, printed p.17, states precisely that a Noetherian
I-adically complete A with quasi-excellent A/I is quasi-excellent (in fact without
characteristic restriction). The node intentionally specializes to rational
algebras. The converse is checked in the local Stacks `more-algebra.tex`,
`lemma-finite-type-over-excellent`, together with `definition-excellent` and
`proposition-finite-type-over-G-ring`: a quotient is a finite type algebra.
The complete ten-step node proof is transcribed in the declaration docstring.

Edge cases checked before writing:

- J=0 gives A/J canonically isomorphic to A and a tautological equivalence.
- J=top: separated J-adic completeness forces A to be the zero ring, which is
  allowed by `[CommRing A] [Algebra ℚ A]`. No `[Nontrivial A]` is imposed.
- The zero ring has empty prime spectrum and vacuous regular-locus conditions;
  its G-ring condition has no primes. The statement does not exclude it.
- General complete pairs need not be local, reduced, integral, or complete for
  a maximal ideal. None of these extra restrictions appears in Lean.
- The chosen `u` permits any size of A, and its quotient remains in that same
  universe. No independent too-small universe is introduced for test algebras.
- Completeness includes separatedness; dropping it would alter the statement.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder` query:
  `A Noetherian rational algebra complete for an ideal is quasi-excellent if and only if its quotient by that ideal is quasi-excellent`.
  Eight hits on Noetherian quotients, quasi-finite algebras and associated primes;
  no quasi-excellence lifting theorem.
- `msearch.py ... loogle 'IsQuasiExcellent, IsAdicComplete'`: zero hits;
  Loogle reports unknown identifier `IsQuasiExcellent`.
- `msearch.py ... grep 'QuasiExcellent|quasi.excellent|Nishimura' RingTheory`:
  zero Mathlib hits.
- `msearch.py ... leansearch` query:
  `quasi excellent Noetherian rational algebra complete ideal quotient quasi excellent`.
  Eight hits, all about ordinary quotients, finite algebras, and characteristic;
  none states the item.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `quasi.?[Ee]xcellent|complete_pair|completePair|Nishimura`: the existing
  `IsQuasiExcellent` definition and geometric uses were found, with no lifting theorem.
- Node-id search in `lean/WeilConjectures` found no statement for this item.
- `rg` for `IsQuasiExcellent|quasiExcellent_iff|isQuasiExcellent_iff` in both
  RingTheory trees found the definition and Nagata theorem, no complete-pair result.
- Search for the proposed declaration name in Mathlib and both source roots
  found no collision. The upstream name index likewise had no quasi-excellent hit.

Validation: prescribed `scompile.py Q138 lem-per-qe-complete-pair-lifting <file>`
passed both sandbox and actual module compilation, with no errors or warnings
(5.5 s and 4.1 s). All Lean lines are at most 100 characters. No statement fault
or disputed claim was found. No source statement or dependency record was changed.

## Second reading by Q138

This is the dispatcher's single-worker assignment; the worker reread the node
and completed module, and the maintainer supplies the independent delivery review.
The rereading checked each binder against the node: arbitrary commutative A,
Noetherian A, actual Q-algebra structure, arbitrary ideal J, separated adic
completeness, and both quasi-excellence conclusions. The quotient uses the
original ideal J directly. The definitions' docstrings and bodies confirm that
`IsQuasiExcellent` is the exact requested predicate and that `IsAdicComplete`
includes the injectivity condition. No properness or nontriviality assumption
appears, and no special ideal or local ring replaces the original pair. The
source's theorem validates the lifting direction and the finite-type quotient
argument validates the converse. No mismatch was found or corrected. No new
nodes or dependency modules occur. The only postponed proof is the named theorem.
