## Worker report

The module `Sheaf.RingTheory.QuasiExcellentCompletePair` states
`isQuasiExcellent_iff_quotient_of_isAdicComplete`, with `sorry` as its whole proof.
No definitions, new nodes, dependency repairs or statement changes are needed.
The node copy changes only `lean`.

The statement matches the node clause by clause:

- “A commutative ring” is `(A : Type u) [CommRing A]`, with explicit arbitrary universe `u`.
- “Noetherian” is `[IsNoetherianRing A]`.
- “Q-algebra” is `[Algebra ℚ A]`; no finite-type rational algebra assumption is added.
- “J an ideal” is `(J : Ideal A)`, without primality, properness or principality assumptions.
- “A is J-adically complete” is `[IsAdicComplete J A]`. This includes separatedness:
  `AdicCompletion.of_bijective_iff` identifies it with bijectivity of the canonical map
  to the inverse limit. Starting the powers at zero only adds the unique component
  in the zero quotient A/J^0, so it is the node's inverse limit over n ≥ 1.
- “A is quasi-excellent if and only if A/J is quasi-excellent” is precisely
  `IsQuasiExcellent A ↔ IsQuasiExcellent (A ⧸ J)`.

Statement dependencies read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, the abbreviation for every ideal being finitely generated.
- `def-weil-pbc-adically-complete-ring`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `IsAdicComplete` and `AdicCompletion.of_bijective_iff`.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsQuasiExcellent`.
  Its complete definition is Noetherian, G-ring, and open regular locus for every
  finite type algebra. It is used directly, without adding universal catenarity.

The published declarations for all stated proof dependencies are imported, privately
when used only by the proof. These are `AlgebraicGeometry.Flat` and its base-change and
affine criteria, `AlgebraicGeometry.IsProper`, the surjectivity base-change instance,
`RingHom.FiniteType`, `Algebra.FiniteType.isNoetherianRing`,
`Ideal.finite_minimalPrimes_of_isNoetherianRing`, `IsClosedMap.specializingMap`,
`isGRing_of_finiteType`, `IsRegularLocalRing.of_flat_of_regular_closedFiber`,
`IsRegularLocalRing.of_ringHom_flat`, and
`IsRegularLocalRing.localization_at_prime_and_isRegularRing`.
The five proof-only nodes `lem-per-qe-normal-counterexample-reduction`,
`lem-per-qe-minimal-formal-defect`, `lem-per-qe-semilocal-defect-height`,
`lem-per-qe-alteration-regular-neighbourhood`, and `lem-per-qe-rotthaus-finite-boundary`
have no recorded Lean declarations. Their later imports are left to the maintainer;
they are not needed to type this statement. All ten node proof steps, including
their specific DAG references, are carried in the theorem docstring.

Source check: read the local Travaux de Gabber PDF with `pdftotext -layout`.
Exposé I, Théorème 9.2, printed p.17 states that a Noetherian I-adically complete
ring is quasi-excellent when its quotient is. It has no characteristic hypothesis,
so it covers this node's rational-algebra specialization. The reverse implication
is the finite-type quotient argument written in the node and docstring. The adjacent
paragraph explicitly warns that replacing quasi-excellent by excellent is false;
this statement uses `IsQuasiExcellent` on both sides.

Edge cases checked mathematically before writing:

- J = 0: every ring is separated and complete for this ideal and the conclusion is
  the identity comparison with the zero-ideal quotient.
- J = A: separatedness forces A to be the zero ring. That case is retained; no
  `Nontrivial A` or proper-ideal hypothesis appears. The zero ring is Noetherian
  and its spectrum and regular-locus conditions are empty.
- Nilpotent ideals are allowed; no nonzero element or nonunit is required.
- No local, domain, reducedness, finite-dimensionality or universal-catenarity
  restriction is imposed on A.
- The quotient stays in universe u, so the imported quasi-excellence predicate
  has exactly the same universe parameter for A and A/J.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "A Noetherian rational algebra complete for an ideal is
  quasi excellent if and only if its quotient is quasi excellent"`: eight hits on
  Noetherian quotient and quasi-finite algebra results; none states this theorem.
- `msearch.py ... leansearch "quasi excellence of an ideal adically complete
  Noetherian rational algebra equivalent to quasi excellence of its quotient"`:
  eight hits including `IsAdicComplete`, `AdicCompletion.ofAlgEquiv` and Noetherian
  quotient facts; none states quasi-excellence lifting.
- `msearch.py ... loogle "IsQuasiExcellent, IsAdicComplete"`: no hits, unknown
  identifier `IsQuasiExcellent` in Mathlib's index.
- `msearch.py ... grep "quasi.?excellent|Nishimura" RingTheory`: no Mathlib hits.
- `rg -n "IsQuasiExcellent|quasi.?excellent|Nishimura"` in `lean/WeilConjectures`
  and `lean/Sheaf`: the existing predicate is in `ExcellentRing`; other hits are
  geometric consumers and unrelated excellence results. No complete-pair theorem.
- Search of `lem-per-qe-complete-pair-lifting` in `lean/WeilConjectures`: no hits.
- Search of the chosen declaration name in both library roots and
  `dag/lean_names_upstream.json`: no hits.

No statement dispute or node fault found.

Validation: `scompile.py Q38 lem-per-qe-complete-pair-lifting` compiled the module
cleanly in both sandbox and library modes (11.8 s and 3.7 s). The prescribed
`deliver2.py ... --no-push` passed the server preflight and compilation, reporting
`OK (dry run)` at candidate commit `137b1fae734`. The packet contains exactly the
item's module, its node record, and this report.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
