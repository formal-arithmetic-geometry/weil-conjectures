## Worker report

The module `Sheaf.RingTheory.NoetherianLocalDomainInfiniteOpens` states
`AlgebraicGeometry.Spec.infinite_of_isOpen_of_two_le_topologicalKrullDim` with a
single `sorry` proof. No definition or additional theorem is introduced. The source
read is `literature/stacks-project/algebra.tex`, lines 14738–14769, Stacks Tag 02IG,
`lemma-Noetherian-local-domain-dim-2-infinite-opens`. Its statement agrees exactly
with the DAG statement. The declaration docstring carries all seven accepted DAG
proof steps, including the generic-singleton reduction, parameter lifting and
reordering, and the quotient-prime-chain contradiction.

Clause-by-clause translation:

- The arbitrary commutative ring is `(R : Type u) [CommRing R]`, with explicit
  `universe u`. No cardinality or characteristic restriction is imposed.
- Noetherian is `[IsNoetherianRing R]`: every ideal is finitely generated.
- Local, with a unique maximal ideal, is `[IsLocalRing R]`. The symbol n in the
  node denotes that unique ideal; it is not additional chosen data in the claim.
- Nonzero integral domain is `[IsDomain R]`, which includes `Nontrivial R` and
  gives the zero-product property for a commutative ring. No redundant separately
  chosen maximal ideal or nontriviality hypothesis is needed.
- The topological space Spec R is the carrier of `Spec (CommRingCat.of R)`.
  This uses the recorded affine-scheme construction, rather than a private
  spectrum or a replacement dimension convention.
- The dimension hypothesis is exactly
  `(hdim : 2 ≤ topologicalKrullDim (Spec (CommRingCat.of R)))` in `WithBot ℕ∞`.
  It is not replaced by finite dimension, equality to two, or a dimension bound
  on the open subset.
- An arbitrary subset O of that space is `(O : Set (Spec (CommRingCat.of R)))`.
- Open is `(hO : IsOpen O)`; nonempty is `(hne : O.Nonempty)`.
- The conclusion that this same O is infinite is `O.Infinite`.

Statement dependencies, whose full source declarations and docstrings were read:

- `def-weil-pbc-noetherian-ring`:
  `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`; the source also gives
  `isNoetherianRing_iff_ideal_fg`, confirming the ideal-finiteness meaning.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` (and the recorded `Spec.map`, although this theorem
  needs no induced map).
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, defined as `Order.krullDim (IrreducibleCloseds T)`.
- The standard local/domain mixins were read in
  `Mathlib.RingTheory.LocalRing.Defs` and `Mathlib.Algebra.Ring.Defs`.

Plain proof imports follow the accepted plan:

- `Mathlib.RingTheory.Ideal.KrullsHeightTheorem` gives the finite-dimension
  instance and parameter-existence/Artinian-quotient declarations recorded by
  `lem-weil-pbc-noetherian-local-system-of-parameters`. Its imported height and
  local-quotient APIs give the other clauses of that node.
- `Mathlib.RingTheory.KrullDimension.Regular` gives
  `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`
  for `lem-weil-pbc-dimension-quotient-nonzerodivisor` and imports the recorded
  `ringKrullDim` definition of `def-weil-pbc-krull-dimension-ring`.
- `Mathlib.RingTheory.Spectrum.Prime.Topology` gives
  `PrimeSpectrum.closure_singleton`,
  `PrimeSpectrum.pointsEquivIrreducibleCloseds`,
  `PrimeSpectrum.isTopologicalBasis_basic_opens`,
  `PrimeSpectrum.localization_away_isOpenEmbedding`, and
  `PrimeSpectrum.localization_away_comap_range`, the recorded interfaces for
  the spectrum-closure and localization-basic-open proof nodes.
- `lem-per-partial-parameters-quotient-dimension` has neither a Lean record nor
  a Mathlib match in the read repository. It is only a proof dependency, not
  a notion needed to state this theorem; its future module is therefore not
  imported. This delivery does not postpone any statement dependency.

Edge cases checked before writing: the zero ring is excluded exactly by the
nonzero domain hypothesis; a field has dimension zero and fails the dimension
hypothesis; a one-dimensional DVR has a finite open generic singleton and fails
that same hypothesis, showing the threshold two matters. The empty subset fails
only the explicit nonempty hypothesis. The whole spectrum is allowed. The
standard example k[[s,t]] has dimension two and satisfies the conclusion. The
statement does not add a finite-dimensionality hypothesis: that is a consequence
of the existing local Noetherian hypotheses. Arbitrary ring universes and all
characteristics remain available. No statement dispute or mathematical correction
was found.

Existing-declaration searches actually run:

- `msearch.py ... leanfinder`: “Every nonempty open subset of the spectrum of a
  Noetherian local integral domain of Krull dimension at least two is infinite”.
  Eight hits, including `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`,
  `instFiniteRingKrullDimOfIsNoetherianRingOfIsLocalRing`, and
  `PrimeSpectrum.exist_mem_one_of_mem_maximal_ideal`; none asserts this conclusion.
- `msearch.py ... loogle`: `IsNoetherianRing, IsLocalRing, PrimeSpectrum`.
  One hit, `PrimeSpectrum.exist_mem_one_of_mem_maximal_ideal`, a different
  prime-chain insertion assertion.
- `msearch.py ... leansearch`: “Every nonempty open subset of the spectrum of a
  Noetherian local domain of dimension at least two is infinite”. Eight hits
  about irreducible components, irreducibility, nonemptiness and Noetherian
  spectra, with no exact match.
- `msearch.py ... grep`: `(infinite.*open|open.*infinite|Infinite.*Open|Open.*Infinite)`
  in `RingTheory`: zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `noetherian.local.domain|infinite_of_isOpen_of_two_le|open.*[Ii]nfinite|[Ii]nfinite.*open`:
  unrelated material (DVRs, curves, field extensions and pro-etale clopens), no
  exact declaration. `grep -rn` for this node id in `lean/WeilConjectures`:
  no hits. Search of `dag/lean_names_upstream.json` for the old module/declaration:
  no hits.
- The node already records this same declaration in a module deleted as
  unreachable on 2026-10-20. `scompile.py --source
  Sheaf.RingTheory.NoetherianLocalDomainInfiniteOpens` confirms “Module source
  unavailable”. Thus this delivery supplies the absent module; it does not
  duplicate a current declaration. Only the node's `lean` field is changed.

## Second reading by Q151

A separate in-thread rereading of the source statement, DAG node and written
signature checked each hypothesis and conclusion against the clause mapping
above. In particular `IsDomain` supplies the node's nonzero condition;
`IsLocalRing` names the unique maximal ideal implicitly; the dimension is that
of the full spectrum; and infinitude is asserted for the identical arbitrary
nonempty open O. The seven docstring steps match the accepted proof without
adding a regularity or Cohen–Macaulay condition. No mismatch was found and no
statement change was made. This is the worker's own second pass; the dispatch
brief prohibits other agents and assigns independent review to the maintainer.
