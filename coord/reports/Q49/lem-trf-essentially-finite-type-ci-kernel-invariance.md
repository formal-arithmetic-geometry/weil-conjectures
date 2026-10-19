## Worker report

This repair replaces the returned stage-1-only packet at immutable head
692064168bfa with a stage-2 statement. That head had no module and its report
described a split, which explains the return's `--apply-fixes` rejection of
`report.md` with `(no module)`. The sandbox initially contained only dispatcher
brief markers. I reconstructed the node copy from the current shared DAG,
preserved every field except `lean`, and added the actual module
`lean/Sheaf/TraceFormula/EssentiallyFiniteTypeCIKernelInvariance.lean`.
The prescribed deliver2.py packet carries the report at the normal
`coord/reports/Q49/lem-trf-essentially-finite-type-ci-kernel-invariance.md`
path; no reviewer `--apply-fixes` payload is being submitted.

The sole declaration is
`TraceFormula.essentiallyFiniteTypeCIKernelInvariance`. Its sole proof is
`sorry`, as stage 2 requires. Its module and declaration docstrings cite
Stacks Algebra Tags 00SF and 00SD and the item's blueprint id. The declaration
docstring contains all six steps of the node's common-polynomial-localization
proof, including the fraction argument proving both comparison maps surjective.
The source passages at `definition-lci-local-ring`, `lemma-ci-well-defined`,
and `lemma-lci-local` in algebra.tex were read. No statement correction,
new notion, new node, or dependency-interface replacement is needed.

Every hypothesis and conclusion clause is represented as follows:

- The field is `(k : Type u) [Field k]`, with no restriction on characteristic.
- The commutative local k-algebra A is `(A : Type v) [CommRing A]
  [Algebra k A] [IsLocalRing A]`. Its essential finite type hypothesis is
  `[Algebra.EssFiniteType k A]`.
- The first commutative regular local k-algebra is `(P : Type w)
  [CommRing P] [Algebra k P] [IsRegularLocalRing P]`; its essential finite
  type hypothesis is `[Algebra.EssFiniteType k P]`. Regular-local includes
  local and Noetherian in Mathlib's class, so neither is silently dropped.
- The second source is `(Q : Type z) [CommRing Q] [Algebra k Q]
  [IsRegularLocalRing Q] [Algebra.EssFiniteType k Q]`.
- `(u : P →ₐ[k] A) (v : Q →ₐ[k] A)` are precisely the two specified
  k-algebra homomorphisms. Their scalar compatibility is part of AlgHom,
  rather than an omitted condition on arbitrary ring maps.
- `[IsLocalHom u.toRingHom] [IsLocalHom v.toRingHom]` assert locality.
  For local rings, reflection of units is equivalent to sending the source
  maximal ideal into the target maximal ideal, the node's convention.
- `(hu : Function.Surjective u) (hv : Function.Surjective v)` assert the
  two surjections separately.
- The left side of `↔` is `∃ xs : List P`, with
  `RingTheory.Sequence.IsRegular P xs` for P-regularity,
  `Ideal.ofList xs = RingHom.ker u.toRingHom` for generation of exactly
  the specified kernel, and `∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal P`
  for membership of every generator in the maximal ideal.
- The right side is `∃ ys : List Q`, with
  `RingTheory.Sequence.IsRegular Q ys`,
  `Ideal.ofList ys = RingHom.ker v.toRingHom`, and
  `∀ y ∈ ys, y ∈ IsLocalRing.maximalIdeal Q`.
- Lists are finite and may be empty. No positive length, chosen presentation,
  perfection, algebraic closedness, completeness, or finite-type-in-place-of-
  essentially-finite-type condition is imposed. The four independent carrier
  universes are explicitly bound, and `autoImplicit` is disabled.

Dependency declarations used:

- `def-weil-pbc-essentially-finite-type-algebra`: its `mathlib_match` is
  `Algebra.EssFiniteType` in `Mathlib.RingTheory.EssentialFiniteness`.
  I read its class and the equivalent finite-type-subalgebra localization
  formulation `Algebra.essFiniteType_iff_exists_subalgebra`; this is exactly
  the node's arbitrary multiplicative-set localization condition.
- `def-weil-regular-scheme`: its retained ring `mathlib_match` is
  `IsRegularLocalRing` in `Mathlib.RingTheory.RegularLocalRing.Defs`.
  I read the class, which extends IsLocalRing and IsNoetherianRing and
  equates maximal-ideal spanFinrank with ringKrullDim. The node's newer
  `AlgebraicGeometry.IsRegularScheme` in
  `Sheaf.AlgebraicGeometry.IsRegularScheme` was also opened; it supplies
  the scheme clause, which is not the ring clause used here. Its lean.note
  explicitly retains the Mathlib ring matches.
- `def-weil-pbc-regular-sequence`: the recorded declaration is
  `RingTheory.Sequence.IsRegular` in
  `Mathlib.RingTheory.Regular.RegularSequence`. I read IsWeaklyRegular
  and IsRegular: injectivity on each preceding quotient and nonzero final
  quotient are both required. `Ideal.ofList` is the generated ideal;
  no private regular-sequence or complete-intersection predicate is defined.

The proof-only imports expose the recorded Mathlib interfaces for finite type,
multivariable polynomials, prime localization, the localization universal
property, and regular polynomial rings. The regular-local-surjection comparison
has no recorded Lean declaration on the current DAG and is not imported from
another group's sandbox. It is cited in the proof docstring as the existing
DAG theorem, not replaced or assumed as an additional theorem hypothesis.

Edge cases checked mathematically and against the actual definitions:

- P = Q = A = k with identity maps: both kernels are zero; the empty lists
  have zero generated ideals, regularity holds because k is nonzero, and
  maximal-ideal membership is vacuous.
- P = k[x] localized at (x), Q = A = k: the left kernel has regular
  generator x while the right kernel has an empty list. Nothing requires
  equal list lengths or equal source dimensions.
- A = k[x]_(x)/(x²), with presentations from k[x]_(x) and
  k[x,y]_(x,y): the regular lists (x²) and (x²,y) are admitted although
  A need not itself be regular.
- A non-CI quotient, for example k[x,y]_(x,y)/(x²,xy,y²), is not excluded:
  neither side is presumed true and the iff compares the two properties.
- Nonclosed primes and the field k(t) are allowed by EssFiniteType; no
  finite-type or completeness restriction excludes them.
- The zero ring is not a local ring with a proper maximal ideal under the
  stated source convention, consistent with Mathlib's IsLocalRing.

Searches actually rerun through msearch.py for this repair (logged in sandbox
searches.jsonl), in addition to the inherited DAG searches:

- LeanFinder: "For two regular local algebras essentially of finite type
  over a field surjecting locally onto the same local algebra, one kernel
  is generated by a regular sequence if and only if the other kernel is".
  Eight hits: formally smooth cotangent criteria, regular-sequence transport,
  Kaehler differential kernel, and regularity in a maximal ideal. None is
  independence of regular-local presentation kernels.
- Loogle: `IsRegularLocalRing, RingHom.ker, RingTheory.Sequence.IsRegular`.
  Zero hits.
- Mathlib grep: `complete.intersection|CompleteIntersection|ker.*[Rr]egular|[Rr]egular.*ker`
  in RingTheory. Seven hits on IsSMulRegular kernels and a presentation
  dimension docstring; no presentation-independence theorem. The presentation
  dimension source was opened and its complete-intersection mention is a
  caveat in a docstring, not this theorem.
- LeanSearch: "Independence of regular local presentation for complete
  intersection local algebras essentially of finite type over a field".
  Eight finite-presentation and localization hits; none states this result.
- rg over WeilConjectures and lean/Sheaf for complete intersection and regular
  kernels, plus the exact item id and proposed declaration name, found no
  exact existing statement. The upstream
  `RingTheory.Sequence.isWeaklyRegular_append_of_surjective` was opened;
  it concerns concatenating sequences across a fixed quotient. The side
  `completeLocalCIPresentationIndependence` in
  `Sheaf.TraceFormula.CompleteLocalCIPresentationIndependence` was opened;
  it requires a complete target and cannot state this noncomplete result.
  The proposed name is absent from the upstream name index as well.

Validation: scompile.py successfully compiled this module separately in both
its sandbox and final library path, with no errors or unexpected warnings.
The node's `lean.statement` is extracted verbatim from the theorem signature.
JSON uses indent 1, Unicode characters, and a final newline. The mathematical
statement, proof, dependency lists, and all non-lean node fields are unchanged.

## Repair of the return

The single return was a malformed stage-2 fix packet: the immutable returned
head was a stage-1 split and supplied no module. This delivery now contains a
real, compiled module, the item's lean record in its node copy, and this full
stage-2 report. It does not repeat the old split_report-only change or submit
`report.md` as a reviewer fix filename. The standard deliver2.py wrapper builds
the packet against current newtargets-dag and runs the stage-2 preflight.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
