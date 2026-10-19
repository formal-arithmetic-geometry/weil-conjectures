## Worker report

The module `Sheaf.TraceFormula.CILocalRingPrincipalNeighbourhood` states
`TraceFormula.ciLocalRingPrincipalNeighbourhood`, with `sorry` as its only proof.
It states Stacks Algebra Tag 00SG (1) implies (3), using the local-ring
presentation spelled out in Tag 00SD. No definition, new node, dependency
repair, statement correction, or disputed statement is needed.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Field k | `(k : Type u) [Field k]` |
| Finite type k-algebra F | `(F : Type v) [CommRing F] [Algebra k F]` and `hfinite : RingHom.FiniteType (algebraMap k F)` |
| Prime ideal Q of F | `(Q : Ideal F) [Q.IsPrime]` |
| The ring F_Q | `Localization.AtPrime Q`, with its canonical composite k-algebra structure |
| Regular local k-algebra A | `(A : Type w) [CommRing A] [Algebra k A] [IsRegularLocalRing A]`; the last class includes locality and Noetherianity |
| A essentially of finite type over k | `[Algebra.EssFiniteType k A]` |
| Finite sequence a_1,...,a_c | `(a : List A)`; c is its length, and zero length is permitted |
| The sequence is regular in A | `hregular : RingTheory.Sequence.IsRegular A a` |
| Each element lies in the maximal ideal | `hmaximal : ∀ x ∈ a, x ∈ IsLocalRing.maximalIdeal A` |
| F_Q is isomorphic to A/(a_1,...,a_c) as k-algebras | `e : Localization.AtPrime Q ≃ₐ[k] (A ⧸ Ideal.ofList a)` |
| There exists h in F outside Q | `∃ h : F, h ∉ Q ∧ ...` |
| F_h is a global complete intersection over k | `Algebra.IsGlobalCompleteIntersection k (Localization.Away h)` |

The existential witnesses A, its algebra/regularity/essential-finiteness structures,
a, and e are unpacked as theorem arguments: the conclusion is obtained for every
presentation satisfying the hypothesis. They are not fixed additional data required
of F or Q. In particular, any witnesses to the node's existential hypothesis can
be supplied. The universe w of A is independent of u and v, so this formulation
places no size restriction on that witness.

Dependency declarations read and reused:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (the current recorded
  declaration) and `Algebra.FiniteType`; `RingHom.finiteType_algebraMap` confirms
  their equivalence for the given algebra structure.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
  Its local-ring instance and canonical scalar structure supply F_Q.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, the ring
  clause of `def-weil-regular-scheme`'s retained mathlib_match. The recently
  recorded `Sheaf.AlgebraicGeometry.IsRegularScheme` was also read; its
  scheme clause is not used for the ring A and is not copied or specialized.
- `Mathlib.RingTheory.EssentialFiniteness`: `Algebra.EssFiniteType`, exactly the
  essentially-finite-type algebra notion in the dependency's mathlib_match.
- `Mathlib.RingTheory.Regular.RegularSequence`:
  `RingTheory.Sequence.IsRegular` and `Ideal.ofList`, for the regular list and
  its generated ideal. Regularity includes that the final quotient is nonzero.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, available
  through the global-complete-intersection module. For commutative rings it
  carries the canonical ring and composite k-algebra structures.
- `Sheaf.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsGlobalCompleteIntersection`. Its actual definition was read:
  zero ring allowed, otherwise a finite polynomial presentation by c equations
  of dimension n-c, guarded by c ≤ n. Its local-complete-intersection companion
  is not substituted for the stronger global conclusion here.

The module imports the stated proof dependencies
`Sheaf.TraceFormula.EssentiallyFiniteTypeCIKernelInvariance` and
`Sheaf.RingTheory.LCIRegularSequenceGlobalCompleteIntersection`, and the
Mathlib polynomial-regularity module. Their signatures and proof docstrings
were read. The quotient-localization proof dependency has no recorded Lean
module and is retained as a named step in the proof docstring. All four node
proof steps appear there, including transfer from the polynomial quotient back
to the original F. No completion or Henselian hypothesis is introduced.

Sources checked locally: `literature/stacks-project/algebra.tex`,
Definition `definition-lci-local-ring` (00SD, lines 36013–36028) and Lemma
`lemma-lci-at-prime` (00SG, lines 36159–36180), with the adjacent 00SF argument.
These agree with the node's statement. The pointwise complete-intersection
assumption need only hold at Q, not at every prime of F.

Edge cases checked before writing:

- Empty a: regularity allows the zero-length sequence in the nonzero regular
  local ring A. The quotient is A, so regular localizations are included.
- F the zero ring: it has no prime Q, so there is no accidental nonempty
  point hypothesis or spurious conclusion. The conclusion still reuses the
  global definition's zero-ring convention without altering it.
- Q need not be maximal. Nothing assumes F_Q has residue field k, F is local,
  or F is a domain. Nonreduced complete intersections such as k[x]/(x²) are
  allowed, as are positive-dimensional and nonclosed-prime examples.
- k has arbitrary characteristic and need not be perfect or algebraically
  closed. The field, F and A have independent explicitly bound universes.
- h is required only to avoid Q; h = 1 is permitted. Since Q is prime,
  h = 0 cannot satisfy the conclusion.

Searches made with `msearch.py Q153 lem-trf-ci-local-ring-principal-neighbourhood`:

- `leanfinder`: "A finite type algebra over a field whose localization at a prime
  is a quotient of an essentially finite type regular local ring by a regular
  sequence has a principal global complete intersection neighborhood". Eight
  hits, chiefly `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`, smooth and
  etale locus results. They have smooth/etale hypotheses rather than the
  regular-sequence quotient hypothesis; none states this result.
- `loogle`: `"CompleteIntersection"`. Zero hits.
- `grep`: `complete.?intersection|CompleteIntersection|lci.at.prime`. One hit,
  `Mathlib/RingTheory/Extension/Presentation/Basic.lean:103`, a comment about
  presentation dimension, not a complete-intersection predicate or theorem.
- `leansearch`: "For a finite type algebra over a field, if its localization at
  a prime is a complete intersection local ring then some principal localization
  away from that prime is a global complete intersection". Eight hits: local
  rings/localizations and a Dedekind-domain principal-ideal-ring fact, no match.
- Additional `grep` search for `IsRegularLocalRing|RegularLocal` in RingTheory
  located the exact regular-local-ring class and polynomial-regularity instance.
- `rg` searches of upstream `WeilConjectures` and project `lean/Sheaf` for
  complete intersections, principal neighbourhoods, the theorem's chosen name,
  and `lemma-lci-at-prime` found the existing global definition, the polynomial
  quotient globalization theorem, and distinct completion/presentation-invariance
  statements. The quotient globalization theorem assumes a fixed polynomial
  quotient and regular sequence in that polynomial localization; it does not
  state this theorem for an arbitrary F and arbitrary regular-local presentation.
- `grep -rn` for the exact node id in upstream `WeilConjectures` found no match.

Validation: `scompile.py` compiled both the sandbox check and the actual module
cleanly, with no errors or warnings (14.9 s and 28.5 s respectively).
Only the node's `lean` field changes, copied with indent 1 and a final newline.

## Second reading by Q153

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
