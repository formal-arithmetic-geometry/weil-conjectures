## Worker report

The module `Sheaf.RingTheory.CompleteIntersectionLocalRingPrincipalNeighbourhood` states
`Algebra.exists_globalCompleteIntersection_of_regularLocalQuotient`, with proof `sorry`.
It introduces no definitions, helper theorems, dependency repairs, or statement corrections.

Source checked: `literature/stacks-project/algebra.tex`, Definition 00SD
(`definition-lci-local-ring`, lines 36013–36028) and Lemma 00SG
(`lemma-lci-at-prime`, lines 36159–36180), implication (1) => (3).
The node spells out exactly the regular-local quotient hypothesis of 00SD.

Clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`, with no restriction on characteristic.
- The finite type commutative k-algebra is `(F : Type v) [CommRing F] [Algebra k F]`
  and `(hF : (algebraMap k F).FiniteType)`. This uses the dependency's currently
  recorded `RingHom.FiniteType`; its equivalence to `Algebra.FiniteType k F` is
  `RingHom.finiteType_algebraMap` in the same Mathlib module.
- The prime ideal is `(Q : Ideal F) [Q.IsPrime]`; its local ring is the canonical
  `Localization.AtPrime Q`, with the induced k-algebra structure.
- The witness regular local k-algebra is `(A : Type w) [CommRing A] [Algebra k A]`
  with `[IsRegularLocalRing A]`. This class includes locality and Noetherianity,
  and says the maximal ideal has the required number of generators. The ring
  clause of `def-weil-regular-scheme` is supplied by its unchanged `mathlib_match`;
  its newer scheme declaration `IsRegularScheme` concerns the other clause and
  is not a replacement for the recorded ring predicates.
- Essential finite type of this witness is `[Algebra.EssFiniteType k A]`.
- The finite sequence is `(a : List A)`, of length `a.length`; no positivity of
  the length is imposed. Its regularity is `(ha : RingTheory.Sequence.IsRegular A a)`.
  This includes injectivity on successive quotients and nonzero final quotient.
- Containment of all sequence elements in the maximal ideal is exactly
  `(ham : ∀ x ∈ a, x ∈ IsLocalRing.maximalIdeal A)`.
- The specified isomorphism is
  `(e : Localization.AtPrime Q ≃ₐ[k] A ⧸ Ideal.ofList a)`.
  This is an algebra equivalence, not merely a ring equivalence.
- The conclusion is `∃ h : F, h ∉ Q ∧
  IsGlobalCompleteIntersection k (Localization.Away h)`: the same element lies
  outside Q and its canonical principal localization is globally a complete
  intersection over the original k.

The existential witnesses in the hypothesis (A, its structures, the sequence,
and the equivalence) are explicit theorem arguments. Supplying these is logically
exactly applying the theorem after eliminating that existential hypothesis;
conversely, a theorem with the existential hypothesis applies to any such witnesses.
No fixed presentation, completeness, separability, or extra dimension condition
is assumed. All three universes and every binder are explicit; the witness algebra
may live in an independent universe because it is supplied, not quantified over as
a restricted family of test objects.

Dependency declarations read and reused:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` and its underlying
  `Algebra.FiniteType` (def-weil-pbc-finite-type-algebra).
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`
  (def-weil-pbc-localization-at-prime); this item uses only the local-ring clause,
  not that dependency's separate residue-field or fibre-ring clauses.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, the ring clause
  of the `mathlib_match` for def-weil-regular-scheme; its full class signature and
  docstring were read. The scheme-only recorded module was also read.
- `Mathlib.RingTheory.EssentialFiniteness`: `Algebra.EssFiniteType`
  (def-weil-pbc-essentially-finite-type-algebra).
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`
  and `IsWeaklyRegular` (def-weil-pbc-regular-sequence).
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, with its
  ring/algebra interface from `Mathlib.RingTheory.Localization.Away.Basic`
  (def-weil-ring-localization-away).
- `Sheaf.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsGlobalCompleteIntersection`
  (def-weil-pbc-complete-intersection-over-field). Its polynomial quotient,
  expected dimension, and zero-ring convention are preserved, not restated.

Proof-plan imports are ordinary non-public imports:
`Sheaf.TraceFormula.EssentiallyFiniteTypeCIKernelInvariance` for
`TraceFormula.essentiallyFiniteTypeCIKernelInvariance`, and
`Sheaf.RingTheory.LCIRegularSequenceGlobalCompleteIntersection` for
`Algebra.exists_globalCompleteIntersection_of_regularSequence`.
Their complete signatures and docstrings were read. The Mathlib proof leaves
use `Mathlib.RingTheory.Localization.Ideal` (quotient-localization instance,
`Ideal.map_primeCompl_comap_of_surjective`, `IsLocalization.algEquiv`) and
`Mathlib.RingTheory.RegularLocalRing.Polynomial`
(`MvPolynomial.isRegularRing_of_isRegularRing`). Their source declarations were
also read. The module docstring records all four proof steps and the DAG nodes
used in each; the only postponed theorem matches the assigned DAG node.

Edge cases checked before writing:

- Empty regular sequence is allowed: the ideal is zero and the quotient is A.
  There is no binder requiring a nonempty list or positive codimension.
- A field as A and codimension zero are included. There is no positive-dimension
  or positive-number-of-variables hypothesis.
- The zero F has no prime Q, so there is no missing conclusion for that case.
  Nontriviality is not an extra assumption on F.
- Since Q is prime, h outside Q cannot be zero or nilpotent. The principal-open
  neighbourhood really contains Q; no assertion at all other primes is assumed.
- The canonical quotient and localization retain their induced k-algebra
  structures. The equivalence preserves k, as required.
- Arbitrary field characteristic and independent ring universe levels are retained.

Searches (all performed before writing):

- `msearch.py ... leanfinder` query:
  "For a finite type algebra over a field, a prime whose local ring is a quotient
  of an essentially finite type regular local algebra by a regular sequence has a
  principal global complete intersection neighbourhood".
  Result: eight hits, including `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`,
  `Algebra.IsSmoothAt.exists_notMem_smooth`, `Algebra.QuasiFiniteAt`, and etale/smooth
  locus results. These require smoothness or concern different properties, not
  the complete-intersection local-ring hypothesis. No exact match.
- `msearch.py ... leansearch` query:
  "A finite type algebra over a field whose local ring at a prime is a complete
  intersection has a principal neighbourhood that is a global complete intersection".
  Result: eight hits on local rings of localizations, quasi-finiteness, and smooth
  loci; none states the implication in this node.
- `msearch.py ... loogle` query `"CompleteIntersection"`: zero hits.
- `msearch.py ... grep` query
  `complete.?intersection|lci.at.prime|principal.*neighbourhood`: one hit,
  `Mathlib/RingTheory/Extension/Presentation/Basic.lean:103`. Read lines 90–108:
  this is only a comment on the dimension of a presentation, not a statement.
- `rg` in upstream `WeilConjectures/` for `CompleteIntersection|complete.?intersection`
  and for the exact node id: no matches. The exact theorem name also has no
  collision in Mathlib, upstream, the side library, or `dag/lean_names_upstream.json`.
- `rg` in `lean/Sheaf` and `dag/lean_names_upstream.json` found the reused global/local
  complete-intersection definitions and related results. Source signatures were
  inspected: `exists_globalCompleteIntersection_of_regularSequence` assumes a
  polynomial-localization kernel, so it is the last proof step, not this node's
  statement; `completion_local_complete_intersection_iff` has a maximal prime,
  completion, and a local-complete-intersection conclusion, hence is different;
  `conormal_generators_global_complete_intersection` uses a conormal-generator
  criterion, also different. No existing declaration states this item.

Validation: the required `scompile.py Q110 lem-trf-ci-local-ring-principal-neighbourhood`
compiled the delivered module cleanly, including its library-form check (1.5 seconds).
No errors or warnings were emitted. The only proof is `sorry`, as required for stage 2.
No node faults or disputed statements were found.

## Second reading by Q110

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
