## Worker report

The delivery states `AlgebraicGeometry.lci_pointwise_criterion` and
`Algebra.isLocalCompleteIntersection_iff_localizations` in
`Sheaf.TraceFormula.LciPointwiseCriterion`. Both theorem proofs are `sorry`, as required
for stage 2. It also supplies the missing Stacks 00SD local-algebra definition in
`Sheaf.RingTheory.CompleteIntersectionLocalAlgebra`. The item's natural-language
statement is unchanged; its statement dependencies gain just this new definition node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`. The scheme is `(X : Scheme.{u})`, with its named
  structure map `(s : X ⟶ Spec (.of k))` and `[LocallyOfFiniteType s]`. This is exactly a
  scheme locally of finite type over the given field, with no separatedness, perfection,
  quasi-compactness, smoothness, characteristic or nonemptiness assumption.
- The three scheme assertions are exactly the three entries of `List.TFAE`.
- Condition (1) is `∃ (I : Type u) (U : I → X.affineOpens), ...`. The assertion
  `∀ x : X, ∃ i, x ∈ (U i).1` makes these affine opens cover `X`. An affine open is
  canonically the spectrum of its section ring, so these are the spectra in the node.
  For every `i`, `∃ ft : @Algebra.FiniteType ...` expresses finite generation, and
  `@Algebra.IsLocalCompleteIntersection ... ft` uses precisely the recorded definition.
  The scalar map is `((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ (U i).1 le_top).hom`.
  Thus these are the coordinate algebras over the original field, with the original
  scheme structure morphism, rather than arbitrarily chosen algebra structures.
- Condition (2) is `∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ...` with
  `@Algebra.IsGlobalCompleteIntersection k Γ(X, U.1) ...`. This is exactly a global
  complete-intersection affine neighbourhood at every point. Finite generation already
  follows from the full recorded global-complete-intersection definition.
- Condition (3) is `∀ x : X, @Algebra.IsCompleteIntersectionLocalAlgebra k
  (X.presheaf.stalk x) ...`. The scalar map is the base-to-global-sections map above,
  followed by `X.presheaf.germ ⊤ x trivial`. It therefore expresses the asserted
  isomorphism as a `k`-algebra isomorphism, not just a ring isomorphism.
- The new definition expands condition (3) into `IsLocalRing A ∧ EssFiniteType k A`
  and a presenting `(R : Type (max u v))` with its commutative-ring and algebra
  structures, `IsRegularLocalRing R`, and `EssFiniteType k R`. The finite list `xs`
  satisfies `RingTheory.Sequence.IsRegular R xs`, lies in
  `IsLocalRing.maximalIdeal R`, and has
  `Nonempty ((R ⧸ Ideal.ofList xs) ≃ₐ[k] A)`. These are every clause of Stacks 00SD.
  Locality and essential finite type of the stalks follow already from the scheme
  hypotheses, and are inherent in the source's term “complete-intersection local ring”.
- The separate algebra assertion quantifies `(S : Type v) [CommRing S] [Algebra k S]
  [FiniteType k S]`. Its equivalence is `IsLocalCompleteIntersection k S ↔
  ∀ p : PrimeSpectrum S, IsCompleteIntersectionLocalAlgebra k
  (Localization.AtPrime p.asIdeal)`. PrimeSpectrum supplies each ideal and its primality;
  the localization has the canonical scalar action. There is no assumption on the
  unrelated scheme in this algebra theorem. The field and algebra universes are
  independently quantified.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (its affine-pair finite-type condition).
- `Sheaf.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsGlobalCompleteIntersection` and `Algebra.IsLocalCompleteIntersection`;
  these are used verbatim for all global and affine local conditions.
- `def-weil-regular-scheme`: its unchanged Mathlib ring clause is
  `IsRegularLocalRing` from `Mathlib.RingTheory.RegularLocalRing.Defs`, including
  Noetherianity and locality. The recorded scheme module
  `Sheaf.AlgebraicGeometry.IsRegularScheme` is imported; its scheme predicate is not
  substituted for the ring condition.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`
  includes both successive injectivity and nonzero final quotient.
- `Mathlib.RingTheory.EssentialFiniteness`: `Algebra.EssFiniteType`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- The new definition node supplies `Algebra.IsCompleteIntersectionLocalAlgebra`.

The modules of stated proof dependencies are imported without `public`: polynomial
regularity (`Mathlib.RingTheory.RegularLocalRing.Polynomial`),
`Sheaf.RingTheory.GlobalCompleteIntersectionLocalRegularSequence`,
`Sheaf.TraceFormula.EssentiallyFiniteTypeCIKernelInvariance`, and
`Sheaf.RingTheory.LCIRegularSequenceGlobalCompleteIntersection`. The Mathlib affine
stalk/basic-open dependencies are available through the affine scheme, open immersion,
and residue field imports. Their recorded signatures were inspected. The docstrings
carry all nine proof steps of the node, split into the six algebra steps and the three
scheme steps. No additional theorem or hidden choice of data is introduced.

Edge cases checked before writing:

- Empty schemes: `I` has no `Nonempty` hypothesis; the empty family covers, and both
  pointwise scheme conditions are vacuous.
- Zero rings: the algebra statement has no `Nontrivial S`; its spectrum has no primes.
  The existing definition explicitly admits the empty principal cover and declares the
  zero ring a global complete intersection. No zero ring is required to be a local
  complete-intersection algebra at a nonexistent point.
- Empty regular sequences: `xs : List R` may be `[]`; this presents the regular local
  ring itself, and membership in the maximal ideal is then vacuous.
- Arbitrary characteristics and imperfect fields: only `[Field k]` is assumed.
- The index universe is the scheme universe. For the new definition the presenting
  ring has universe `max u v`, not an independent possibly smaller universe. Any
  essentially finite type algebra over `k` has a representative there: use a finite
  polynomial algebra, quotient and localization. Thus this size convention loses no
  presentation. It allows fields and algebras in independent universes in the algebra
  assertion.

Searches for reuse were made with the prescribed `msearch.py` wrapper. The exact
queries and returned records are appended below. LeanSearch found quasi-finiteness,
finite type, and quotient results; LeanFinder found smoothness, standard-smooth
presentations and DVR equivalences. None states this criterion or defines the Stacks
00SD notion. Loogle found no identifier `Algebra.IsLocalCompleteIntersection` in
Mathlib. Mathlib grep found only the unrelated presentation-dimension docstring, and
no complete-intersection-local-algebra definition.

Direct `rg` searches for `CompleteIntersection|complete.intersection` in the upstream
`WeilConjectures/` and side `lean/Sheaf/` found the existing global and affine-local
algebra definitions, relative global presentations, and other trace-formula criteria.
The full signatures and docstrings were inspected for the definitions used here. The
upstream search for `lem-trf-lci-pointwise-criterion` found no declaration. The side
hits with that id were only proof-plan text in `NodalOpenLocus.lean`. The side helper
`IsLocalCompleteIntersectionOver` in `SyntomicGeometricFibresAffineCriterion.lean`
expresses the cover condition alone; it is not a statement of the pointwise criterion.
Here the cover is written directly with affine opens and canonical section algebras,
without creating a second named scheme predicate. Searches for
`IsCompleteIntersectionLocal|CompleteIntersectionLocal` in upstream and side source
found no definition. A DAG search for complete-intersection local rings found statement
nodes about presentations, kernel invariance and this criterion, but no definition node.
`tools/blueprint_refs.py search 'complete intersection local'` returned zero blueprint
matches. The ancestor command returned `lem-trf-local-term-locality`.

The source was read locally: Morphisms 01UG (three conditions), Algebra 00SD (all four
presentation clauses, including maximal-ideal membership), and Algebra 00SH (conditions
(1) and (2)). No statement fault or disputed assertion was found.

## New nodes

`def-trf-complete-intersection-local-algebra` records exactly the missing Stacks 00SD
notion. Its module is `Sheaf.RingTheory.CompleteIntersectionLocalAlgebra`, declaration
`Algebra.IsCompleteIntersectionLocalAlgebra`. It is a full proposition-valued definition,
with actual regular-sequence and algebra-isomorphism data in the defining predicate,
and no `sorry` or chosen unknown object. It cites the existing regular-ring,
regular-sequence, and essentially-finite-type definitions. The three required search
kinds are copied from the wrapper's exact records into its `mathlib_searches`; upstream,
side-library and DAG searches are detailed above. Its blueprint ancestor and via list
come from the item's recorded ancestor, with this item prepended.

## Second reading by Q90

This is the author's second reading; independent mathematical review is performed by
the maintainer, as specified in the dispatch brief. I reopened the node, both Lean
modules and the source definitions. The field, local-finite-type hypothesis, affine
cover, finite-generation witnesses, global affine neighbourhoods, every-point stalk
condition, and every-prime algebra equivalence correspond exactly as listed above.
The new definition includes the source's maximal-ideal requirement and regularity of
its finite list; the quotient is an algebra equivalence. The first compile identified
that membership must use the underlying open `(U i).1` or `U.1`, and one overlong line;
these were repaired. The next wrapper run compiled both delivered files cleanly in
dependency order, including their library-module forms. No natural statement was
changed, and no edge case or scalar compatibility was omitted.

## Validation

`scompile.py Q90 lem-trf-lci-pointwise-criterion` with both delivered Lean files passed
cleanly (both definitions and theorem module; approximately 1.4 and 1.9 seconds in the
library-module checks). All variables and universes are explicit with
`set_option autoImplicit false`. The only postponed proofs are the two named theorems
of the item.

## Exact search records

```jsonl
{"t": "2026-10-17T23:48:55Z", "tool": "leansearch", "query": "A finite type algebra over a field is a local complete intersection if and only if all local rings at prime ideals are complete intersection local rings", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["Algebra.QuasiFinite.iff_finite_primesOver", "Algebra.QuasiFinite.casesOn", "Algebra.QuasiFinite.recOn", "Algebra.finite_of_essFiniteType_of_isAlgebraic", "Algebra.FiniteType.of_span_eq_top_source", "AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType", "Algebra.QuasiFinite.of_isIntegral_of_finiteType", "AlgebraicGeometry.instLocallyOfFiniteTypeOfLocallyOfFinitePresentation"], "digest": "14b4d190afb104db"}
{"t": "2026-10-17T23:48:56Z", "tool": "loogle", "query": "Algebra.IsLocalCompleteIntersection, IsRegularLocalRing", "sub": "", "ok": true, "n_hits": 0, "note": "loogle: unknown identifier 'Algebra.IsLocalCompleteIntersection'", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-17T23:48:56Z", "tool": "grep", "query": "CompleteIntersection|complete.intersection", "sub": "RingTheory", "ok": true, "n_hits": 1, "note": "", "top": ["Mathlib/RingTheory/Extension/Presentation/Basic.lean"], "digest": "08e65e9beea7152f"}
{"t": "2026-10-17T23:48:59Z", "tool": "leanfinder", "query": "local complete intersection scheme pointwise criterion regular local quotient finite regular sequence", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["Algebra.smoothLocus", "Algebra.IsSmoothAt", "AlgebraicGeometry.isSmoothOfRelativeDimension_iff", "AlgebraicGeometry.isSmooth_iff", "Algebra.isOpen_smoothLocus", "AlgebraicGeometry.IsSmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension", "AlgebraicGeometry.IsSmooth.exists_isStandardSmooth", "AlgebraicGeometry.instHasRingHomPropertyIsSmoothLocallyIsStandardSmooth"], "digest": "910ea01b8c4c84b5"}
{"t": "2026-10-17T23:49:55Z", "tool": "leansearch", "query": "A complete intersection local algebra over a field is a quotient of a regular local essentially finite type algebra by a finite regular sequence", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["Algebra.QuasiFinite.casesOn", "Algebra.QuasiFinite.recOn", "Algebra.instEssFiniteTypeQuotientIdeal", "Algebra.QuasiFinite.instQuotientIdeal", "Algebra.EssFiniteType.mk", "instIsIntegralQuotientIdeal", "Algebra.QuasiFinite.of_isIntegral_of_finiteType", "Ideal.iInf_pow_smul_eq_bot_of_isLocalRing"], "digest": "fb236100cf64d4d1"}
{"t": "2026-10-17T23:50:06Z", "tool": "leanfinder", "query": "complete intersection local ring over a field definition", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["Algebra.IsSmoothAt", "Algebra.IsStandardSmoothOfRelativeDimension", "tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain", "Algebra.Smooth.exists_span_eq_top_isStandardSmooth", "Algebra.IsStandardSmooth", "Algebra.IsEtaleAt", "Algebra.IsSmoothAt.exists_notMem_isStandardSmooth", "Algebra.Presentation.localizationAway_dimension_zero"], "digest": "8c5e517c1c654590"}
{"t": "2026-10-17T23:50:06Z", "tool": "grep", "query": "IsCompleteIntersectionLocal|CompleteIntersectionLocal|complete intersection local", "sub": "RingTheory", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
```
