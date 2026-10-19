## Worker report

The module `Sheaf.Paper.FiniteCoefficientFlatModel` states the whole node in four
named theorems, each with `sorry` as its entire proof. It introduces no definitions,
no instance, and no chosen map. The natural-language statement is unchanged.
The signatures use `set_option autoImplicit false` and explicitly bind universe `u`.

Clause-by-clause correspondence:

- The global finite-field datum is `D : WeilConjectures.FiniteFieldDatum.{u}`.
  The prime is `l : ℕ` with `[Fact l.Prime]`; `_hl : l ≠ D.p` is retained in
  every theorem. The finite extension is `E : Type u` with `[Field E]`,
  `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]`.
- The positive integer level is `n : ℕ` with `hn : 1 ≤ n`. The coefficient ring
  is the existing `Padic.coefficientExtensionRing l E n`, namely the recorded
  quotient of the valuation ring by the chosen uniformizer to the nth power.
  No arbitrary finite coefficient ring is substituted for it.
- The scheme is `T : Scheme.{u}`. Invertibility of l is
  `[∀ x : T, Invertible (l : T.residueField x)]`, the existing project convention.
  There is no Noetherian assumption in either equivalence.
- In `AlgebraicGeometry.Scheme.finiteCoefficient_torAmplitude_iff_flatModel`,
  `K : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n)` is
  exactly the recorded derived category of modules over the constant ring sheaf.
  `_hK : intrinsicFiniteTorsionConstructible l E n hn T K` imposes finite support
  of cohomology and the recorded finite-stratification constructibility on every
  cohomology sheaf. The intrinsic predicate is the dependency's current recorded
  declaration; the separate binders retain the global datum omitted by that predicate.
- The ordered interval is `(a b : ℤ) (_hab : a ≤ b)`. Condition (i) is
  `HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E n) K a b`.
  Its existing definition tests all degree-zero module sheaves using all K-flat
  resolutions of representatives isomorphic to K; it requires precisely the
  derived-tensor cohomology vanishing outside the ordered interval.
- Condition (ii) quantifies over `P : CochainComplex (proEtaleRingModules T
  (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) ℤ`.
  `∀ q, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
  (R := proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)) (P.X q)`
  is termwise flatness. This is the recorded exactness of the sheafified sectionwise
  tensor functor. Tensor is right exact and symmetric, so this is equivalently
  preservation of injections by tensor with each term, as the node requests.
  `∀ q, q < a ∨ b < q → IsZero (P.X q)` is support in [a,b] and hence boundedness.
  `Nonempty (K ≅ DerivedCategory.Q.obj P)` is the requested derived isomorphism.
  `↔` retains both directions.
- `AlgebraicGeometry.Etale.finiteCoefficient_hasTorAmplitude_iff_flatModel`
  is the corresponding small-etale equivalence. The ambient category is
  `DerivedCategoryModule (ULift.{u+1} (Padic.coefficientExtensionRing l E n)) T`.
  The canonical `ULift` carries the ring structure transported by `ULift.down`;
  it is the very same ring at the coefficient universe required by the existing
  etale `ModuleCat` API. It adds no size equality or algebraic hypothesis.
  The scheme/site universe remains u. Bounded constructibility is exactly
  `Etale.DerivedCategory.isBoundedConstructible`, with its finite-ring argument
  provided by `Padic.finite_coefficientExtensionRing` and `Equiv.ulift.finite_iff`.
  There is no finite-ring assumption on the caller. Tor amplitude is
  `Etale.DerivedCategory.hasTorAmplitudeIn`. The model is a cochain complex of
  `Sheaf T.smallEtaleTopology (ModuleCat.{u+1} (ULift ...))`.
  `IsBoundedFlatComplex` means termwise `ObjectProperty.flat` and zero outside
  [a,b], with precisely the same derived isomorphism and no constructibility
  imposed on its terms.
- `AlgebraicGeometry.Etale.finiteCoefficient_exists_flatConstructibleModel`
  adds exactly `[IsNoetherian T]` and the amplitude hypothesis `_hTor` in the
  specified interval. It returns such a bounded flat complex and also
  `∀ q, Scheme.IsConstructibleEtaleModuleSheaf (P.X q)`. This is the dependency's
  recorded finite-constant-value constructibility predicate, not a substitution
  of the upstream finite-stalk predicate. Again, the isomorphism starts at K.
- `AlgebraicGeometry.Etale.finiteCoefficient_exists_boundedFlatConstructibleModel`
  writes out the final 'in particular': a bounded constructible K with one
  ordered interval of Tor amplitude has a flat constructible model in some
  ordered interval. The finite-Tor hypothesis is one common interval for every
  test sheaf, not a bound depending on the sheaf. This theorem does not claim
  bounded constructibility alone implies finite Tor amplitude.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (publicly importing
  `Sheaf.NumberTheory.Padics.CoefficientExtension`):
  `Padic.coefficientExtensionRing` and `Padic.finite_coefficientExtensionRing`.
  The construction uses the recorded valuation ring, maximal ideal and uniformizer.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`;
  `Sheaf.AlgebraicGeometry.ProEtaleOperations`:
  `AlgebraicGeometry.Scheme.proEtaleRingModules`; the constant sheaf is the existing
  `AlgebraicGeometry.Scheme.proEtaleConstantRing`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`:
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, with the correct explicit site and ring argument.
  The current server source was also checked through `scompile.py --source`.
- `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`:
  `AlgebraicGeometry.Etale.IsBoundedFlatComplex` and the recorded
  `AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatModel`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`;
  `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` imports the recorded
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.
- `Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel` (proof import):
  `AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel`.
  Read its complete signature and six-step proof plan, also via server source.
- The pro-etale attachment's complete source signature and docstring were read:
  `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_iff_exists_flatModel`
  in `WeilConjectures.SixFunctors.ProEtale.Derived.FlatModel`. It states the
  corresponding theorem in the upstream ModuleCat-valued sheaf encoding with
  etale-origin bounded constructibility. It is not used as if it directly typed
  the project's ringed-site category or its intrinsic constructibility predicate.
  The docstring gives the resolution/truncation proof on the actual category.
  Importing that upstream module alongside the current project interfaces fails
  with duplicate `AlgebraicGeometry.ProEtale.«term(_)_*[_]»` declarations between
  the old and FiniteCoefficient UpperLowerStar.Defs modules. Accordingly its
  incompatible proof import is omitted; the common site-independent flat-model
  machinery remains imported through the etale FlatModel module. No library
  source or dependency record was changed to conceal this conflict.

The added stmt_deps are only already landed definition nodes which own the exact
interfaces appearing explicitly in these statements. The original three statement
and proof dependencies remain in the node; no dependency is removed or redefined.
No new nodes, dependency modules, statement correction, or disputed statement.

Edge cases checked before writing:

- a=b permits a single possibly nonzero flat term; no strict inequality is added.
- Negative endpoints are allowed because both endpoints and all degrees use ℤ.
- K=0 permits the zero model; nothing requires a nonzero complex or term.
- The empty scheme is allowed; pointwise invertibility is then vacuous as it should be.
- n=1 is included; n=0 is excluded exactly by the source's positive-level hypothesis.
- E need not be an algebraic closure, Galois or unramified extension; the finite
  dimensional field-extension assumptions are exactly the coefficient convention.
- No Noetherian hypothesis leaks into the two equivalences; it is present only
  for termwise constructibility and its finite-Tor consequence.
- Pro-etale site object and morphism universes retain sizes u+1 and u respectively.
  The etale ULift is explicit; no same-universe restriction is imposed on the site.
- The general equivalences require flat terms, not flat constructible terms.
  Termwise constructibility is added exactly in the stated Noetherian variant.

Searches for existing notions/statements:

- `msearch.py`, LeanFinder: 'A bounded constructible complex of sheaves has Tor
  amplitude in an interval if and only if it has a bounded flat model'. Eight hits
  were generic derived t-structure support/representative lemmas, including
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`; none states the flat model.
- `msearch.py`, Loogle: `torAmplitudeIn, IsBoundedFlatComplex`. No hits, unknown
  identifier `torAmplitudeIn`.
- `msearch.py`, Mathlib grep: `flatModel|IsBoundedFlatComplex`. Zero hits.
- `msearch.py`, LeanSearch: 'A bounded complex of sheaves of modules with Tor
  amplitude in [a,b] is isomorphic to a complex of flat sheaves supported in [a,b]'.
  The service returned Internal Server Error; this is recorded as unavailable.
- `rg` through upstream WeilConjectures for `lem-sf-flat-model`, `flatModel`,
  `FlatModel`: found the two upstream FlatModel modules and their partial clauses,
  read in full. Neither states this whole node in the actual ringed-site category
  with this coefficient datum and constructibility convention.
- `rg` through project `lean/Sheaf` for `flatModel|IsBoundedFlatComplex`: found the
  recorded finite-value etale constructible theorem, reused as the proof interface.
- `rg` through Mathlib, upstream and project for all four proposed declaration
  names: no existing declarations. No private copy of a notion was introduced.

Validation: the complete four-declaration module compiled through `scompile.py`
with no errors or warnings. The first dry run found a truncated lean.statement metadata string (the extraction
stopped at a named argument); it was repaired to the full verbatim signature.
The second-reading section is intentionally left to the independent reader.

## Second reading by Q27

I independently opened the DAG statement, this module, the three flat-model dependency
nodes and their declarations, and the definition-node records and implementation sources
used by the signatures. The blueprint source is absent under this read-only clone's
`literature/`; I read its exact archived copy at
`/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/sec-smooth-purity/sk-lem-sf-flat-model/lem-sf-flat-model.md`.
Its hypotheses and three clauses agree with the node. I also read the archived Stacks
`sites-cohomology.tex`, definition-tor-amplitude and lemma-tor-amplitude (including the
preceding last-one-flat lemma), `sites-modules.tex`, definition-flat(3), and
`etale-cohomology.tex`, section-more-constructible (095M). The latter assumes a Noetherian
coefficient ring; the actual coefficient quotient is finite, hence meets that condition.
The constructible resolution argument assumes Noetherianity of the scheme, exactly where
the two corresponding Lean declarations impose it. No source hypothesis needs adding.

Object/hypothesis/conclusion checklist, with verdicts:

1. Global finite-field datum: `D : WeilConjectures.FiniteFieldDatum.{u}` retains the
   characteristic prime, positive exponent, finite base field and chosen algebraic closure.
   I opened `Sheaf.Paper.FiniteFieldFiber`, including the structure fields. PASS.
2. Coefficient prime and finite extension: `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`
   and `(E : Type u) [Field E] [Algebra (Padic l) E]
   [FiniteDimensional (Padic l) E]` occur in all four declarations. No algebraic-closure,
   Galois or unramified restriction on E occurs. PASS.
3. Positive level and actual ring: `(n : ℕ) (hn : 1 ≤ n)` and
   `Padic.coefficientExtensionRing l E n`. I read CoefficientExtension and
   CoefficientExtensionFinite: this is the quotient of the recorded valuation ring by
   `(span {uniformizer})^n`; the named finiteness theorem supplies the finite-ring argument.
   The quotient is not replaced by an arbitrary finite ring. PASS.
4. Scheme with invertible l: `(T : Scheme.{u})`
   `[∀ x : T, Invertible (l : T.residueField x)]`. This is pointwise invertibility,
   equivalent to invertibility of the corresponding constant section. There is no
   finite-type, separatedness or Noetherian requirement in the equivalences. PASS.
5. Pro-etale complex and bounded constructibility: `K : proEtaleDerivedCategory T ...`
   and `_hK : intrinsicFiniteTorsionConstructible l E n hn T K`. I unfolded the
   intrinsic predicate: finite support of cohomology and constructibility of each
   cohomology sheaf, in the same category as `DerivedCategory.Q.obj P`. I read
   ProEtaleDerivedCategory, ProEtaleOperations and ProEtaleConstructibleSheaf. The latter
   uses finite locally closed scheme strata, local constancy after the canonical constant
   coefficient inverse image, and finite geometric module stalks. I also opened the actual
   upstream `Topology.Stratification`: its `isConstructible_stratum` field supplies
   constructibility of the parts, inherited by LocallyClosedStratification (despite the
   latter module's older prose saying it imposes no constructibility). PASS.
6. Ordered integer endpoints: `(a b : ℤ) (_hab : a ≤ b)` precede both sides of each
   equivalence and the fixed-interval constructible assertion. PASS.
7. Condition (i): `HasProEtaleTorAmplitude T ... K a b`. Its implementation tests every
   degree-zero module sheaf and every degree outside the interval on all K-flat
   resolutions of all representatives of K, using the recorded derivedTensor. Resolution
   existence and invariance give precisely the requested derived-tensor vanishing; no
   arbitrary tensor or representative is fixed as an extra hypothesis. PASS.
8. Condition (ii): the existential `P : CochainComplex (proEtaleRingModules T
   (proEtaleConstantRing T ...)) ℤ`, termwise `SheafOfModules.IsFlatOnSite`,
   `∀ q, q < a ∨ b < q → IsZero (P.X q)`, and
   `Nonempty (K ≅ DerivedCategory.Q.obj P)`. FlatOnSite is exactness of the sheafified
   sectionwise tensor functor. Tensor is right exact and symmetric, so this is equivalent
   to the node's preservation of injections by left tensor. Support implies boundedness;
   no termwise constructibility is added to this equivalence. The connective is `↔`,
   with the same universally fixed a,b on both sides. PASS.
9. Small-etale equivalence: `Etale.finiteCoefficient_hasTorAmplitude_iff_flatModel`
   repeats the coefficient and scheme hypotheses and uses `DerivedCategoryModule`,
   `DerivedCategory.isBoundedConstructible`, `DerivedCategory.hasTorAmplitudeIn`,
   `IsBoundedFlatComplex`, and the localization isomorphism. I read the bounded
   constructibility definition, its IsConstructibleEtaleModuleSheaf dependency,
   the source Coefficients.hasTorAmplitudeIn, and FlatModel.IsBoundedFlatComplex.
   The predicates respectively mean constructible bounded cohomology, tensor testing
   against every module sheaf in degree zero, and exact tensor with every term plus
   zero terms outside [a,b]. `ObjectProperty.flat` requires both tensor directions to
   be exact; symmetry makes these equivalent. PASS.
10. Coefficient size on the etale site: `ULift.{u + 1} (Padic.coefficientExtensionRing
    l E n)` has its transported CommRing structure. The explicit
    `Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing ...)` supplies
    finiteness, not an additional hypothesis. This is the same coefficient ring and
    retains all its modules via the canonical coefficient equivalence. The site's
    object/morphism universes remain u+1/u; there is no imposed equality. PASS.
11. Constructible variant: `Etale.finiteCoefficient_exists_flatConstructibleModel`
    adds `[IsNoetherian T]` and `_hTor` for the fixed ordered interval, and concludes
    the same bounded flat P with `∀ q, Scheme.IsConstructibleEtaleModuleSheaf (P.X q)`
    and `Nonempty (K ≅ Q.obj P)`. No bound or conclusion clause is dropped. I opened
    the recorded dependency EtaleFlatConstructibleModel: it uses exactly this
    finite-value predicate, with the opposite isomorphism orientation inverted. PASS.
12. Final consequence: `Etale.finiteCoefficient_exists_boundedFlatConstructibleModel`
    assumes bounded constructibility and `∃ a b, a ≤ b ∧ hasTorAmplitudeIn ... a b K`,
    then returns some ordered interval and such a model. The quantifiers require one
    common interval for all test sheaves. It does not claim finite Tor amplitude from
    boundedness alone. This is exactly the displayed D^b_ctf consequence. PASS.

Edge cases: a=b permits a single nonzero term; negative endpoints are allowed; K=0
admits a zero model; empty T is permitted and pointwise invertibility is then vacuous.
The constructibility partition permits a positive number of empty strata on the empty
scheme, so its auxiliary positive-stratum convention does not exclude this case.
n=1 is included and n=0 excluded exactly as the source requires. There is no index set
assumed nonempty in this module. The coefficient and scheme universes are the recorded
common universe convention, with the pro-etale site retaining its distinct object and
morphism universes. All universe and term variables are explicitly bound with
`autoImplicit false`.

Independent searches (different wording from the worker):

- `msearch.py ... leanfinder "A complex of sheaves of modules has Tor dimension in an
  integer interval exactly when it admits a flat representative concentrated in that
  interval"`: eight hits concerning projective/injective dimension, derived cohomology
  bounds and vanishing of Tor for projectives; no exact flat-model declaration.
- `msearch.py ... loogle "CochainComplex, ObjectProperty.flat"`: zero hits; the search
  service does not know the project's ObjectProperty.flat identifier.
- `msearch.py ... leansearch "For sheaves of modules, Tor amplitude in [a,b] is
  equivalent to an isomorphism with a bounded complex of flat sheaves supported in
  [a,b]"`: unavailable, Internal Server Error; no verdict inferred from the failure.
- `msearch.py ... grep "torAmplitudeIn_iff_exists|IsBoundedFlatComplex|flat_model"`:
  no Mathlib hits. Direct rg of Mathlib, upstream WeilConjectures and project lean/Sheaf
  with `flatModel|flat_model|flat.*representative|torAmplitudeIn_iff_exists`, followed
  by a narrower declaration search, found the generic categorical theorem, the two
  upstream FlatModel modules, the project's ordinary-ring TorAmplitudeFlatModel and
  the recorded etale finite-value constructible model theorem. I read the source
  signatures: the ordinary-ring statement has a different ambient category; the
  upstream pro-etale one has a ModuleCat-valued rather than ringed-site encoding and
  a different constructibility predicate; the upstream etale ones also use their
  source constructibility predicate. None directly states the complete four-clause
  node with the actual recorded predicates. Existing bounded-flat-complex and
  flatness notions are reused; no second definition was introduced.

No mathematical mismatch was found. No Lean signature, definition, node statement,
or dependency record was changed. There are no new nodes, sibling modules or
statement_change to audit. The intentional omission of the incompatible old pro-etale
FlatModel proof import remains documented in the worker report; the actual ringed-site
resolution/truncation proof is spelled out in the theorem docstring, and the shared
flat-model machinery is imported through the etale module. Each of the four theorem
proofs is exactly `sorry`, with source/blueprint docstrings and its clause's proof plan.
There are no hollow definitions, local notation, local instances, new axioms, or proved
auxiliary theorems. All lines meet the 100-character limit, declaration names are fresh,
and `lean.statement` equals the complete primary signature verbatim.

Validation: ran the prescribed scompile.py wrapper from this sandbox on
`lean/Sheaf/Paper/FiniteCoefficientFlatModel.lean`; both sandbox and library compilation
passed, with no errors or warnings (14.5 s and 18.5 s respectively). The only change
made by this second reading is this independent review report and the additional
search records. Delivery preflight and push results follow below.

Additional source confirmation: `scompile.py --source WeilConjectures.Topology.Stratification`
confirmed the same `isConstructible_stratum` field in the current server compilation source.
The required `deliver2.py Q27 lem-sf-flat-model --no-push` completed successfully:
`OK (dry run): commit 36800dea3a passes the preflight and compiles; nothing pushed`.
