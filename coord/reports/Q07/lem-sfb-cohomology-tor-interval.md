## Worker report

The new module `Sheaf.Paper.CohomologyTorInterval` states
`AlgebraicGeometry.ProEtale.torAmplitudeIn_of_cohomology_interval` with a single
`sorry` proof. It introduces no definitions. The node statement, dependencies,
and proof are unchanged. No repair note exists for this item.

The source is the current main-20261015 blueprint's
`sec-proetale-coefficients/sk-def-localizing-closure/`
`sk-def-localizing-closure-ctf-equals-bc.proof.md`, Complexes paragraph.
The node is the stated generalization of its common cohomology interval
`[-1,0]` to `[c,d]`. Its five-step proof is included in the theorem docstring.

Clause-by-clause correspondence:

- A scheme: `(X : Scheme.{u})`, with no quasi-compactness, separation,
  Noetherian, or other geometric hypothesis.
- An arbitrary commutative condensed ring: `(Λ : Profinite.CondensedRing.{u})`
  and `[IsCommMonObj Λ.X]`. The recorded abbreviation is exactly
  `Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})`; the scope
  `CategoryTheory.Obj` exposes its canonical `MonObj Λ.X` instance.
  This is not restricted to coefficients coming from a topological ring.
- The coefficient ring `Λ_X`: the existing `condensedRingObj Λ.X X` transports
  the ring structure along the point inverse image. It is the unbundled form
  of the recorded `coefficientRing X Λ`.
- `K ∈ D(Mod(Λ_X))`: the explicit `K` binder is the existing `DerivedCategory`
  of `CategoryTheory.Mod` over `condensedRingObj Λ.X X`. This uses precisely
  the internal-module encoding already selected by the Tor-amplitude dependency;
  that dependency identifies it with sectionwise module sheaves.
- Integers `a ≤ b`, `c ≤ d`: `(a b c d : ℤ)`, `(hab : a ≤ b)`,
  and `(hcd : c ≤ d)`. No sign condition on any endpoint is imposed.
- Cohomology zero outside `[a,b]`: `hK` quantifies over every integer `q`,
  and `q ∉ Set.Icc a b` implies
  `IsZero ((DerivedCategory.homologyFunctor _ q).obj K)`.
- The degree-zero cohomology module has Tor amplitude `[c,d]` for each
  `q ∈ [a,b]`: `hH` quantifies over precisely `q ∈ Set.Icc a b` and applies
  `DerivedCategory.torAmplitudeIn _ c d` to
  `(DerivedCategory.singleFunctor _ 0).obj
  ((DerivedCategory.homologyFunctor _ q).obj K)`.
- Conclusion: `DerivedCategory.torAmplitudeIn _ (a + c) (b + d) K`,
  exactly the requested sum of intervals.
- No constructibility assumption: none occurs in the binders. Importing the
  recorded well-definedness module does not impose its constructibility
  predicates on this theorem.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`
  (sk-def-sfb-condensed-ring).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`,
  `condensedRingObj`, `isCommMonObj_condensedRingObj`
  (sk-def-sfb-pulled-back-coefficients). Their full source definitions use the
  point inverse image and its monoidal functor; no replacement is introduced.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.singleFunctor`; and
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`
  (def-weil-abstract-derived-category).
- `Sheaf.Paper.ConstantModelTorAmplitude`:
  `AlgebraicGeometry.ProEtale.constantModelConstructibleFiniteTor_wellDefined`
  (det-def-sfb-constructible-tor-amplitude). The predicate this dependency
  specifies is `DerivedCategory.torAmplitudeIn`, defined in
  `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude` by tensor tests
  against every module in degree zero. Its full source was read.
  `homologyConcentratedIn` means both canonical t-structure bounds, equivalently
  zero cohomology outside the closed interval.
- Proof-only imports cover every remaining recorded proof dependency:
  `Sheaf.CategoryTheory.RingedSiteModules` (`CategoryTheory.ringedSiteModules`),
  `Sheaf.CategoryTheory.TruncationDescends`
  (`DerivedCategory.truncation_descends`),
  `WeilConjectures.CategoryTheory.TruncationTriangle`
  (`DerivedCategory.truncation_triangle`), and
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`
  (`AlgebraicGeometry.ProEtale.CondensedRing.derivedHom` and the publicly
  imported `CondensedRing.derivedTensor`). The tensor is the existing Layer-B
  relative derived tensor, definitionally the tensor used by `torAmplitudeIn`.

Edge cases checked before writing:

- `K = 0`, the empty scheme, and the zero coefficient ring are all admitted.
  Tensor tests and cohomology vanish in these cases.
- `a = b` reduces to a single module placed in degree `a`, with the expected
  Tor interval `[a+c,a+d]`; `c = d` is also allowed.
- A module in negative degree, for example `a = b = -2` and `[c,d] = [-1,0]`,
  gives `[-3,-2]`. This checks the cohomological sign: `M[-q]` is in degree q.
- For `[a,b] = [2,3]` and `[c,d] = [-1,0]`, the result is `[1,3]`, agreeing
  with the blueprint's `[a-1,b]` special case. Endpoints and interior zero
  cohomology terms are included. No lower bound of zero on degrees occurs.
- General non-qcqs schemes and non-topological condensed coefficients are
  retained, with `Ab.{u+1}` on the small pro-etale site. No universe equality
  or extra tensor structure is supplied as a hypothesis.

Searches for an existing statement (all on 2026-10-21):

- `msearch.py ... leanfinder` with query "A bounded complex whose cohomology
  modules all have Tor amplitude c through d has Tor amplitude a+c through b+d":
  8 hits, giving `DerivedCategory.IsGE`, `IsLE`, the corresponding `Q` facts,
  `CochainComplex.isLE_shift`, and a localized-shifted-Hom fact. No Tor bound.
- `msearch.py ... leansearch` with query "If a complex has cohomology only in
  degrees a through b and every cohomology object has Tor amplitude c through d,
  the complex has Tor amplitude a+c through b+d": 8 hits, including bounded
  representatives and shift formulas. None states the requested implication.
- `msearch.py ... loogle` with query `torAmplitudeIn, homologyConcentratedIn`:
  0 hits, reporting unknown identifier `torAmplitudeIn` in the search service.
  The project definitions were then inspected directly in the source.
- `msearch.py ... grep` with regex `torAmplitude|tor_amplitude|TorAmplitude`:
  0 Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for cohomology/Tor interval
  names and combinations, and for the proposed declaration name: no exact
  statement or name match. The item id also has no upstream source hit.
  The generic `TorAmplitude.lean` supplies the predicate and interval widening;
  `FlatModel.lean` supplies tensor bounds from an already known Tor amplitude,
  not this implication from the amplitudes of the individual cohomology modules.
  `ConstructibleFlatCohomologyTorBound.lean` concerns a specialized flat/adic
  constructible setting. None duplicates this arbitrary-coefficient assertion.

Validation: the prescribed `scompile.py Q07 lem-sfb-cohomology-tor-interval`
compiled both its sandbox check and the actual module against the published
live server library, with no errors or warnings (3.6 s and 3.4 s).
The file has explicit universe/variable binders and `autoImplicit false`,
no private definitions, file-local notation, or file-local instances;
all lines are at most 100 characters. The sole postponed theorem is the item
itself and its docstring contains the complete DAG proof. No node fault or
statement correction was needed.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
