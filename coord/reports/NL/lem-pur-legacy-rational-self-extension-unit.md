## Worker report

Existing declaration: `WeilConjectures.rationalConstructibleScalarUnit` in
`Sheaf.Paper.ScalarExtensionComposition`, source lines 1330–1337. No Lean module
is added: this declaration already supplies the natural-isomorphism witness
whose existence the item asserts. The item's node is changed only in `lean`.

### Hypotheses and clauses

- The global datum is the section parameter `D : FiniteFieldDatum.{d}`;
  its fields include the prime `p`, positive exponent, finite base field and
  algebraic closure. The independent datum universe `d` is retained.
- The coefficient prime is `l : ℕ` with `[Fact l.Prime]`, and the characteristic
  exclusion is the parameter `hl : l ≠ D.p`.
- The finite extension is `E : Type u` with `[Field E]`,
  `[Algebra (Padic l) E]` and `[FiniteDimensional (Padic l) E]`.
- The scheme is `Y : AlgebraicGeometry.Scheme.{u}`. No map to `D.k`, finite-type
  hypothesis, nonemptiness, or geometric restriction is required. Scheme and
  coefficient universes are those of the precise legacy presentation named by
  the node, rather than additional restrictions on a different presentation.
- The integral category underlying `rationalConstructibleCategory D l hl E Y`
  is literally `boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y`.
  In `DerivedCompleteIntegralDetailed.lean:38–63`, this is the full subcategory
  for `IsDerivedComplete l E Y D hl K` and `∃ r s : ℤ, r ≤ s ∧ ∀ n : ℕ, …`.
  For each positive power `n + 1`, the first conjunct is
  `intrinsicFiniteTorsionConstructible … ((integralDerivedReduction … n).obj K)`;
  the other conjunct bounds every cohomological support degree between `r` and
  `s`. Thus the same finite interval works for all positive powers.
- `RationalizationKaroubi.lean:40–44` defines the legacy rational category as
  `ScalarLocalization` of that exact integral category at
  `Padic.coefficientExtensionUniformizer l E`. This is the raw Hom scalar
  localization, with unchanged objects and no Karoubi completion.
- The source of the recorded natural isomorphism is literally
  `rationalScalarExtension D l hl E Y E (AlgHom.id (Padic l) E)`.
  `RationalizationKaroubi.lean:133–160` specifies its object map by the actual
  `constructibleIntegralScalarExtension`, and its Hom map by extension of the
  integral arrow and the coefficient-field inclusion. For the identity inclusion
  the scalar coordinate is unchanged.
- Its target is literally `𝟭 (rationalConstructibleCategory D l hl E Y)`.
  The Lean `≅` between these functors is a natural isomorphism, so the existing
  definition gives the requested witness `u_E`, including inverse and naturality.
- No comparison with another constructibility predicate occurs in this signature.
  In particular the `sf…` categories currently recorded on two dependencies are
  not substituted for the explicitly requested legacy categories.

### Dependencies and source inspection

Read every statement dependency's complete statement and Lean record. Read the
recorded declarations and docstrings in the following modules:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; it publicly retains the original
  coefficient fields, integer rings, uniformizers and quotients.
- `Sheaf.Paper.SfIntegralConstructible`:
  `WeilConjectures.sfIntegralConstructible` and
  `WeilConjectures.sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`:
  `WeilConjectures.sfRationalConstructibleCategory` and its completed scalar
  extension interface.

The last two records expose the intrinsic presentations of their nodes' notions.
The item explicitly fixes the older presentations. The existing witness already
has those older types, provided by `Sheaf.Paper.DerivedCompleteIntegralDetailed`
and `Sheaf.Paper.RationalizationKaroubi`, and consequently needs no transport,
new definition, dependency repair, or assertion equating the predicates.

Also read the existing unit's implementation and its restricted integral unit
and rational ordinary unit normalization, and the actual legacy functor formulas.
The isomorphism is the inverse of `rationalOrdinaryComparison` followed by
`rationalOrdinaryScalarUnit`. The source's use in
`AlgebraicallyClosedCoefficients.lean:393–398` is exactly the legacy unitor.
The latest blueprint unit `sk-thm-sfb-qlbar-two-colimit`, clause 4, gives the
finite-stage categorical context; the node explicitly retains the old argument,
without identifying it with the modern coefficient category.

### Edge cases

Checked the empty scheme, the zero complex, the identity extension `E = L`,
positive reduction level one, and arbitrary common finite cohomological intervals.
None is excluded by the witness. In particular the identity coefficient map is
supplied literally, not an arbitrary endomorphism, and no completeness condition
is dropped: it is part of the legacy integral objects. No assumption that `Y`
is over the finite-field closure is introduced. No new `sorry` is added; this
stage records an existing declaration and does not claim its proof closure is
axiom-free.

### Searches

- `msearch.py … leanfinder`, query: "Completed integral scalar extension along
  the identity coefficient field followed by raw rationalization is naturally
  isomorphic to the identity functor". Eight hits, headed by
  `ModuleCat.extendScalarsId` and its coherence lemmas. These ordinary-module
  statements do not describe the legacy completed rational functor.
- `msearch.py … loogle`, query: `ModuleCat.extendScalarsId`. Nine hits, all
  ordinary module extension/coherence interfaces; no exact Mathlib match.
- `msearch.py … grep`, query: `rationalConstructibleScalarUnit|extendScalarsId`.
  Six Mathlib hits in `ModuleCat/Pseudofunctor.lean` and
  `ModuleCat/ChangeOfRings.lean`; no completed-derived rational unit.
- `rg` of the exact unit name and item ID in `lean/WeilConjectures`: no hits.
- `rg` in `lean/Sheaf` found the exact witness in
  `Paper/ScalarExtensionComposition.lean:1333`, together with its actual use by
  `Paper/AlgebraicallyClosedCoefficients.lean:398`. Opened its full signature,
  section binders, docstring and body, and its category and functor definitions.
- `rg` of `dag/lean_names_upstream.json` for the unit name: no hit.

No statement fault, disputed clause, new node, or dependency module is needed.

### Validation

The prescribed delivery wrapper checks the existing declaration by a server-side
Lean `#check` through `scompile.py`, and runs the maintainer preflight. Results
are recorded below after validation.

Dry run passed: `deliver2.py NL lem-pur-legacy-rational-self-extension-unit
--no-push` reported `OK (dry run)` at commit `688bd59761f`; server compilation
and preflight both passed. No new Lean files require compilation.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
