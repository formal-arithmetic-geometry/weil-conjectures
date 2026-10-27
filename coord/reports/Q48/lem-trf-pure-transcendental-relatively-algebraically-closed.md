## Worker report

The module `Sheaf.FieldTheory.FinitePurelyTranscendentalConstants` states
`Algebra.exists_algebraMap_eq_of_isAlgebraic_of_finite_purelyTranscendental`.
Its only theorem proof is `sorry`, as required for stage 2. It adds no definitions,
new nodes, dependency modules, or changes to the mathematical statement. The node
copy changes only `lean`.

### Statement correspondence

- “Let L/k be a field extension” is `{k : Type u} {L : Type v} [Field k]
  [Field L] [Algebra k L]`. The structure embedding is `algebraMap k L`.
  The two universes are independently and explicitly declared.
- “For a finite integer r >= 0 there is a k-isomorphism” is the hypothesis
  `htrans : ∃ r : ℕ, Nonempty (L ≃ₐ[k] FractionRing (MvPolynomial (Fin r) k))`.
  A natural number is exactly a finite nonnegative integer. `Nonempty` asserts
  the existence of the algebra equivalence, without choosing it or supplying
  extra structure. `AlgEquiv` commutes with the given structure maps, so the
  isomorphism is over k, not just an abstract field isomorphism.
- “k(u_1,...,u_r), where the u_i are algebraically independent, and the right
  hand side is the fraction field of k[u_1,...,u_r]” is precisely
  `FractionRing (MvPolynomial (Fin r) k)`. The r formal indeterminates are
  algebraically independent over k. An isomorphism from any given independent
  family to this standard presentation is exactly the usual renaming of
  indeterminates, not an additional assumption. Conversely, the inverse images
  of the formal indeterminates under the given equivalence provide the family
  in L. `AlgebraicIndependent.aevalEquivField`, read in
  `Mathlib.RingTheory.AlgebraicIndependent.Adjoin`, records this equivalence
  with the intermediate-field presentation.
- “Thus L/k is purely transcendental” describes the same hypothesis; it is not
  a second independent assumption. The project's
  `Algebra.IsPurelyTranscendentalExtension` is imported and reused as the
  meaning of that phrase; the docstring explains that the displayed presentation
  is its finite-variable case. There is no private replacement of this predicate.
- “For every alpha in L satisfying a nonzero polynomial with coefficients in k”
  is `{α : L} (hα : IsAlgebraic k α)`. The actual Mathlib definition is
  `∃ p : Polynomial k, p ≠ 0 ∧ Polynomial.aeval α p = 0`; thus no monicity,
  separability, degree bound or nonzero-alpha hypothesis has been added.
- “There exists a in k whose image is alpha” is
  `∃ a : k, algebraMap k L a = α`.
- The explicit r = 0 clause is included because the existential ranges over all
  natural numbers, and `Fin 0` is empty. The zero-variable polynomial ring is
  k and its fraction field is k. No `Nonempty (Fin r)` or `0 < r` is imposed.

### Dependencies read and used

The full source signatures and docstrings of the recorded interfaces were read.

- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`.
  The Field/Algebra binders and `algebraMap` use this interface directly.
- `def-kun-transcendence-degree`: `Algebra.trdeg` in
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`, imported publicly as recorded.
  This node also supplies algebraic independence; its actual definition
  `AlgebraicIndependent` in `...AlgebraicIndependent.Defs` is injectivity of
  multivariate evaluation. No transcendence-degree bound occurs in this item.
- `def-trf-purely-transcendental-extension`:
  `Algebra.IsPurelyTranscendentalExtension` in
  `Sheaf.FieldTheory.PurelyTranscendentalExtension`, imported publicly. Its data
  is `∃ t : Set L, AlgebraicIndependent k (fun x : t ↦ (x : L)) ∧
  IntermediateField.adjoin k t = ⊤`. The finite fraction-field presentation
  in this item specializes this existing notion without redefining it.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`,
  `MvPolynomial.aeval`, and `MvPolynomial.algHom_ext`, in
  `Mathlib.Algebra.MvPolynomial.Basic` / `...Eval`. The standard polynomial
  algebra in the statement is available through the public statement imports.
- `def-weil-pbc-normal-ring`: `IsIntegrallyClosed` in
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`. This is a plain proof
  import; normality is not a hypothesis on k or L beyond their being fields.
- `lem-weil-pbc-polynomial-ring-normal-domain`: the Mathlib match
  `instIsIntegrallyClosedPolynomialOfIsDomain` in
  `Mathlib.RingTheory.Polynomial.IsIntegral` (Stacks 030A), imported for the proof.
- `def-weil-polynomial-ring`: `Polynomial` in
  `Mathlib.Algebra.Polynomial.Basic`, used in the actual definition of
  `IsAlgebraic`, publicly imported via `Mathlib.RingTheory.Algebraic.Defs`.
- `lem-trf-mvpolynomial-divisor-nonzero-constant`: the Mathlib match
  `MvPolynomial.dvd_C_iff_exists` in `Mathlib.Algebra.MvPolynomial.NoZeroDivisors`,
  imported for the proof. Its unrestricted variable type, nonzero-constant
  hypothesis and existential divisor conclusion were read in full.

All recorded proof dependencies that have a declaration are imported, with plain
imports for dependencies needed only by the eventual proof. No import cycle is
introduced. The module docstring names the source; the theorem docstring carries
all four DAG proof steps, including the reductions for zero variables and zero
alpha, the finite normality induction, polynomial normalization, integral
closedness, and the nonzero-constant divisor argument. The source proof at
`literature/stacks-project/more-morphisms.tex`, Tag 057K, was read, including the
paragraph beginning “Let T be the connected component”. As the DAG already
records, that passage uses the field fact implicitly; the expanded field proof
is agent-origin, not a proof quoted verbatim from Stacks.

### Edge cases checked before writing

- Empty variable set: r = 0 remains allowed; the statement reduces to an
  isomorphism with k, under which every element is a scalar.
- Alpha = 0: it is included and is the image of 0. The proof plan separates
  this case before using a nonzero constant coefficient.
- Finite or imperfect base field and positive characteristic: the proof only
  uses field operations, normality of polynomial rings and the stated divisor
  lemma; there is no assumption that k is infinite, perfect or separably closed.
- Arbitrary different universes for k and L: the algebra equivalence supports
  different universes, so no extra size equality excludes an extension.
- Nonalgebraic rational functions: no conclusion is asserted for these; the
  `IsAlgebraic` hypothesis requires a nonzero annihilating polynomial.
- The trivial ring is correctly excluded by `Field`; this is already implicit
  in the original notion of field extension.

No statement dispute or node fault was found. The referenced example
`Sheaf.CategoryTheory.CompactObject` was read and is currently a withdrawn module;
its node now points to `WeilConjectures.CategoryTheory.CompactObject`. The new
module follows the current mandatory module/public-import/exposed-section header.

### Searches (2026-10-24)

The prescribed `msearch.py Q48 <item>` wrapper was used for all search services.

- LeanFinder: “The base field is relatively algebraically closed in a finite
  purely transcendental extension”: eight hits, including
  `IsAlgClosed.isAlgClosure_of_transcendence_basis`,
  `IsTranscendenceBasis.isAlgebraic_field` and algebraic-closure constructions.
  None states that algebraic elements of a finite rational function field are
  scalars.
- Loogle: `AlgebraicIndependent, IsAlgebraic`: zero hits.
- Mathlib grep: `IsAlgClosedIn|isAlgebraic.*iff|relatively.*closed` in
  `FieldTheory`: 25 hits, mostly change-of-base algebraicity and algebraic-closure
  membership results; no exact match.
- LeanSearch: “Algebraic elements of the fraction field of a multivariate
  polynomial ring over a field are scalars”: eight hits. In particular,
  `IsFractionRing.isAlgebraic_iff` changes a coefficient domain to its fraction
  field, and `isAlgebraic_of_isFractionRing` concerns fractions of an integral
  extension. These have different hypotheses and conclusions.
  `AlgebraicIndependent.aevalEquivField` gives the presentation but not the
  constant-field result.
- Direct Mathlib source search in `FieldTheory/RatFunc/IntermediateField.lean`
  found `RatFunc.transcendental_of_ne_C`. Its full signature covers a single
  variable only, so it is not this finite-multivariable statement.
- `rg -n 'isAlgClosedIn|IsAlgClosedIn|pure.*[Tt]ranscend|algebraic.*constant'`
  over `lean/WeilConjectures` and `lean/Sheaf` found the existing purely
  transcendental definition, geometric consumers, and unrelated algebraic
  constant constructions. No declaration states this field-theoretic lemma.
- The prescribed node-id search in `lean/WeilConjectures` found no occurrence.
- The proposed full declaration name was searched in Mathlib, both project
  source roots and `dag/lean_names_upstream.json`; no collision was found.

### Validation

`scompile.py Q48 <item> lean/Sheaf/FieldTheory/FinitePurelyTranscendentalConstants.lean`
compiled both the sandbox view and the actual library module successfully against
the live published build. The reported times were 1.1 and 1.2 seconds, with no
errors or warnings. All variables and universes are explicitly bound, and the
only postponed proof is the named theorem belonging to this DAG node.

## Second reading by Q48

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
