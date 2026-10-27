## Worker report

Q23 stage 2, lem-trf-initial-diagram-stabilization. This is a fresh statement delivery,
not a new stage-1 split. The current live node is split and reviewed for Q78 on
2026-10-22, has no `lean` record, and is ready for stage 2. The preceding dispatch's
claim that a reviewed split forbids this stage-2 statement confused the two stages.
No reviewed statement, proof, proof dependencies, or stage-1 metadata is changed.

`Sheaf.RingTheory.InitialDiagramStabilization` states
`MonomialDiagram.exists_finiteDivisionTest`, with only `sorry` as its proof.
`Sheaf.RingTheory.SupportedHomogeneousDivision` supplies actual definitions for
its previously unstated first-vertex-supported division family and test predicate.
There are no auxiliary theorem sorries and no data obtained from a sorry.

Hypothesis and clause correspondence:

- The natural number of variables is `n : ℕ`; exponents are `Fin n →₀ ℕ`, Mathlib's
  encoding of N^n. The diagram is `D : Set (Fin n →₀ ℕ)`.
- `hD : IsMonotone D` contains exactly additive closure and the whole-coordinate
  moves from earlier to later variables. `a - single i (a i) + single j (a i)` is
  the node's displayed move, using coordinatewise natural subtraction.
- `s : ℕ` and `a : Fin s → Fin n →₀ ℕ` give the finite vertex list;
  `ha : IsOrderedVertexFamily D a` says its range is exactly the coordinatewise
  minimal elements (`Minimal`), with strict ascending `Finsupp.DegLex` order.
  The latter is degree first, then increasing-coordinate lex order, as checked
  from `Finsupp.DegLex` and `Finsupp.lex_def`. Strictness forbids duplicate vertices.
- The vertex degree is `(a i).degree`, Mathlib's sum of exponent coordinates.
  `quotientSupport a i` is exactly Delta_i: `a i + b` automatically lies in its
  own orthant, while no earlier vertex divides it. Divisibility of exponent
  vectors is coordinatewise `≤`, including zero coordinates.
- `DivisionIndex D a t` is a SUM of subtypes, not a set of polynomial values.
  The left subtype is `(i,b)` with `b ∈ quotientSupport a i` and
  `b.degree + (a i).degree = t`; the right subtype is `e ∉ D`, `e.degree = t`.
  `divisionFamily` sends them to `monomial b 1 * H i` and `monomial e 1`.
- The coefficient ring is any `A : Type u` with `CommRing A`, without
  `Nontrivial`, field, characteristic, or Noetherian assumptions.
  Each existential `b : ℕ` PRECEDES all coefficient rings, so its bound depends
  on the diagram and chosen list, never on A or H. The list is uniquely
  specified by D and its fixed degree-lex order, so this is the node's b(D).
- `IsFiniteDivisionTest` quantifies over all `H` with precisely
  `(H i).IsHomogeneous (a i).degree`. This is the Mathlib coefficient-support
  notion, not the assertion that its totalDegree equals the number: zero forms
  are allowed, just as in the node's coefficient-based definition.
- Polynomials are exactly Mathlib's `MvPolynomial`, with their existing
  `MvPolynomial.toMvPowerSeries` coefficientwise inclusion into `MvPowerSeries`.
  This represents the finite-support-series subring from the node; no alternate
  polynomial or series carrier is constructed.
- `SpansDegree` is equality of the span of the indexed family with the existing
  `MvPolynomial.homogeneousSubmodule`, so it means exactly spanning V_t.
- The first conjunct of `IsFiniteDivisionTest` is the propagation clause:
  `b ≤ q → SpansDegree ... q → ∀ t, q ≤ t → SpansDegree ... t`.
- Its second conjunct is `SpansDegree ... t → LinearIndependent A ...` in
  EVERY degree, without the restriction `b ≤ t`. Together with spanning V_t
  this says the given indexed family is a basis of V_t, including the zero ring.
  It does not assert merely that some unrelated basis exists.
- Its third conjunct says that all tests `t ≤ b` span iff `HasUniqueDivision`
  holds in every degree. The latter is `∃! c : DivisionIndex ... t →₀ A` with
  `Finsupp.linearCombination A (divisionFamily ...) c = P` for every homogeneous
  P. Group coefficients by vertex to obtain exactly the supported quotient
  polynomials, and group the remainder indices to obtain the remainder. Conversely
  such quotient polynomials and remainder determine the finitely supported c.
  For `t < d_i` there are no indices for i, forcing its quotient to zero without
  a spurious truncated subtraction degree condition.
- The main theorem's first conjunct is the complete assertion for `(D,a)`.
- Its second conjunct quantifies over every degree cutoff `d : ℕ`, using
  `prefixVertices a d` indexed by `{i // (a i).degree ≤ d}` with inherited order,
  and `generated` for the union of retained orthants. Earlier vertices for any
  retained i are all retained, so its quotient support is the original Delta_i.
  Each prefix gets its own bound, as the node's proof explicitly prescribes.
- Its third conjunct applies the whole assertion to `essentialVertices a`, which
  uses Mathlib's actual `Finsupp.subtypeDomain` restriction to
  `EssentialVariables a = {j // ∃ i, a i j ≠ 0}`. The diagram is generated by the
  restricted vertices, equivalently the restriction of D to those coordinates.
  It is quantified over all homogeneous forms there; in particular this includes
  the forms obtained by setting unused variables of any original H to zero.
- Its fourth conjunct repeats the essential-variable clause for EACH prefix,
  allowing a prefix to use fewer variables than the original diagram. No identity
  between original-variable and restricted-variable polynomial families is assumed.

Dependency declarations read and used:

- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`,
  `Mathlib.RingTheory.MvPowerSeries.Basic`; also its canonical polynomial inclusion
  `MvPolynomial.toMvPowerSeries` in the same module.
- The new definition node cites `def-weil-pbc-mv-polynomial-ring`:
  `MvPolynomial`, `Mathlib.Algebra.MvPolynomial.Basic` (available through the imports).
- `MvPolynomial.IsHomogeneous` and `MvPolynomial.homogeneousSubmodule`,
  `Mathlib.RingTheory.MvPolynomial.Homogeneous`, are used as given.
- `Minimal`, `Finsupp.DegLex`, `Finsupp.subtypeDomain`, `Submodule.span`,
  `LinearIndependent`, and `Finsupp.linearCombination` are existing Mathlib
  definitions. Their relevant signatures/docstrings and lexicographic conventions
  were read from the pinned Mathlib source.
- Proof-only imports retain the plan's `def-weil-pbc-free-module`
  (`Module.Free`, `Module.Basis`, `Mathlib.LinearAlgebra.FreeModule.Basic`) and
  `lem-weil-pbc-finite-module-surjective-endomorphism-bijective`
  (`OrzechProperty.bijective_of_surjective_endomorphism`, made applicable to a
  commutative ring through the imports of `Mathlib.RingTheory.FiniteType`).
  The diagram-face-exceptions proof dependency has no Lean declaration live,
  so there is no module for it to import yet; the maintainer can add that
  proof-only import when it is stated. Its mathematical input is fully recorded
  in the theorem docstring, which gives all ten proof steps of the live node.

Edge cases checked before writing and again against the definitions:

- `n = 0`: only the zero exponent exists. Degree zero is A; positive degrees
  are zero. The finite test can be zero. Both empty and full diagrams are covered.
- `s = 0`, `D = ∅`: no multiple indices; the remainder family is the monomial
  basis. Essential variables and every degree prefix are empty.
- `D = univ`: the unique vertex is zero; its quotient support is all exponents,
  and there are no remainder indices. If its constant form is not a unit,
  spanning need not hold, as required by the conditional theorem.
- Empty degree prefixes are permitted; zero vertices and degree-zero forms
  impose no artificial positivity condition. `d = 0` and `t = 0` are included.
- The zero ring is allowed; its module and all coefficient functions are
  singletons, so unique expansions and linear independence have the correct
  zero-ring meaning. No cancellation, invertible leading coefficient, or
  characteristic-zero assumption is added.
- Distinct indices remain distinct even when their polynomial values coincide;
  this is essential for the conditional basis assertion.

Searches:

- Required msearch leanfinder: "A monotone monomial diagram admits a finite
  degree test for unique supported homogeneous division over any commutative ring".
  Hits include `MonomialOrder.div` and `div_set`, which assume unit leading
  coefficients and give ordinary division, not this stabilization theorem.
- msearch loogle: `MvPolynomial.IsHomogeneous, MvPowerSeries.coeff, Module.Basis`;
  zero hits. The relevant individual definitions were then read in source.
- msearch grep: `monotone.?diagram|homogeneous.?division|initial.?exponent`
  in Mathlib/RingTheory; zero hits.
- msearch leansearch: "monotone diagram ordered minimal vertices supported
  homogeneous division"; eight hits on generic order minimality, no match.
- For the new definition node, leansearch and leanfinder with query
  "monotone monomial diagram supported homogeneous division family quotient
  support first dividing vertex finite degree test": hits on monomial division,
  Groebner division and homogeneous components; no matching definition.
  msearch grep `monotone.?diagram|homogeneous.?division|quotientSupport|DivisionIndex`
  in Mathlib/RingTheory: zero hits. The actual result records are retained
  verbatim in the new node's mathlib_searches, not invented search summaries.
- `rg` of WeilConjectures, Sheaf and dag/lean_names_upstream.json for
  MonomialDiagram, IsFiniteDivisionTest, quotientSupport, IsOrderedVertexFamily
  and DivisionIndex: no match. An initial broader project search for monotone
  diagrams, homogeneous division and this item's blueprint id also found none.
- DAG text searches found the existence statements `lem-trf-generic-monotone-diagram`,
  `lem-trf-regular-hilbert-coefficient-data`, `lem-trf-formal-hilbert-stratum-minors`
  and the face-exceptions lemma, but no definition node for the indexed support
  family or test predicate. They are not duplicate definitions. `blueprint_refs.py
  search 'homogeneous division'` found zero blueprint nodes; `ancestor` confirmed
  `lem-trf-local-term-locality` for the new node's blueprint.from.

Source check: the online journal PDF named by the live node was opened; section 8,
Theorem 8.1, Definition 8.3, Remarks 8.4 and Lemma 8.5, pp.273--275, state the
arbitrary-commutative-ring stabilization and coordinate-restriction argument.
The stronger field-only assumptions of the surrounding resolution theorem are
not assumptions of Theorem 8.1. The source's surrounding section 7 and the
Theorem 9.6 application explain the prefixes and essential variables. There is
no statement correction and no STATEMENT-DISPUTED flag.

Validation: scompile.py compiled BOTH modules separately in dependency order
against the published live library, without errors or warnings. Definitions
are real data/predicates; the item's only theorem is postponed as required.
No global build, direct Git mutation, launcher edit, or shared-library edit was made.

## New nodes

`def-trf-supported-homogeneous-division` introduces only the missing common
language for the same notion: monotone diagrams and ordered vertices, the
first-dividing-vertex quotient supports and disjoint indexed family, spanning,
unique supported coefficients, the finite-test predicate, degree prefixes and
essential-variable restriction. Its module is
`Sheaf.RingTheory.SupportedHomogeneousDivision`; its main declaration is
`MonomialDiagram.IsFiniteDivisionTest`, and all twelve definitions are listed
in lean.declarations. The mathematical primitives are Mathlib's existing ones;
no replacement polynomial ring, basis, homogeneous submodule, lexicographic
order, or formal-series ring is introduced. Source and actual searches are
listed above and in the node. The new node is directly cited by the item.

The independent mathematical second reading is the maintainer's delivery review,
as specified in the dispatcher brief; no second reading by another worker is
claimed in this report.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
