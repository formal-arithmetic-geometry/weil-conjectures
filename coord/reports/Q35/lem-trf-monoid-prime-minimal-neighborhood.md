## Worker report

The module `Sheaf.AlgebraicGeometry.MonoidPrimeMinimalNeighborhood` states
`AlgebraicGeometry.FineFan.monoidPrime_minimal_neighborhood`. It has one theorem,
whose proof is `sorry`, and no definitions. The node is unchanged except for its
`lean` record. No statement dispute or dependency fault was found.

The source was read in ILO, Exposé VIII, printed p.98, sections 3.1.1--3.1.4
(PDF page 104). These define units and integral localizations, include the empty
prime, and describe point localizations as affine basic opens. The node expands
the finite-generator calculation underlying those descriptions. The declaration
docstring reproduces all seven proof steps, including their dependency and the
integrality argument needed to recover equality in the original monoid.

Hypotheses and notation:

- `P : Type u` and `[CommMonoid P]` give the arbitrary commutative monoid, using
  the recorded dependency's multiplicative convention. `1`, multiplication,
  powers, and products stand for additive `0`, addition, natural multiples, and
  sums. This changes notation only, and does not assume an absorbing zero.
- `hP : IsFine P` is exactly finite generation plus injectivity of the canonical
  map into the Grothendieck group; no saturation, sharpness, or torsion-freeness
  hypothesis is imposed.
- `r : ℕ`, `e : Fin r → P`, and
  `he : Submonoid.closure (Set.range e) = ⊤` are the arbitrary finite tuple of
  monoid generators, including `r = 0`.
- `x : MonoidPrime P` is the proper semigroup ideal with multiplicative
  complement, including the empty ideal.
- `F` is written inline as `Submonoid.closure {a : P | a ∉ x.carrier}`. The
  first conclusion asserts that its carrier is exactly the complement, so this
  representation neither changes the face nor assumes closure as an extra
  hypothesis.
- `I` is written inline as
  `Finset.univ.filter (fun i : Fin r ↦ e i ∉ x.carrier)`.
- `b : P` and `hb : b = I.prod e` name precisely the product prescribed by
  the node. This defining equality is a binder for the node's introduced object,
  not a restriction on the input data. It is available for every `P`, `e`, and
  `x`. There are no hidden `let` binders or auto-implicit variables.

Conclusions, in theorem order:

1. `(Submonoid.closure ... : Set P) = {a | a ∉ x.carrier}` says the complement
   is a submonoid, with its actual underlying elements fixed.
2. `∀ c d, c * d ∉ x.carrier → c ∉ x.carrier ∧ d ∉ x.carrier` is the face
   property, with both factors included.
3. For every exponent tuple `n : Fin r → ℕ`, a product outside the prime has
   `e i ∉ x.carrier` whenever `n i ≠ 0`. This is exactly the assertion about
   every generating expression, including all repeated occurrences.
4. Equality between the closure of
   `{a | ∃ i, e i ∉ x.carrier ∧ e i = a}` and the closure of the complement
   says the selected generators generate `F`.
5. Equality of the carrier of `basicOpen b` with
   `⋂ (i : Fin r) (_ : e i ∉ x.carrier), basicOpen (e i)` is the indexed
   intersection over selected generators. Taking carriers states equality of
   the underlying open sets, with exactly the intended empty-intersection case.
6. Equality with `⋂ (f : P) (_ : f ∉ x.carrier), basicOpen f` is the second
   intersection, over the whole complementary face.
7. `x ∈ basicOpen b` asserts containment of the original prime.
8. `∀ U : Opens (MonoidPrime P), x ∈ U → basicOpen b ≤ U` asserts containment
   in every open neighborhood. Openness already belongs to `basicOpen`.
9. `Algebra.faceLocalization P (Submonoid.powers b) =
   Algebra.faceLocalization P (Submonoid.closure ...)` is equality of the
   submonoids inside the very same canonical Grothendieck group, namely
   `P_b = P-F` in additive notation.
10. For each selected index, the completion element
    `of (I.erase i |>.prod e) * (of b)⁻¹` belongs to `P_b`, and its product
    with `of (e i)` equals `1`. These are both the membership and inverse
    assertions for `(b-e_i)-b`. Erasing the index removes one occurrence,
    even when two indices have equal generator values.
11. For every `p : P`, existence of `v` in the face localization with
    `of p * v.val = 1` is equivalent to
    `∃ q f : P, f ∉ x.carrier ∧ p * q = f`.
    This is exactly the dependency's definition of being a unit, applied to
    the numerator. Every numerator belongs to the localization (fraction
    `p/1`); the existential inverse condition is stated in its ambient group
    to avoid introducing a redundant numerator helper or a proof binder.
    Both `q` and `f`, and especially `p * q = f`, are in `P` itself.
12. The latter existential is equivalent to `p ∉ x.carrier`. Thus both
    equivalences in the displayed chain, with their common middle term,
    are present, rather than just the composite criterion.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineFanBlowup`:
  `AlgebraicGeometry.FineFan.IsFine`, `MonoidPrime`, `spectrumTopology`, and
  `basicOpen`, with their full signatures and source docstrings. This public
  import is also the only recorded proof-dependency module, so no additional
  proof import is missing.
- Its imported `Sheaf.TraceFormula.FaceLocalizationFs`:
  `Algebra.faceLocalization (Q : Type u) [CommMonoid Q] (F : Submonoid Q) :
  Submonoid (Algebra.GrothendieckGroup Q)`, whose carrier consists of
  actual fractions `of q * (of f)⁻¹`.
- Mathlib's `Algebra.GrothendieckGroup`, `Algebra.GrothendieckGroup.of`,
  `Submonoid.closure`, `Submonoid.powers`, and `Finset.prod`. The explicit
  BigOperators import supplies the finite products used in the statement.

Edge cases checked before writing:

- `r = 0`: the generation hypothesis forces the trivial monoid, the selected
  product is `1`, and both intersections give the entire spectrum. The inverse
  assertion has no indices. The unit criterion still holds.
- The empty prime is admitted: the face is all of `P`, its localization is the
  group completion, and its smallest open consists of the generic point.
- At the maximal prime of nonunits, the face is the unit group; selected
  generators may be absent, in which case `b = 1` and the smallest neighborhood
  is the entire spectrum. In a fine group only the empty prime exists; all
  conclusions still apply.
- Generators equal to `1`, repeated generators, zero exponents, and the empty
  selected set cause no division or indexing problem. The inverse formula uses
  `erase i` on the selected index finset, not erasure of the generator value.
- Integrality comes only from `IsFine`; torsion in the completion is allowed.
  All elements of the localization remain fractions in that completion, and
  the unit witness equation is deliberately in `P`.
- The universe `u` is explicit and arbitrary; the finite generator indices are
  `Fin r`, with no additional universe restriction.

Searches for an existing statement (all through the prescribed `msearch.py`):

- LeanFinder query: "A prime complement in a finitely generated integral monoid
  is generated by the generators it contains; their product defines its smallest
  open neighborhood and its localization". Eight hits, headed by
  `Ideal.primeCompl`, `PrimeSpectrum.PiLocalization`, and
  `Submonoid.FG.finite_irreducible_mem_submonoidClosure`. The ring-spectrum
  results require a semiring, while the irreducibility result has neither the
  prime complement nor its neighborhood. No exact statement.
- Loogle query: `Submonoid, IsUnit, Localization`. No hits.
- Mathlib grep query:
  `MonoidPrime|faceLocalization|smallest.*neighbo|minimal.*neighbo`.
  Three hits, in `Topology/Defs/Filter` and `Topology/AlexandrovDiscrete`.
  Read the Alexandrov definition: it supplies an abstract topology property,
  not the generating tuple, monoid prime, localization equality, or inverse.
- LeanSearch query: "The complement of a prime monoid ideal is a face generated
  by the monoid generators outside the prime, and their product defines its
  smallest open neighborhood". Eight hits, chiefly `Ideal.primeCompl` and
  order-ideal complements. Their signatures require semiring ideals or order
  filters and do not state the theorem.
- Direct `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `MonoidPrime`, `faceLocalization`,
  `monoidPrime_minimal_neighborhood`, prime-complement generation, and smallest
  neighborhoods. No upstream declaration of this theorem and no existing
  theorem with all its clauses. The exact node id has no existing Lean hit.
  Project hits supplied the canonical FineFan definitions and localization;
  `AffineFanLocalizationSections` describes the argument only in its proof
  docstring. `Monoscheme.neighborhoodGenerator` in `AffineLiftTowerDescent`
  defines the same selected product but no theorem; this delivery uses the
  finite-product expression directly and defines no duplicate helper.
- Read `Submonoid.LocalizationMap.map_isUnit_iff` in
  `Mathlib/GroupTheory/MonoidLocalization/Divisibility.lean`: it gives a general
  divisibility criterion, but not the face-generator or neighborhood statements.
  The face-generation argument in the proof of `faceLocalization_fineSaturated`
  is local to a theorem with saturation hypotheses, and is not an available
  exact statement of this item.

Validation: the prescribed `scompile.py` compiled the module on the server as
both its sandbox check and its library-module check, with no errors or warnings.
Only the prescribed wrappers are used for compilation and delivery. The shared
repository and all its Lean sources were read only.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
