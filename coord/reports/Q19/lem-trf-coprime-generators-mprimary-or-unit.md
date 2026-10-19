## Worker report

The module `Sheaf.TraceFormula.CoprimeGeneratorsMprimaryOrUnit` states the node's
statement as `RingTheory.coprimeGeneratorsMprimaryOrUnit`.  It contains only the
requested theorem with proof `sorry`; no data definition or proved helper is added.
The module and theorem docstrings cite Stacks Project Curves, Tag 0C48, and carry
`(blueprint: lem-trf-coprime-generators-mprimary-or-unit)`.  The theorem docstring
records all four proof steps from the node: the regular-local UFD/domain input and
nonzero ideal observation; the dimension-two prime-chain argument; principality of a
height-one prime and the common-divisor contradiction; and the radical/intersection
conclusion.

Clause-by-clause rendering of the node is as follows.

- The regular local ring is `(A : Type u) [CommRing A] [IsRegularLocalRing A]`.
  This is Mathlib's recorded declaration for `def-weil-regular-scheme` at ring level;
  its class supplies the local and Noetherian hypotheses in the node.
- Krull dimension two is
  `hdim : ringKrullDim A = (2 : WithBot ℕ∞)`, using the recorded Mathlib
  `ringKrullDim` declaration for `def-weil-pbc-krull-dimension-ring`.
- A finite list of generators is represented without an extra finiteness hypothesis by
  `(r : ℕ) (g : Fin r → A)`.  Its generated ideal `J` is rendered everywhere by
  `Ideal.span (Set.range g)`.
- “Every element dividing every generator is a unit” is exactly
  `hdiv : ∀ d : A, (∀ i : Fin r, d ∣ g i) → IsUnit d`.
- The two alternatives are exactly
  `Ideal.span (Set.range g) = ⊤ ∨
  (Ideal.span (Set.range g)).radical = IsLocalRing.maximalIdeal A`.
  The maximal ideal is the canonical one supplied by the local-ring dependency; no
  independently chosen ideal is introduced.

The statement dependencies were read in full and are used as follows:

- `Mathlib.RingTheory.RegularLocalRing.Defs`, declarations
  `IsRegularLocalRing`/`IsRegularRing`, supplies the regular-local ring notion.
- `Mathlib.RingTheory.KrullDimension.Basic`, declaration `ringKrullDim`, supplies
  the Krull-dimension expression.

The proof dependencies named by the node were also inspected for the docstring plan:
`Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization`, declaration
`RingTheory.regularLocalUFDBoundaryFactorization`; Mathlib's
`UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one`; and Mathlib's
`PrimeSpectrum.zeroLocus_eq_iff` (with `Ideal.radical_eq_sInf` as the recorded
radical/intersection ingredient).  They are imported only to preserve the stage-3
proof route; the stage-2 proof itself is `sorry`.

Edge cases checked: `r = 0` is admitted by the type (then `hdiv` is the stated
vacuous common-divisor condition, which cannot hold in a nontrivial regular local
ring); a one-element list and a list containing zero are admitted exactly when the
common-divisor hypothesis permits them; the unit ideal alternative covers a generator
that generates `1`; and no field, characteristic, nonzero-generator, or universe
restriction beyond the node is added.  The `Fin r` encoding covers every finite list,
including the empty one, and `Set.range` gives exactly its span.

Searches made on 2026-10-18:

- `msearch.py Q19 lem-trf-coprime-generators-mprimary-or-unit leanfinder` with the
  plain-language two-dimensional regular-local coprime-generator query returned
  UFD, Dedekind, and primary-ideal results, but no exact dichotomy theorem.
- `msearch.py ... loogle "IsRegularLocalRing, Ideal.radical"` returned no hits.
- `msearch.py ... grep "radical|height.*one|prime.*divisor" Mathlib/RingTheory`
  returned general radical and height lemmas, but no combined statement.
- `msearch.py ... leansearch` queries for the dimension-two local-UFD radical
  dichotomy returned only generic UFD, height, and maximal-radical lemmas.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/` found no declaration of
  `coprimeGeneratorsMprimaryOrUnit` or an equivalent theorem; the only related local
  result is the separate `regularSurfaceDepthOnePrincipal` theorem.
- `grep -rl` over `dag/nodes` found this item and its single consumer only, with no
  duplicate notion.  The recorded dependency declarations were opened at their full
  signatures and docstrings.

No node correction, new node, dependency repair, or `STATEMENT-DISPUTED` flag is
needed.  The returned stage-1-only split metadata was retained unchanged; this
repair adds the missing stage-2 module, `lean` record, and reports.

## Second reading by Q19

I reread the returned node, its source paragraph (Curves.tex, Tag 0C48, lines
3829–3837), and the completed signature.  The object and hypothesis audit is:

- `A`, its commutative-ring instance, and the regular-local class are rendered by
  `(A : Type u) [CommRing A] [IsRegularLocalRing A]`, with no added Noetherian,
  domain, field, or nonzero assumption.
- The dimension hypothesis is exactly `ringKrullDim A = 2` in `WithBot ℕ∞`.
- `r : ℕ` and `g : Fin r → A` are the finite generator list; the only condition on
  it is the node's common-divisor-to-unit implication `hdiv`.
- `Ideal.span (Set.range g)` is the direct Lean ideal generated by all listed
  elements, and the conclusion has both node alternatives, including the exact
  maximal ideal and radical equality.

I checked `r = 0`, `r = 1`, zero generators, a unit generator, and arbitrary universe
`u`; all remain in the quantified statement.  The module has no local notation,
private declaration, hidden variable, or proof other than `sorry`.  The searches
above were repeated with alternate “maximal-primary”, “height-one prime”, and
“local UFD” wording; no existing exact declaration was found.  No mismatch was
found and no statement correction was made.
