## Worker report

The module `Sheaf.RingTheory.PopescuResolveCharP` states
`Algebra.canBePopescuResolved_of_char_pos`, with its proof left as `sorry`.
Its docstring carries all eleven expanded DAG proof steps and their cited nodes,
including the DAG's existing corrections of the source's intermediate formulas.
No definition, dependency module, or new node is needed; the node changes only in `lean`.

Hypothesis and clause correspondence:

- The field k is `{k : Type u} [Field k]`; positive characteristic is
  `(p : ℕ) [CharP k p] (hp : 0 < p)`. No extra perfectness or cardinality assumption.
  The field forces any positive characteristic to be prime, so a separate primality
  hypothesis is unnecessary.
- The finitely presented k-algebra A is `{A : Type v} [CommRing A] [Algebra k A]
  [FinitePresentation k A]`.
- The commutative k-algebra Λ and its k-algebra map are `{Λ : Type w} [CommRing Λ]
  [Algebra k Λ]` and `(α : A →ₐ[k] Λ)`.
- The prime ideal q is `(q : PrimeSpectrum Λ)`; its ideal is `q.asIdeal`.
- Noetherianity of Λ is `[IsNoetherianRing Λ]`.
- Geometric regularity over k is `(hreg : IsGeometricallyRegular k Λ)`.
  The recorded definition includes Noetherianity and tests every finite purely
  inseparable field extension in `Type (max u w)`. This matches the source notion.
- The ideal h_A is exactly `popescuIdeal α`, the radical of the image ideal of
  `singularIdeal k A` under α. No alternate singular ideal is introduced.
- Minimality over h_A is the pair `hcontain : popescuIdeal α ≤ q.asIdeal` and
  `hminimal : ∀ q' : PrimeSpectrum Λ, popescuIdeal α ≤ q'.asIdeal →
  q'.asIdeal ≤ q.asIdeal → q' = q`. This says q belongs to the stated set and no
  distinct member of that set lies below q; it does not require q to be least.
- The conclusion is `CanBePopescuResolved α q`, using precisely the recorded
  factorization predicate. It includes finite presentation of B, equality of the
  composite with α, h_A ≤ h_B, and h_B not contained in q through
  `IsPopescuResolution`.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, whose docstring and
  `isNoetherianRing_iff_ideal_fg` identify the finite-generation condition.
- `Sheaf.RingTheory.GRing`: `Algebra.IsGeometricallyRegular`. Read the whole module,
  including the regular-map and G-ring declarations; the theorem uses its field-algebra
  clause only, as the dependency node requires here.
- `Sheaf.RingTheory.PopescuResolution`: `Algebra.popescuIdeal`,
  `Algebra.CanBePopescuResolved`, and its underlying `Algebra.IsPopescuResolution`.
  Read full signatures, bodies, docstrings, and universe convention for the witness B.

Source check: local `literature/stacks-project/smoothing.tex` is absent on this machine.
Opened https://stacks.math.columbia.edu/tag/07FJ instead: its three assumptions and
conclusion agree exactly with the DAG statement. Its reference to Situation 07F7 is
implemented by the already recorded Popescu-resolution dependency. No statement
correction or STATEMENT-DISPUTED fault is needed.

Edge cases checked: the zero target ring has no prime-spectrum element, so it adds no
spurious instance of the hypotheses. If h_A is the unit ideal, `hcontain` is impossible
for a prime. If h_A is zero, the hypotheses allow any minimal prime, including height
zero. No dimension bound or nonzero singular ideal is assumed. Minimal primes can be
incomparable: the formulation only compares primes below q. Arbitrary and independent
universes u, v, w are retained; the intermediate algebra's universe is exactly the
recorded resolution predicate's `max u v`, justified there by finite presentation.
Characteristic zero is excluded exactly by hp; no positive characteristic is excluded.

Searches for an existing statement (msearch.py, group E1, this item):

- leansearch: `Popescu resolution geometrically regular algebra positive characteristic`:
  service unavailable (Internal Server Error); recorded as unavailable, no verdict.
- leanfinder: `Popescu local problem can be resolved over a field of positive
  characteristic for geometrically regular Noetherian algebra`: eight hits, including
  `Algebra.Smooth.exists_finiteType`, `Algebra.Smooth`, geometric reducedness and
  smooth-locus lemmas; none states this resolution theorem.
- loogle: `Algebra.CanBePopescuResolved, Algebra.IsGeometricallyRegular`: zero hits,
  unknown identifier for the project-only resolution predicate.
- Mathlib grep: `Popescu|popescu|GeometricallyRegular` in RingTheory: zero hits.
- rg over WeilConjectures and lean/Sheaf: `Popescu|popescu|resolve.*char|07FJ`:
  only unrelated Gabriel-Popescu material upstream; locally the definitions and
  component reductions (`FactorsThroughSmooth`, `EssentiallySmoothComp`), not this
  theorem. Exact node-id grep upstream found nothing.
- Exact proposed declaration name rg in `dag/lean_names_upstream.json`, Mathlib,
  WeilConjectures and lean/Sheaf: no collision.

Validation: server compilation via scompile.py; initial compilation had only three
long-line warnings in the copied natural-language proof, repaired by wrapping equations.
The final server compilation and deliver2.py --no-push are run after this report.
The independent second reading is left to the assigned second reader.

## Second reading by E1

I independently opened the item node, its entire Lean module, all three statement
 dependency nodes and their declarations. I fetched Stacks' `smoothing.tex` into
`scratchpad/smoothing.tex` because the repository has no local Stacks source.
I read `lemma-resolve-general` (lines 2671 onward), `situation-local`
(lines 2078-2094), and the opening of `section-inseparable`. The section adds
no standing hypothesis: the local Artinian and cotangent-dimension hypotheses
belong to `lemma-helper`, not to this item. The statement also agrees with
https://stacks.math.columbia.edu/tag/07FJ and its Situation 07F7.

My object/hypothesis/conclusion list and correspondence:

1. Field k: `{k : Type u} [Field k]`. Exact; its Noetherian instance supplies
   the base-ring condition of Situation 07F7 without an extra assumption.
2. Positive characteristic p: `(p : ℕ) [CharP k p] (hp : 0 < p)`.
   Exact; no prime, perfectness, or finite-field assumption added. In a field,
   positive characteristic is necessarily prime.
3. Finitely presented k-algebra A: `{A : Type v} [CommRing A] [Algebra k A]
   [FinitePresentation k A]`. Exact; no smoothness or reducedness required.
4. Commutative k-algebra Λ and its specified map: `{Λ : Type w} [CommRing Λ]
   [Algebra k Λ] (α : A →ₐ[k] Λ)`. Exact; the algebra-map type ensures the
   two structural k-maps commute, not merely that α is a ring map.
5. Prime q of Λ: `(q : PrimeSpectrum Λ)`, with ideal `q.asIdeal`.
   Exact; neither maximality nor localization of Λ is imposed.
6. Λ Noetherian: `[IsNoetherianRing Λ]`. Exact. I read the Mathlib abbreviation
   and `isNoetherianRing_iff_ideal_fg` in Noetherian/Defs.lean.
7. Geometrically regular over k: `(hreg : IsGeometricallyRegular k Λ)`.
   Exact recorded field-algebra clause in GRing.lean: Noetherianity and
   regularity of `TensorProduct k k' Λ` for every finite purely inseparable
   field extension k'/k. I read the full definition, not the G-ring predicate.
   Its repeated Noetherian clause is the same stated hypothesis, not a stronger one.
8. h_A = radical of the singular ideal extended along α: `popescuIdeal α`.
   Exact body `(Ideal.map α.toRingHom (singularIdeal k A)).radical`.
   I also read SingularIdeal.lean: the singular ideal is the radical span of
   the elements whose principal localizations are smooth. No private copy.
9. q minimal over h_A: `hcontain : popescuIdeal α ≤ q.asIdeal`, together with
   `hminimal : ∀ q' : PrimeSpectrum Λ, popescuIdeal α ≤ q'.asIdeal →
   q'.asIdeal ≤ q.asIdeal → q' = q`. Exact membership and minimality;
   equality of bundled primes is equivalent to equality of their ideals.
   Incomparable minimal primes are allowed; q is not asserted least.
10. The local problem can be resolved: `CanBePopescuResolved α q`. Exact.
    I unfolded its definition and `IsPopescuResolution` in PopescuResolution.lean:
    there exists a commutative k-algebra B with β : A →ₐ[k] B and
    γ : B →ₐ[k] Λ, such that B is finitely presented, `γ.comp β = α`,
    `popescuIdeal α ≤ popescuIdeal γ`, and `¬ popescuIdeal γ ≤ q.asIdeal`.
    All four clauses are present in the required existential order, for the
    same α and q, without requiring B itself smooth everywhere.

Edge cases: the zero ring Λ has no prime q, and the zero algebra A cannot map
as a unital algebra into a ring with a prime. These vacuous cases agree with
the source; no `IsDomain` or `Nontrivial` hypothesis was added. If h_A is the
unit ideal, containment in q is impossible; if h_A is zero, height-zero
minimal primes are included. Characteristic zero is excluded precisely by hp;
p = 1 is already impossible for a field, and all positive prime characteristics
are covered. There is no index set, scheme, or integer n in the signature;
empty parameter families and d = 0 in the proof impose no statement restriction.
Universes u, v, w are bound and independent. Geometric regularity tests fields
in `max u w`, large enough to represent every finite extension of k. The
resolution witness lives in `max u v`, sufficient for any finite polynomial
quotient over k; Λ need not live in that universe. No case is excluded.

Independent searches, using different descriptive words from the first reader:

- LeanFinder via msearch: `Neron desingularization local resolution prime minimal
  singular ideal in positive characteristic`. Eight hits, chiefly smoothness
  at a prime, standard smooth localizations and smooth locus; none is this theorem.
- Loogle via msearch: `"resolution"`. Twelve hits, on Cooper arithmetic and Lean
  internals; no ring-theoretic resolution theorem.
- LeanSearch via msearch: `A finitely presented algebra over a positive
  characteristic field maps to a Noetherian geometrically regular algebra and
  has a Popescu resolution at a minimal singular prime`. Service unavailable
  (Internal Server Error); no mathematical verdict inferred from that failure.
- rg for `desingular|geometrically.?regular|popescu|07FJ` over Mathlib/RingTheory,
  upstream WeilConjectures, and repository lean/Sheaf: only the recorded
  definitions and other geometric-regularity/component lemmas locally;
  upstream Popescu hits concern the unrelated Gabriel-Popescu theorem.
  The local FactorsThroughSmooth and EssentiallySmoothComp signatures concern
  intermediate reductions, not this local-resolution assertion.
- Exact-name search including dag/lean_names_upstream.json found no collision
  for `canBePopescuResolved_of_char_pos`.

No mismatch found and no Lean or node change needed. There are no new nodes,
dependency modules, statement corrections, or existing-declaration claims in
this delivery. Both imports supply definitions actually used. There is one
named theorem, with proof `sorry`, no new definition and nothing proved.
The module and theorem docstrings identify the source and blueprint node;
the theorem docstring contains all eleven DAG proof steps and their uses,
including the already documented intermediate-formula corrections. No variable
or universe is unbound, and all lines are within the convention. I checked
programmatically that `lean.statement` is verbatim the theorem signature.

Validation: server scompile.py completed in 1.7 seconds, exit 0, with no warnings.
The first invocation used a relative path from the read-only repository and
could not locate the sandbox file; retrying its absolute sandbox path succeeded.
The delivery dry run and final delivery follow this independent review.

## Reviewer fix (R-prc1351)

The pair `hcontain`/`hminimal` (a hand-written second encoding of "q minimal over h_A")
is replaced by the sibling form `(hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes)`,
as in the landed PopescuDelocalizeHeightZero / PopescuDelocalizeWeak and G1's
lem-weil-pbc-popescu-resolve-separable. Same meaning; one encoding of minimality.
