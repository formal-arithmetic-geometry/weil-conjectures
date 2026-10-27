## Worker report

The module `Sheaf.RingTheory.LCIPrimePolynomialLocalPresentation` states
`Algebra.exists_prime_polynomial_local_presentation`, with proof `sorry`.
No definition or additional theorem is introduced, and no node field except `lean` changes.
I read the full node and its five proof steps, all eight statement-dependency nodes and
recorded interfaces, and Stacks `algebra.tex` at Definition 00S9, the final paragraph of
00SC, and Lemma 00SG. The module docstring records the five-step proof with its DAG inputs.

Clause-by-clause translation:

- The field is `(k : Type u) [Field k]`; the commutative algebra is
  `(S : Type v) [CommRing S] [Algebra k S]`, with independent, explicitly bound universes.
- Finite generation is `[Algebra.FiniteType k S]`. This is exactly the algebra form
  of the recorded `RingHom.FiniteType (algebraMap k S)`, as
  `RingHom.finiteType_algebraMap` states; no dependency repair is necessary.
- Local complete intersection is `(hlci : IsLocalCompleteIntersection k S)`, using
  the recorded upstream definition, including its finite-type parameter.
- A prime ideal is `(q : Ideal S) [q.IsPrime]`.
- The chosen principal neighbourhood is `∃ (h : S), h ∉ q ∧ ...`.
- Nonnegative numbers of variables and equations are `m c : ℕ`. The polynomial ring
  is exactly `MvPolynomial (Fin m) k`, and the equations are
  `f : Fin c → MvPolynomial (Fin m) k`.
- The presentation is the explicitly quantified algebra equivalence
  `θ : (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] Localization.Away h`.
- “Global complete intersection with this presentation” is `c ≤ m` together with
  `topologicalKrullDim (PrimeSpectrum (Localization.Away h)) = ↑(m - c)` for those
  very same `m`, `c`, `f`, and `θ`. This unpacks the nonzero branch of the recorded
  `IsGlobalCompleteIntersection`, rather than claiming some unrelated presentation.
  Nonzeroness follows from the given prime and `h ∉ q`; this is why truncated natural
  subtraction is accompanied by `c ≤ m`, exactly as in the upstream definition.
- The ideal `q_h` is written directly as `q.map (algebraMap S (Localization.Away h))`.
  The chosen `b : PrimeSpectrum (MvPolynomial (Fin m) k)` has ideal equal to its comap
  along `θ.toRingHom.comp (Ideal.Quotient.mk (Ideal.span (Set.range f)))`. Thus `b`
  is exactly the inverse-image prime in the node, with its primality carried by the
  bundled spectrum point; it is not an arbitrary prime.
- The regular-local assertion is `IsRegularLocalRing (Localization.AtPrime b.asIdeal)`;
  essential finite type is `Algebra.EssFiniteType k (Localization.AtPrime b.asIdeal)`.
- Regularity of the ordered sequence is `RingTheory.Sequence.IsRegular` on the
  localization itself, with sequence `(List.ofFn f).map (algebraMap ... ...)`.
  The maximal-ideal clause is separately `∀ i : Fin c, algebraMap ... (f i) ∈
  IsLocalRing.maximalIdeal (Localization.AtPrime b.asIdeal)`.
- The final isomorphism is the explicitly quantified `e`, from the quotient of
  `Localization.AtPrime b.asIdeal` by the span of the *same localized equations*,
  to `Localization.AtPrime q`, as a `k`-algebra equivalence.
- Canonicity is included: `ι : Localization.Away h →ₐ[k] Localization.AtPrime q`
  satisfies `∀ s, ι (algebraMap S _ s) = algebraMap S _ s`. The normalization on
  every polynomial `r` then says
  `e ([r/1]) = ι (θ ([r]))`. These are universal-property characterizations of the
  canonical maps, not unconstrained existence of an equivalence or an arbitrary map.
  Specifically, a homomorphism out of `S_h` is uniquely determined by its composite
  with `S → S_h`, since it must carry the inverse of `h` to the inverse of its image.
  Likewise, a homomorphism from a polynomial localization quotient is determined by
  the polynomial numerators, since the permitted denominators become units.
  Consequently the displayed equation forces the value on `r/t` to be the ratio
  of the images of `θ(r̄)` and `θ(t̄)`, and forces the iterated-localization fraction
  `(a/h^i)/(b/h^j)` to be `a*h^j/(h^i*b)` in `S_q`. This formulation avoids introducing
  extra chosen algebras or a second definition of localization.

Dependency declarations used:

- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType`,
  `Algebra.FiniteType`, and `RingHom.finiteType_algebraMap`,
  `Mathlib.RingTheory.FiniteType` (publicly supplied by the complete-intersection module).
- `def-weil-pbc-complete-intersection-over-field`:
  `Algebra.IsLocalCompleteIntersection` and the presentation in
  `Algebra.IsGlobalCompleteIntersection`,
  `WeilConjectures.RingTheory.CompleteIntersectionOverField`.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`,
  `Mathlib.Algebra.MvPolynomial.Basic`, publicly imported through the dependencies.
- `def-weil-ring-localization-away`: `Localization.Away`, from
  `Mathlib.GroupTheory.MonoidLocalization.Away`, publicly supplied by
  `Mathlib.RingTheory.Localization.Away.Basic`.
- `def-weil-regular-scheme`: its unchanged **ring clause**, namely
  `IsRegularLocalRing`, `Mathlib.RingTheory.RegularLocalRing.Defs`.
  The recorded `Sheaf.AlgebraicGeometry.IsRegularScheme` adds the scheme clause;
  this item uses only the ring clause supplied by that node's `mathlib_match`.
- `def-weil-pbc-essentially-finite-type-algebra`: `Algebra.EssFiniteType`,
  `Mathlib.RingTheory.EssentialFiniteness` (this Mathlib leaf needs no `lean` repair).
- `def-weil-pbc-regular-sequence`: `RingTheory.Sequence.IsRegular`,
  `Mathlib.RingTheory.Regular.RegularSequence`.

All stated proof inputs are imported: the polynomial regular-ring result from
`Mathlib.RingTheory.RegularLocalRing.Polynomial`,
`IsLocalization.prime_localRing_residueField_iso` from
`WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso`, and
`MvPolynomial.isRegular_localizationAtPrime_of_quotient_dimension` from
`WeilConjectures.RingTheory.GlobalCompleteIntersectionLocalRegularSequence`.
The quotient-localization Mathlib interface (`IsLocalization` quotient instance,
`Ideal.map_primeCompl_comap_of_surjective`, `IsLocalization.algEquiv`) is already
publicly imported by `Mathlib.RingTheory.Localization.AtPrime.Basic` and its imports.
The four definition nodes in `proof_deps` are the statement dependencies above.
There is no omitted proof module or import cycle.

Edge cases checked before drafting:

- `S = 0`: no proper prime, so `[q.IsPrime]` has no instance. No extra nonzero
  hypothesis on `S` is introduced.
- `m = 0`: `MvPolynomial (Fin 0) k` is the constant polynomial algebra; `c = 0`
  gives the field presentation. No positivity restriction occurs.
- `c = 0`: `f` has empty domain, its range spans the zero ideal, and its ordered
  list is empty. Regularity then expresses nonzeroness of the polynomial local ring.
- The polynomial algebra at the zero prime is a field localization and is covered.
- Dual numbers `k[t]/(t²)` at `(t)` and the crossing `k[x,y]/(xy)` at `(x,y)`
  admit their expected one-equation presentations. No reducedness or smoothness is assumed.
- All characteristics are allowed, as are differing carrier universes for `k` and `S`.
- The homomorphism `ι` is uniquely fixed by its normalization; the conclusion cannot
  be satisfied by substituting a noncanonical equivalence.

Searches, all using the prescribed `msearch.py` wrapper unless otherwise stated:

- LeanFinder: “A local complete intersection algebra over a field localized at a prime
  is a quotient of a polynomial regular local ring by a regular sequence”: eight hits,
  including `Algebra.IsSmoothAt`, its standard-smooth-neighbourhood theorem,
  `Algebra.IsStandardSmooth.localization_away`, `Algebra.SubmersivePresentation.localizationAway`,
  and `RingTheory.Sequence.IsWeaklyRegular.isRegular_of_isLocalization_of_mem`.
  Smoothness is stronger than LCI; the regular-sequence localization theorem assumes
  an existing weak regular sequence and supplies none of the presentation data here.
- Loogle: `"CompleteIntersection"`: zero hits.
- Mathlib grep: `CompleteIntersection|complete.intersection|polynomial.*local.*presentation`
  in `RingTheory`: one hit, a comment in `Extension/Presentation/Basic.lean` explaining
  the presentation-dimension convention. I read that comment; it is not a theorem.
- LeanSearch: “local complete intersection polynomial localization at prime regular
  sequence quotient presentation”: eight hits. These include localization of regular
  sequences, `IsLocalization.Away.mvPolynomialQuotientEquiv` (the inverse-element
  presentation of a principal localization), localized module constructions, and
  finite presentation of localization maps. None gives this LCI theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `prime_polynomial|polynomial_local_presentation|lem-trf-lci-prime-polynomial-local-presentation|IsLocalCompleteIntersection|IsGlobalCompleteIntersection`:
  found the recorded definitions and neighbouring results (pointwise LCI criterion,
  smooth LCI, conormal criteria, and syntomic fibre results), no theorem with these
  presentation and canonical-map clauses.
- The requested `grep -rn` of the item id in `lean/WeilConjectures` returned no match.
- `rg` for `exists_prime_polynomial_local_presentation|prime_polynomial_local_presentation`
  in Mathlib, `WeilConjectures`, `Sheaf`, and `dag/lean_names_upstream.json` returned
  no match: the proposed declaration name is unused.

No statement fault or disputed assertion was found. There are no new nodes,
dependency modules, statement corrections, or definitions with postponed data.

Validation: the prescribed `scompile.py Q31 ...` compiled this file both in sandbox
mode (1.9 seconds) and its actual library-module name (2.1 seconds), with no errors
or warnings. Every type/universe variable is explicitly bound; `autoImplicit` is false.

## Second reading by Q31

I reopened the node and the delivered module for a separate clause-by-clause pass.
This is an author second pass, not a claim of review by another agent: the dispatch
brief explicitly forbids starting other agents, and the maintainer reviews independently.
I checked the finite-type and LCI binders against the upstream definition, the identical
`f` in the global quotient and localized ideal, the direction of `θ`, and both comap
and algebra-equivalence directions. I checked that the dimension condition is tied to
this presentation, including `c ≤ m`, rather than only the abstract existence of some
GCI presentation. I checked that the prime is the inverse image of the extension of
`q`, that sequence order is preserved by `List.ofFn`, and that every localized equation
is explicitly in the maximal ideal. Finally I checked both normalization equations:
the first uniquely specifies `ι`, and the second uniquely specifies `e` because the
quotient is generated by polynomial numerators and inverses of denominators. This gives
both fraction formulas in the node, with no arbitrary-map loophole. Empty sequences,
zero variables, the zero-ring vacuity and independent universes are retained.
No mismatch was found and no statement change was made on this pass.
