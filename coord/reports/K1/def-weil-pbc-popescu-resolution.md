## Worker report

Module: `Sheaf.RingTheory.PopescuResolution`. It defines three notions belonging to
`def-weil-pbc-popescu-resolution`: the extended radical singular ideal (`Algebra.popescuIdeal`),
a resolution condition on two specified maps (`Algebra.IsPopescuResolution`), and existence
of a resolution (`Algebra.CanBePopescuResolved`). These are actual definitions, with no
`sorry`, axioms, auxiliary theorems, new nodes, or dependency replacements.

Source read: https://stacks.math.columbia.edu/tag/07F7 (Situation 16.9.1) and
https://stacks.math.columbia.edu/tag/07F6 (the paragraph immediately after that situation).
The repository's `literature/stacks-project/smoothing.tex` is absent on this machine;
the corresponding primary-source pages were opened instead. The node agrees with the source.

Clause-by-clause correspondence:

- The commutative rings are `{R : Type u}`, `{A : Type v}`, `{Λ : Type t}` with
  `[CommRing R] [CommRing A] [CommRing Λ]`.
- Noetherian `R` is `[IsNoetherianRing R]` in both resolution definitions.
- The given `R`-algebra structures are `[Algebra R A] [Algebra R Λ]`.
- Finite presentation of `A` is `[FinitePresentation R A]`. Mathlib's class explicitly
  describes a surjective map from `MvPolynomial (Fin n) R` with finitely generated kernel,
  exactly a presentation with finitely many variables and relations. No presentation
  is chosen: the node's parenthetical presentation explains the property, not extra data.
- The homomorphism `α` is `(α : A →ₐ[R] Λ)`, so it respects the fixed base algebra maps.
- The prime ideal is `(q : PrimeSpectrum Λ)`; its underlying ideal is `q.asIdeal`.
  This bundles an ideal and its primality, without requiring any further property.
- `H_{A/R}` is the recorded dependency `Algebra.singularIdeal R A`.
- Extension along `α` is `Ideal.map α.toRingHom (singularIdeal R A)`, the ideal generated
  by the image, including arbitrary coefficients from `Λ`.
- Taking `.radical` gives precisely `h_A`. The helper `popescuIdeal` is defined for any
  algebra map because this ideal construction itself needs neither Noetherianity nor
  finite presentation; the two local-problem predicates retain both hypotheses.
- A candidate intermediate ring has `{B : Type w} [CommRing B] [Algebra R B]`.
- Its finite presentation is the first condition `FinitePresentation R B`, inside the
  predicate, so a candidate not of finite presentation is not a resolution.
- The specified factorization maps are `(β : A →ₐ[R] B)` and `(γ : B →ₐ[R] Λ)`;
  `γ.comp β = α` asserts their composite is the given map, as an algebra homomorphism.
- `h_B` is `popescuIdeal γ`, formed by the identical construction with the map `γ`.
- Inclusion `h_A ⊆ h_B` is `popescuIdeal α ≤ popescuIdeal γ`.
- Noncontainment `h_B ⊈ q` is `¬ popescuIdeal γ ≤ q.asIdeal`.
  These two conditions are conjoined explicitly; the first is not inferred from factorization.
- “Can be resolved” is the existential over `B`, its commutative ring and `R`-algebra
  structures, and the maps `β` and `γ`, satisfying `IsPopescuResolution α q β γ`.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: Mathlib's `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`, lines 193–198, including its docstring.
  Its record is `mathlib_match`, not `lean`; no replacement is needed.
- `def-weil-pbc-singular-ideal`: `Algebra.singularIdeal`,
  `Sheaf.RingTheory.SingularIdeal`; read the entire module, including the full signature
  and docstring. It is the radical of the span of the elements with smooth principal
  localization, exactly the node's intrinsic singular ideal.
- Standard Mathlib operations: `Ideal.map` (`Mathlib.RingTheory.Ideal.Maps`),
  `Ideal.radical` (`Mathlib.RingTheory.Ideal.Operations`), `AlgHom.comp`
  (`Mathlib.Algebra.Algebra.Hom`), and `Algebra.FinitePresentation`
  (`Mathlib.RingTheory.FinitePresentation`). Their defining signatures were read.
  Both explicit imports are used: the first provides the singular ideal and spectrum;
  the second provides finite presentation and the Noetherian infrastructure.

Edge cases checked before writing:

- The zero ring `Λ` has no primes, correctly leaving no local problem at a prime.
  No nontriviality hypothesis is imposed on any ring.
- Zero intermediate rings are allowed as candidates; any impossible map or failure
  of noncontainment is handled by the predicate, without excluding them in a binder.
- Zero variables or relations in a finite presentation are included by Mathlib's
  `n : ℕ` and finitely generated kernel; no positive-dimension or positive-size condition.
- An identity factorization is a resolution exactly when its ideal is not contained in
  `q`; factorization alone does not satisfy the noncontainment clause.
- `h_A = ⊥` and `h_A = ⊤` remain legitimate ideals. The latter forces `h_B = ⊤`,
  which is not contained in the proper prime `q`.
- All characteristics and distinct universes for `R`, `A`, `B`, and `Λ` are allowed.
  For existence the carrier `B : Type (max u v w)` is sufficiently large: every
  finitely presented `R`-algebra is isomorphic to a quotient of a finite-variable
  polynomial ring over `R`, whose carrier lies in `Type u`; it can be lifted to this
  universe. Thus this choice loses no resolution, even if `Λ` has a larger universe.
  The candidate predicate itself accepts `B` in an arbitrary universe.

Searches performed with `/home/ubuntu/weil-launcher/msearch.py` under group K1 and this item
(the tool's actual records are in sandbox `searches.jsonl`):

- LeanSearch: “Popescu resolution of an algebra map through a finitely presented algebra
  with inclusion of extended singular ideals”. Service unavailable (Internal Server Error);
  no mathematical verdict inferred from this failure.
- LeanFinder: “radical ideal generated by the image of the singular ideal and a Popescu
  resolution at a prime ideal”. Eight hits, including `Algebra.IsSmoothAt`,
  `Algebra.smoothLocus`, `Algebra.smoothLocus_eq_compl_support_inter`,
  `Algebra.IsSmoothAt.exists_notMem_smooth`, and `Algebra.Smooth.exists_span_eq_top_isStandardSmooth`.
  These concern smoothness, not extension of a singular ideal or resolutions. No match.
- Loogle: `Ideal.map, Ideal.radical`. Four hits: `Ideal.map_radical_le`,
  `Ideal.map_radical_of_surjective`, `IsLocalization.map_radical`, and
  `IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`. These are properties of
  general ideal operations, not the node's definitions. No match.
- Mathlib grep: `popescu|singularIdeal|PopescuResolution|07F7`, subdirectory `RingTheory`.
  No hits.
- `rg` of the same conceptual names and the node id in `WeilConjectures`, `lean/Sheaf`,
  and `dag/lean_names_upstream.json`: only the existing dependency's `singularIdeal`
  and its lemmas in `Sheaf.RingTheory.SingularIdeal`. No resolution notion.
- Exact proposed names `PopescuResolution|popescuIdeal|CanBePopescuResolved` searched in
  all Mathlib, `WeilConjectures`, `lean/Sheaf`, and the upstream names table: no hits.

No statement correction or disputed statement. The module compiled on the server in 1.4 s,
with exit code 0 and no warnings, under the project's explicit-variable settings.

## Second reading by K1

I independently matched the node's single statement against `PopescuResolution.lean`.

- The node's Noetherian commutative base ring `R` is rendered by `{R : Type u}`,
  `[CommRing R]`, and `[IsNoetherianRing R]` in `IsPopescuResolution` and
  `CanBePopescuResolved`.
- The commutative `R`-algebras `A` and `Λ` and finite-presentation hypothesis on `A`
  are rendered by `[CommRing A] [CommRing Λ]`, `[Algebra R A] [Algebra R Λ]`, and
  `[FinitePresentation R A]`; no presentation data or stronger finiteness condition is
  introduced.
- The `R`-algebra map `α : A → Λ` is `(α : A →ₐ[R] Λ)`, and the prime `q` is
  `q : PrimeSpectrum Λ`, with its ideal rendered as `q.asIdeal`.
- The singular ideal `H_{A/R}` and its extension/radical `h_A` are rendered by the
  dependency declaration `Algebra.singularIdeal R A` and
  `Algebra.popescuIdeal α := (Ideal.map α.toRingHom (singularIdeal R A)).radical`.
- The resolution's intermediate commutative `R`-algebra `B`, maps `β` and `γ`, and
  factorization are rendered by `[CommRing B] [Algebra R B]`,
  `β : A →ₐ[R] B`, `γ : B →ₐ[R] Λ`, and `γ.comp β = α`.
- Finite presentation of `B`, inclusion `h_A ⊆ h_B`, and noncontainment
  `h_B ⊈ q` are exactly the three remaining conjuncts of
  `IsPopescuResolution`; `h_B` is `popescuIdeal γ`. The existential in
  `CanBePopescuResolved` quantifies the intermediate carrier, its structures, and both
  maps and then applies this predicate.

No mismatch was found and no source or Lean change was needed. The empty prime set of
 a zero `Λ`, zero rings and zero intermediate candidates, `n = 0` presentations,
radical ideals equal to `⊥` or `⊤`, all characteristics, and independent universes are
all admitted by the binders and predicates. The implementation does not impose a
nontriviality, properness, or positivity hypothesis. `B : Type (max u v w)` is a
polymorphic universe choice and does not restrict the candidate notion.

I repeated the existing-definition searches (LeanSearch/LeanFinder/Loogle and grep in
Mathlib, `WeilConjectures`, `lean/Sheaf`, and the upstream names table); only the
recorded `Algebra.singularIdeal` dependency was found. No declaration for Popescu's
extended ideal or resolution exists, so the three definitions remain necessary. The
module compiles cleanly with `scompile.py`; there were no mismatches, corrections,
new nodes, or dependency replacements.
