## Worker report

The module states Serre's normality criterion, without proving it. The node and the source
agree, so there is no statement correction, new node, dependency module, or disputed statement.
Source checked: [Stacks Tag 031S](https://stacks.math.columbia.edu/tag/031S), Lemma 10.157.4.
The local Stacks checkout is absent on this machine, so the source statement and proof were
read from that page. The declaration docstring carries all nine steps of the DAG proof.

Clause-by-clause correspondence:

- A commutative ring: `(R : Type u) [CommRing R]`, with arbitrary explicit universe `u`.
- Noetherian: `[IsNoetherianRing R]`, precisely finite generation of every ideal.
- Every prime localization is a normal domain:
  `∀ (p : Ideal R) [p.IsPrime], IsDomain (Localization.AtPrime p) ∧
  IsIntegrallyClosed (Localization.AtPrime p)`. Both the domain clause and integral closedness
  clause are required. No global domain assumption is added.
- If and only if: `↔`.
- Property `(R₁)`: `Ring.IsSerreR R 1`.
- Property `(S₂)`: `Ring.IsSerreS R 2`.
- Both properties: the conjunction `∧` on the right.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its docstring;
  `isNoetherianRing_iff_ideal_fg` confirms the interpretation.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, the abbreviation
  for integral closedness in `FractionRing`, and `isIntegrallyClosed_iff`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, localization at the
  prime complement. This is available through the SerreConditions import.
- `Sheaf.RingTheory.SerreConditions`: `Ring.IsSerreR` and `Ring.IsSerreS`, full signatures,
  definitions and docstrings read. The former requires regular local rings at primes of height
  at most k; the latter bounds local depth below by the minimum of k and prime height.
- The normal-ring dependency is a Mathlib leaf with an inline match rather than a declaration:
  its recorded conjunction is used verbatim, as required by the standing NORMAL RING rule.

Edge cases checked before finalizing: the zero ring has no primes, so both normality and the
Serre conditions hold vacuously; it is not excluded by an added Nontrivial assumption. Fields
have dimension zero, regular prime localizations and the required depth-zero bound. Products
of normal domains are allowed because no global IsDomain is assumed. Dimension-one primes
require regularity and depth at least one. At dimension at least two the depth bound is two.
There is no finite-dimensional, finite-cardinality or characteristic restriction in the statement.

Searches for an existing statement:

- msearch LeanFinder, `Serre criterion normality Noetherian ring R1 S2`: eight hits about
  Noetherian spectra and finite-generation criteria; none gives normality iff R1 and S2.
- msearch LeanSearch, `A Noetherian ring is normal if and only if it satisfies Serre conditions
  R1 and S2`: service unavailable (Internal Server Error); no verdict assigned to this search.
- msearch Loogle, `IsNoetherianRing IsIntegrallyClosed IsSerreR IsSerreS`: malformed type-pattern
  query, no useful result. Retried as `IsIntegrallyClosed, IsNoetherianRing`: six results on
  discrete valuation rings and finite integral closure, none the full criterion.
- msearch grep, `Serre|serre|criterion.*normal` under Mathlib RingTheory: seven unrelated
  bibliographic hits, no normality criterion.
- rg, the same pattern, in WeilConjectures and lean/Sheaf: unrelated Serre duality/cohomology
  and uses of this DAG lemma in proof docstrings; the existing SerreConditions module supplies
  the two notions but no criterion theorem.
- grep for the exact item id in WeilConjectures: no result.
- rg for `serreCriterionNormal` in dag/lean_names_upstream.json, WeilConjectures, and lean/Sheaf:
  no result, so the chosen declaration name is not already used.

Validation: scompile.py compiles the final standalone module cleanly on the server, with
explicit universe and variable binders and only the required sorry theorem proof. The initially
considered named normality predicate was discarded before delivery, in accordance with the
standing instruction to use the inline normal-ring conjunction. No dependency node is changed.

## Second reading by M1

I independently opened the item node, its module, all three statement-dependency nodes,
`Sheaf.RingTheory.SerreConditions`, `Sheaf.RingTheory.Depth`, and the Mathlib declarations
below. There are no new nodes, dependency modules, or statement corrections in this delivery.

Source reading: the local Stacks checkout is absent. I read the actual upstream
[algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex),
labels `section-conventions`, `definition-conditions` (Tag 031P), and
`lemma-criterion-normal` (Tag 031S), including the whole proof. A scratch copy is in
`scratchpad/algebra.tex` and is not part of the delivery. The chapter convention admits
commutative unital rings, including the zero ring. No domain, field, characteristic,
finite-dimensionality, or local-ring assumption on R is implicit in the lemma.
The [rendered lemma](https://stacks.math.columbia.edu/tag/031S) agrees with that TeX.

Object/hypothesis/conclusion inventory and its exact Lean correspondence:

- Object R, a commutative unital ring: `(R : Type u) [CommRing R]`. Exact; `universe u`
  is explicit and arbitrary, and the ring need not be nontrivial or a domain.
- Hypothesis R is Noetherian: `[IsNoetherianRing R]`. Exact. I opened
  `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` abbreviates `IsNoetherian R R`,
  and `isNoetherianRing_iff_ideal_fg` identifies it with finite generation of every ideal,
  precisely `def-weil-pbc-noetherian-ring`.
- Primes p of R and their local rings: `∀ (p : Ideal R) [p.IsPrime]` and
  `Localization.AtPrime p`. Exact. I opened `Localization/AtPrime/Basic.lean`:
  this is `Localization p.primeCompl`; the prime binder supplies the required instance.
  No extra family of rings, algebra structures, or localization choices is assumed.
- Normality of each prime localization: `IsDomain (Localization.AtPrime p) ∧
  IsIntegrallyClosed (Localization.AtPrime p)`. Exact, including both clauses of
  `def-weil-pbc-normal-ring` and its recorded inline Mathlib match. I opened
  `IntegralClosure/IntegrallyClosed.lean`: `IsIntegrallyClosed` is integral closedness in
  `FractionRing`, and `isIntegrallyClosed_iff` gives the integral-element description
  for a domain. Normality is in the conclusion, not an additional assumption on R.
- Equivalence: `↔`. Exact; both directions are present, with normality on the left.
- First right-hand clause (R_1): `IsSerreR R 1`. Exact. The recorded declaration is
  `def IsSerreR (R : Type u) [CommRing R] [IsNoetherianRing R] (k : ℕ) : Prop`,
  with body `∀ (p : Ideal R) [p.IsPrime], p.height ≤ (k : ℕ∞) →
  IsRegularLocalRing (Localization.AtPrime p)`. Prime height is the local dimension;
  this restricts regularity to primes of height at most one. Mathlib's
  `IsRegularLocalRing` requires a Noetherian local ring whose maximal ideal has minimal
  generator number equal to its Krull dimension, the dependency's regular-local notion.
- Second right-hand clause (S_2): `IsSerreS R 2`. Exact. The recorded declaration is
  `def IsSerreS (R : Type u) [CommRing R] [IsNoetherianRing R] (k : ℕ) : Prop`,
  with body `∀ (p : Ideal R) [p.IsPrime], min (k : ℕ∞) p.height ≤
  IsLocalRing.depth (R := Localization.AtPrime p) (Localization.AtPrime p)`.
  This is depth of the local ring over itself, not depth of an arbitrary module.
  I opened the depth module: local depth is maximal-ideal depth, computed from regular
  sequence lengths, with infinity when the ideal spans the whole module. The self-module
  is finite automatically; no finite-module assumption is added to the theorem.
- Both right-hand clauses together: `IsSerreR R 1 ∧ IsSerreS R 2`. Exact; neither clause
  is omitted or moved into a hypothesis. All quantifiers are in the required scope.

Edge cases: the zero ring has no prime ideals, so all three universally quantified
conditions are vacuous and the equivalence includes it. An empty spectrum is thus covered.
Fields and height-zero primes require regularity and only the depth-zero bound; height-one
primes require regularity and depth at least one; higher-height primes require depth at
least two. Products and other rings with zero divisors are allowed, since only the local
normality conclusion requires domains. The fixed indices 1 and 2 do not introduce a variable
n or an n=0 restriction; the dependency definitions admit k=0. Empty schemes and arbitrary
index sets are not objects of this ring statement. There is no characteristic restriction.
Every type and instance binder and the single universe are bound explicitly.

Independent searches (different wording from the worker):

- msearch LeanFinder: `integrally closed prime localizations equivalent regular codimension
  one depth two`. Eight hits, including `IsIntegrallyClosed.of_localization`, its maximal
  variant, and Dedekind localization statements. Their displayed signatures impose a global
  domain or dimension-one condition and do not give the R_1/S_2 equivalence. No exact match.
- msearch Loogle: `IsIntegrallyClosed, Localization.AtPrime`. Two hits, the same integral
  closedness localization criteria; neither states this normality criterion. No exact match.
- msearch LeanSearch: `Normal commutative Noetherian rings characterized by local regularity
  in height one and depth at least two`. Service unavailable (Internal Server Error);
  no mathematical verdict is inferred from that failure.
- Independent rg over Mathlib RingTheory, WeilConjectures, project lean/Sheaf, and
  dag/lean_names_upstream.json for `normal.*criterion|criterion.*normal|IsSerre[RS]|
  regular in codimension|serre.{0,25}normal` (case insensitive): only the landed Serre
  definitions, docstring uses of this DAG lemma, and unrelated conormal/zeta criteria.
  There is no duplicate normality criterion to reuse. The new name is not occupied.

H5/H6/H8/H9: the delivery introduces one theorem and no definitions; its sole proof is
`by sorry`. The two imports supply the Serre predicates and integral closedness. Module and
statement docstrings carry Tag 031S and the exact blueprint id; namespace and paths follow
project conventions, with all lines at most 100 characters. I checked the proof docstring
against all ten DAG steps: docstring steps 1-4 render DAG steps 0-3, docstring step 5 renders
DAG steps 4-5 (the inductive claim and reducedness/base cases), and docstring steps 6-9 render
DAG steps 6-9. Thus the worker report's phrase “all nine steps of the DAG proof” miscounts
the DAG steps; the nine numbered docstring paragraphs do carry all ten DAG steps.

Findings and changes: no mathematical, signature, dependency, or module mismatch found.
The Lean and node are retained verbatim. This second-reading section adds the independent
correspondence, source-TeX reading, searches, edge cases, and the proof-step-count clarification.

Validation: second-reader scompile.py compiled the unchanged module on the server in
1.5 seconds, exit code 0, with no warnings or errors. An exact text comparison confirms
that lean.statement equals the theorem signature through the conclusion, before :=.
