## Worker report

The module `Sheaf.RingTheory.QuasiFiniteFourRings` states
`Algebra.finiteType_and_isQuasiFiniteAtPrime_of_four_rings`, with its sole proof `sorry`.
The node is unchanged except for its `lean` record. No new notions, dependency modules,
or statement corrections are needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The four commutative rings are `(R : Type u) (S : Type v) (R' : Type w) (S' : Type z)`
  with their four `CommRing` instances. Their universes are independent and explicitly bound.
- The maps R → S, R → R', R' → S' are the algebra maps of `[Algebra R S]`,
  `[Algebra R R']`, `[Algebra R' S']`. These are exactly arbitrary unital ring homomorphisms
  between commutative rings, with no injectivity or other condition. The fourth map is
  `(σ : S →+* S')`.
- Equality of the two composites is `hcomm`, evaluated on every `r : R`.
- Finite type of R → S is `[Algebra.FiniteType R S]`.
- Generation of S' by finite sums of products is `hgen`: every x has an n and families
  `s : Fin n → S`, `r : Fin n → R'` with
  `x = ∑ i : Fin n, σ (s i) * algebraMap R' S' (r i)`.
  This is the node's explicit finite-sum formulation, so no tensor-map definition is needed.
- The unconditional finite-type conclusion is `∃ hft : Algebra.FiniteType R' S', ...`.
  The witness also supplies the finite-type argument required by the dependency's definition.
- An arbitrary prime q' is `q' : PrimeSpectrum S'`. Its inverse image q is `q'.comap σ`.
  The other inverse image p' is determined by `q'.comap (algebraMap R' S')`; the node
  names it but makes no additional assertion about it, so no extra free prime or condition
  is introduced. It is used internally by the target quasi-finiteness definition.
- The quasi-finiteness hypothesis at q is `IsQuasiFiniteAtPrime R S (q'.comap σ)`.
- Quasi-finiteness at q' is `@IsQuasiFiniteAtPrime R' S' _ _ _ hft q'`. The explicit
  finite-type witness avoids a let binder and uses exactly the recorded isolated-fibre-point
  definition, not Mathlib's localization-based `QuasiFiniteAt`.
- The existential finite-type witness precedes the universal prime and implication: finite
  type is concluded even when the quasi-finiteness hypothesis fails or no prime exists.

Dependencies read in full:

- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`,
  `Algebra.FiniteType`. The class means the top subalgebra is finitely generated.
  Its docstring and signature were read in pinned Mathlib's FiniteType.lean.
- `def-weil-pbc-ring-map-quasi-finite-at-prime`: `Sheaf.RingTheory.QuasiFiniteAtPrime`,
  `Algebra.IsQuasiFiniteAtPrime`. The full definition and docstring were read: the contraction
  p and `PrimeSpectrum.preimageHomeomorphFiber` give the corresponding fibre prime, whose
  singleton is required to be open. This import also exposes `Algebra.FiniteType`.
- `Mathlib.Algebra.BigOperators.Ring.Finset` supplies the finite sum notation in `hgen`.

The module docstring names Stacks 00PN, and the theorem docstring records all eight proof
steps and their non-elementary DAG inputs. No proof is implemented.

Edge cases checked before writing:

- `n = 0` is allowed, so an empty sum gives zero; no nonempty generator assumption appears.
- Zero rings are allowed; if S' is zero its spectrum has no primes, but finite type is still
  the unconditional conclusion. No field/domain/characteristic hypotheses are added.
- Non-injective and non-surjective individual arrows are allowed; the only generation
  condition is the specified finite-sum condition.
- Arbitrary primes, not only maximal primes, are quantified. Contraction under σ always
  gives a prime. No auxiliary choice of primes restricts the statement.
- All four ring universes are explicit; the hypothesis quantifies only over actual elements
  of S', so there is no undersized test-object universe.

Searches for an existing statement (real calls recorded in searches.jsonl):

- LeanFinder: `commutative square of rings with surjective tensor product map preserves
  finite type and quasi-finiteness at a prime`: eight hits, including
  `Algebra.QuasiFiniteAt.baseChange` and `.of_surjectiveOnStalks`; none is this full statement.
- Loogle: `Algebra.QuasiFiniteAt, Function.Surjective`: two hits, a fibre-to-residue-field
  surjection and a polynomial kernel lemma; neither is a four-ring statement.
- Mathlib grep through msearch: `four.rings|QuasiFiniteAt.baseChange|QuasiFiniteAt.of_surjective`
  in RingTheory: six hits, base-change and surjective-on-stalks lemmas and comments.
  Their signatures and QuasiFiniteAt's docstring were read in QuasiFinite/Basic.lean:
  they use the localization-based notion and would need composition and an equivalence.
- LeanSearch: `quasi-finite at prime four rings surjective tensor product base change`:
  service unavailable (Internal Server Error); no verdict inferred from that search.
- Direct rg in source WeilConjectures, project lean/Sheaf and dag/lean_names_upstream.json:
  `four.rings|finiteType_and_isQuasiFiniteAtPrime|quasi.finite.*square` found only related
  finite/étale statements, docstring mentions and a scheme base-change lemma, no exact match.
- Direct rg for this item's id in source WeilConjectures found no declaration.
- Direct rg for `IsQuasiFiniteAt|quasiFiniteAt|QuasiFiniteAt` in project and source RingTheory
  identified the existing dependency module and related statements; none gives this square.

Source verification: literature/stacks-project/algebra.tex is absent on this machine.
The canonical source https://stacks.math.columbia.edu/tag/00PN was opened and checked:
its square, finite-type hypothesis, tensor-map surjectivity and quasi-finiteness implication
agree with the node. The node spells out the equivalent finite-sum hypothesis and the
finite-type conclusion implicit in the source. No node fault or STATEMENT-DISPUTED issue found.

Validation: the final module compiled cleanly on the server. The delivery dry run printed
OK: compilation and preflight passed, except for the independent second reading, which
the second reader supplies. Earlier line-length warnings in the proof docstring were repaired.
Nothing was pushed.

## Second reading by C1

I independently opened the item node, both statement-dependency nodes, their actual Lean
signatures and docstrings, and the delivered module. There are no new definition nodes,
dependency modules, or statement corrections in this delivery. The following is my list of
the node's objects, hypotheses, and conclusions, with the Lean correspondence and verdict.

1. Four commutative unital rings R, S, R', S': the four explicit `Type u/v/w/z` binders
   and four `CommRing` instances. Exact; zero rings and independent universes are allowed.
2. Ring maps R → S, R → R', R' → S', S → S': the three `Algebra` instances and
   `σ : S →+* S'`. Exact. On commutative rings an algebra structure represents an arbitrary
   unital ring map, with its associated scalar action; no injectivity, flatness, or extra
   scalar-tower instance is required.
3. Equality of the composites R → S': `hcomm : ∀ r : R, ...`. Exact pointwise equality
   of precisely these maps, not an additional compatibility with an unrelated action.
4. Finite type of R → S: `[Algebra.FiniteType R S]`. Exact. I read Mathlib's class,
   whose field is `(⊤ : Subalgebra R S).FG`, and the dependency node's generator formulation.
   This is algebraic generation, not module finiteness or finite presentation.
5. Every element of S' is a finite sum of products from the images of S and R': `hgen`
   quantifies over every `x : S'`, chooses `n : ℕ`, `s : Fin n → S`, `r : Fin n → R'`,
   and asserts the displayed sum equality. Exact, including the empty sum. The node explicitly
   states this equivalent form of tensor-map surjectivity, so no tensor-map notion is missing.
6. Unconditional finite type of R' → S': `∃ hft : Algebra.FiniteType R' S', ...`.
   Exact. Its position before `∀ q'` makes finite type unconditional, including empty spectra.
   The witness is a proof of a Prop class, not an additional algebra structure or assumption.
7. Arbitrary prime q' of S', with contractions q in S and p' in R': `∀ q' : PrimeSpectrum S'`
   and `q'.comap σ` give q' and q. The contraction p' is
   `q'.comap (algebraMap R' S')`; it is determined by q' and appears inside the target fibre
   definition. Exact: no assertion about an independently chosen p' has been omitted.
8. Quasi-finiteness at q implies quasi-finiteness at q':
   `IsQuasiFiniteAtPrime R S (q'.comap σ) → @IsQuasiFiniteAtPrime R' S' _ _ _ hft q'`.
   Exact. I read the actual dependency definition: it contracts the prime, uses
   `PrimeSpectrum.preimageHomeomorphFiber`, and asks that the corresponding singleton in
   `PrimeSpectrum (p.asIdeal.Fiber S)` be open. I also read Mathlib's homeomorphism signature
   and `Ideal.Fiber = κ(p) ⊗[R] S`; the tensor-factor swap from the node is canonical.
   The explicit `hft` supplies the required finite-type proof without a statement-level let.

Source check: the local Stacks .tex is absent. I opened the canonical pages
[Tag 00PN](https://stacks.math.columbia.edu/tag/00PN) and
[Tag 00PL](https://stacks.math.columbia.edu/tag/00PL), and independently fetched and read
`lemma-four-rings` and its proof in the upstream `algebra.tex` at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex.
I also read that file's Conventions: rings are commutative with 1, zero rings are included,
and contraction notation does not imply injectivity. No standing Noetherian, field,
characteristic, or other hypothesis is missing. The node's explicit finite-type conclusion
follows from finite algebra generators and the surjective tensor map; its eight-step proof
is represented in order in the theorem docstring.

Edge cases: `Fin 0` admits the empty sum, giving zero. No ring has a `Nontrivial`, domain,
field, or characteristic restriction. A zero S' has empty spectrum but still receives the
finite-type witness. There is no empty underlying ring type (unital rings have zero), so
no relevant empty-object case is lost. Primes need not be maximal. Ring universes are
independent and explicitly bound, and there is no universe-restricted test-object quantifier.
Neither individual arrow surjectivity nor nonempty generators are assumed.

Independent searches (real msearch calls, recorded in searches.jsonl):

- LeanFinder: `Surjective algebra generated by two compatible ring images preserves isolated
  points in fibres`: eight results, including spectrum surjectivity and polynomial lemmas;
  no four-ring statement with this conclusion.
- Loogle: `Algebra.QuasiFiniteAt`: twelve results. I opened the pinned Mathlib definitions
  and the signatures of `Algebra.QuasiFiniteAt.baseChange` and
  `Algebra.QuasiFiniteAt.of_surjectiveOnStalks`. The former has a tensor-product target;
  the latter has a fixed base and a stalk-surjective algebra homomorphism. Neither is this
  combined four-ring statement or concludes target finite type. These are potential proof
  ingredients, not an exact existing declaration.
- Grep through msearch: `QuasiFiniteAt|quasi.finite.*surject|four.ring` in
  `RingTheory/QuasiFinite`: fifteen hits locating those definitions and related lemmas.
- Direct rg with `QuasiFiniteAt|four.?rings|IsQuasiFiniteAtPrime` across source
  `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`: the recorded
  quasi-finiteness definition and related statements, but no exact four-ring theorem.
- LeanSearch: `A finite type ring map remains finite type and quasi finite at a contracted
  prime in a commutative square with surjective tensor map`: Internal Server Error,
  recorded as unavailable; no negative verdict inferred from it.

H4/H5/H6/H8/H9 check: both recorded dependency declarations are used, no private notion
or hollow definition is introduced, the only proof is the named theorem's `sorry`, both
source-bearing docstrings have the correct blueprint id, and all eight proof steps and
non-elementary inputs are present. The explicit universes and binders leave nothing unbound.
The node's `lean.statement` matches the file signature verbatim after whitespace normalization;
all lines are at most 100 characters. Imports supply the quasi-finiteness definition and sums.

Mismatches and changes: none found in the Lean or the node; both are retained unchanged.
This second-reading section and independent search records are the only additions.

Second-reader validation: scompile of the absolute sandbox module path succeeded on the
server in 1.4 seconds, with no errors or warnings. The first invocation used a relative
path from the read-only repository and failed to locate the sandbox file; using the actual
sandbox path corrected that invocation without changing any file or bypassing the tool.

## Reviewer fix (R-qfr1549)

The fourth map `σ : S →+* S'` and the pointwise `hcomm` were replaced by `[Algebra S S']`
`[Algebra R S']` `[IsScalarTower R S S']` `[IsScalarTower R R' S']`, the scalar-tower form
of a commutative square used by the landed sibling `IsQuasiFiniteAtPrime.of_restrictScalars`
(M1 165becf79). `hgen` and the contraction now use `algebraMap S S'`. The statement is
equivalent: the two towers say exactly that both composites equal `algebraMap R S'`.
