## Worker report

The module `lean/Sheaf/RingTheory/SmoothNormalRing.lean` states
`RingHom.Smooth.isNormalRing`. It uses Mathlib's `RingHom.Smooth` for the
smooth homomorphism and writes the normal-ring predicate exactly as the
conjunction over all prime localizations from `def-weil-pbc-normal-ring`.

The binders `{R : Type uR}` and `{S : Type uS}` with `[CommRing R]` and
`[CommRing S]` introduce the two commutative rings. The binder
`{f : R →+* S}` and hypothesis `hf : f.Smooth` render the smooth ring map.
The hypothesis `hR` says for every prime ideal `p` of `R`, the localization
`Localization.AtPrime p` is a domain and integrally closed. The conclusion
is the same clause for every prime ideal `q` of `S`, hence says that `S` is a
normal ring.

Dependency declarations used:

- `def-weil-pbc-smooth-ring-map`: `Algebra.Smooth` in
  `Mathlib.RingTheory.Smooth.Basic`; the homomorphism form is Mathlib's
  `RingHom.Smooth` in `Mathlib.RingTheory.RingHom.Smooth`.
- `def-weil-pbc-normal-ring`: Mathlib declarations `IsDomain`,
  `IsIntegrallyClosed`, and `Localization.AtPrime`.

Edge cases checked: the quantifiers over prime ideals permit empty prime
spectra; no Noetherian, domain, or characteristic assumption was added; both
rings may be zero rings subject only to the stated hypotheses; universes for
`R` and `S` are explicit and independent.

Searches made: the node's recorded LeanSearch, LeanFinder, Loogle, and grep
searches (2026-10-10) found no Mathlib or project theorem asserting normality
ascent for smooth maps. I additionally searched the project with
`rg -n "Smooth R S|normal ring|IsIntegrallyClosed"` and found only the
separate etale analogue and component normality lemmas, not this declaration.
The module compiled successfully with `scompile.py`.

## Earlier second reading (a previous round; superseded)

I reread the node statement and the module signature clause by clause. The
source map `\varphi:R\to S` is represented by `f : R →+* S`, and smoothness is
exactly `f.Smooth`. The source normality hypothesis is rendered by `hR` with
all prime ideals and both domain and integral-closure clauses; the conclusion
quantifies over every prime of `S` with the identical two clauses. No source
hypothesis or conclusion was added, and no edge case was excluded. The only
change after this reading was adding the required blueprint marker to the
docstring and recording the signature without the proof body.

## Second reading by H1

I read the item node, both statement-dependency nodes, their Mathlib declarations,
and Stacks `algebra.tex` in the local source mirror
`/home/ubuntu/c1-stacks-review/`: conventions (lines 31 onward), definitions
0309, 00GV and 00T2, the smooth overview, and Lemma 033C with its proof
(lines 46563 onward). The tags table confirms these labels. The repository's
`literature/stacks-project/algebra.tex` is absent on this machine; the mirror
has the exact labels and line numbers cited by the node. The conventions
include the zero ring and impose no Noetherian or characteristic hypothesis.

Clause-by-clause inventory and verdicts:

- Objects R and S: `{R : Type uR} {S : Type uS} [CommRing R] [CommRing S]`.
  These are arbitrary commutative rings with identity, in independent universes.
  Matches the node and source.
- Ring homomorphism phi: `{f : R →+* S}`. Matches, with no injectivity,
  surjectivity or separate algebra structure assumed.
- Smoothness of phi: `(hf : f.Smooth)`. I opened
  `Mathlib/RingTheory/RingHom/Smooth.lean`: `RingHom.Smooth` is exactly
  `Algebra.Smooth R S` with `f.toAlgebra`. In `Smooth/Basic.lean`,
  `Algebra.Smooth` requires formal smoothness and finite presentation;
  `Algebra.FormallySmooth` requires projective Kaehler differentials and
  `Subsingleton (H1Cotangent R S)`. This is the dependency node's notion,
  including finite projectivity: `KaehlerDifferential.finite` in
  `Kaehler/Basic.lean:433` supplies finiteness from finite type, which follows
  from finite presentation. The canonical H1 is the kernel from the canonical
  presentation, as recorded by the dependency. No extra instance is required.
- Normality of R: `hR : ∀ (p : Ideal R) [p.IsPrime],
  IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
  Both clauses and every prime are present, exactly as def-weil-pbc-normal-ring
  and Stacks 00GV require. I opened `Localization/AtPrime/Basic.lean:57`:
  `Localization.AtPrime p` is localization at `p.primeCompl`. I opened
  `IntegralClosure/IntegrallyClosed.lean:74`: `IsIntegrallyClosed` means
  integral closure in `FractionRing`. Together with `IsDomain` this is
  precisely a normal domain (0309), not normality in a fixed ambient field.
- Conclusion: `∀ (q : Ideal S) [q.IsPrime],
  IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)`.
  Every prime localization of S is both a domain and integrally closed.
  Matches all of the conclusion, with the quantifiers after the two hypotheses.

Edge cases: no `Nontrivial R` or `Nontrivial S` binder excludes the zero ring.
An empty prime spectrum makes its normality quantifier vacuous, as in 00GV;
if R is zero, a unital map forces S to be zero as well. Neither R nor S is
assumed to be a domain globally, so disconnected normal rings are covered.
There is no field, Noetherian, characteristic, dimension or nonzero relative
rank assumption. Relative dimension zero and presentations with zero variables
are allowed by Mathlib smoothness. There is no scheme or auxiliary index set
in this statement. All variables and both universes are explicitly bound.

Independent searches (via msearch.py, logged in searches.jsonl):

- LeanSearch: "A finitely presented formally smooth extension of a ring whose
  prime local rings are integrally closed domains has normal local rings".
  Service returned Internal Server Error; no result or negative verdict inferred.
- Loogle: `RingHom.Smooth, IsDomain` returned no hits.
- LeanFinder: "Localizations at primes of a smooth algebra over a normal
  commutative ring are integrally closed integral domains" returned eight hits,
  including `IsIntegrallyClosed.of_localization_maximal` and smooth-localization
  results. None states normality ascent; the former only reconstructs integral
  closure of a domain from its own maximal localizations.
- Mathlib grep: `smooth.*(normal|integrallyClosed)|
   (normal|integrallyClosed).*smooth|033C|normal.goes.up` in RingTheory returned
  no hits. Separate rg of the upstream WeilConjectures and repository Sheaf
  sources for smooth/normal combinations, Tag 033C and the full declaration
  name found special cases for curves, the etale analogue, and references to
  this node, but no declaration of this general smooth ring-map assertion.
  Thus no existing declaration can replace this module. The two dependency
  notions are reused, with no new definition node or dependency module needed.

Mismatch and repairs: no mathematical signature mismatch was found; the node
and `lean.statement` are unchanged. The old proof docstring compressed all seven
node steps into four sentences and omitted the normalization system and the
colimit universal property (H8). I replaced it with seven numbered steps naming
the supporting DAG nodes, including the elementwise construction in step 6.
I added the project copyright/license/author header from the example and made
both source blueprint markers contiguous. No definition was introduced, and
the sole theorem remains `by sorry`; there is nothing proved at this stage.
The three imports serve smoothness, integral closure and prime localization.

Validation: scompile.py compiled the repaired module on the server in 1.6 s,
exit code 0 with no errors or warnings. The signature in the node copy is
verbatim the theorem signature before `:= by`; all Lean lines are at most
100 characters. Delivery preflight is run after this reading.
