## Worker report

The module `Sheaf.RingTheory.AssociatedLocalizationFg` states
`Module.exists_annihilator_eq_of_localization_atPrime`, with a `sorry` proof only.
It states the node exactly and requires no new definitions or dependency modules.

Hypotheses and clauses, matched individually:
- The commutative ring R is `{R : Type u} [CommRing R]`.
- The arbitrary R-module M is `{M : Type v} [AddCommGroup M] [Module R M]`.
  No finiteness or faithfulness of M is assumed.
- The ideal p is `(p : Ideal R)`, primality is `[p.IsPrime]`, and finite generation
  of that ideal alone is `(hp : p.FG)`; R need not be Noetherian.
- The ring R_p is `Localization.AtPrime p` and the module M_p is
  `LocalizedModule.AtPrime p M`, definitionally `LocalizedModule p.primeCompl M`.
- The premise that the maximal ideal is the annihilator of an element is the
  existential `h : ∃ z : LocalizedModule.AtPrime p M, ...`, with equality of
  `IsLocalRing.maximalIdeal (Localization.AtPrime p)` and
  `(⊥ : Submodule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).colon {z}`.
  By `Submodule.mem_colon_singleton` and membership in bottom, this colon ideal
  consists exactly of the scalars killing z. No radical is taken.
- The conclusion is `∃ m : M, p = (⊥ : Submodule R M).colon {m}`, exactly the
  existence of an element with annihilator p. Reversing the equality would
  describe the same equality of ideals.

Dependency declarations read and used:
- `def-weil-pbc-localization-at-prime` is a Mathlib leaf. Its applicable recorded
  declaration is `Localization.AtPrime` in `Mathlib.RingTheory.Localization.AtPrime.Basic`:
  it is the localization at `p.primeCompl`, with its canonical local-ring structure.
  The record's other clauses `Ideal.ResidueField` and `Ideal.Fiber` were also read;
  they are irrelevant to this node's statement and are not imported.
- `def-weil-pbc-module-localization` is a Mathlib leaf whose record is
  `LocalizedModule` in `Mathlib.Algebra.Module.LocalizedModule.Basic`.
  `Mathlib.Algebra.Module.LocalizedModule.AtPrime` provides the existing abbreviation
  used here; it has exactly the complement-of-p multiplicative subset.
- `Submodule.colon` and `mem_colon_singleton` in `Mathlib.RingTheory.Ideal.Colon`
  supply the annihilator of a singleton; `Ideal.FG` in
  `Mathlib.RingTheory.Finiteness.Defs` supplies finite generation.

Sources checked: the local Stacks TeX file is not present on this machine, so
read https://stacks.math.columbia.edu/tag/0310 (clause (2) and its denominator-clearing
proof) and https://stacks.math.columbia.edu/tag/058A (its final descent step).
Tag 0310 is currently numbered Lemma 10.63.15; the stable tag identifies the intended
result despite the node's older numerical reference. The declaration docstring
contains all three proof steps from the node, naming both dependency ids.
No statement correction or dispute is needed.

Edge cases checked before writing:
- The zero module cannot satisfy the premise: its elements have annihilator top,
  whereas a local ring's maximal ideal is proper. No unnecessary nonzero binder is added.
- The zero ring has no prime ideal and hence no instance `[p.IsPrime]`; no case
  covered by the node is lost.
- p = 0 is allowed when prime. Its empty generating family gives the empty
  product 1 in the proof. Over a domain the premise yields an element with zero
  annihilator; the same statement covers this case.
- All characteristics, non-Noetherian rings, and modules that are not finitely
  generated remain allowed. R and M have separately bound universes u and v;
  the localized module lives in their maximum, with no equality constraint.

Searches for an existing statement:
- `msearch.py ... leanfinder` query: "If a finitely generated prime ideal is the
  annihilator of an element after localization at that prime, it is the
  annihilator of an element before localization". Eight hits. Closest:
  `Module.associatedPrimes.comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg`.
  Reading its signature and the definitions in AssociatedPrime/Basic.lean shows
  it concludes equality with a radical, not equality with the annihilator itself.
  `isAssociatedPrime_iff` removes that radical only under `IsNoetherianRing R`,
  a hypothesis this node does not have. It is not an exact existing statement.
- `msearch.py ... loogle` query `LocalizedModule, Submodule.colon`: two hits, both
  primary-decomposition results in Mathlib.RingTheory.Lasker, not this statement.
- `msearch.py ... grep` query `annihilator|colon|associatedPrimes` restricted to
  RingTheory/Ideal/AssociatedPrime: fifteen hits including the localization theorem
  and the radical-based definition; none states this radical-free conclusion.
- `msearch.py ... leansearch` query "finitely generated prime ideal annihilator of
  element localization at prime": service unavailable, Internal Server Error.
- Direct `rg` over Mathlib/Algebra/Module/LocalizedModule and Mathlib/RingTheory for
  `exists.*colon|colon.*exists|annihilator.*localiz|localiz.*annihilator` found
  Noetherian minimal-prime and primary-decomposition lemmas, not this result.
- Direct `rg` over WeilConjectures and lean/Sheaf for the node id and
  `annihilator.*localiz|localiz.*annihilator|associated.*localiz`: no matches.
  Search for the chosen name and module name in these roots and
  dag/lean_names_upstream.json also returned no matches.

Validation: server single-file compilation succeeded (exit code 0, 1.2 seconds)
with no errors or warnings. `deliver2.py J1 lem-sc-associated-localization-fg --no-push`
printed OK: compilation and preflight passed except for the second reading,
which the independent second reader supplies. Nothing was pushed.


## Second reading by J1

Independent second reading: I opened the node copy, its Lean module, both
statement-dependency nodes and the Mathlib declarations they record. Verdict:
the Lean states exactly the node; no statement, dependency or module repair is
needed. The only change is this independent review section.

Objects, hypotheses and conclusion, enumerated before comparison:

1. A commutative unital ring R: `{R : Type u} [CommRing R]`. Exact.
2. An arbitrary R-module M: `{M : Type v} [AddCommGroup M] [Module R M]`.
   Exact; neither finite generation of M nor a Noetherian ring is required.
3. An ideal p of R, prime and finitely generated: `(p : Ideal R) [p.IsPrime]
   (hp : p.FG)`. Exact. Mathlib `Ideal.FG` is existence of a finite set spanning
   the ideal, not finite presentation or finite generation of the ring.
4. R_p and M_p, localized at the complement of p:
   `Localization.AtPrime p` and `LocalizedModule.AtPrime p M`. Exact.
   I read `Localization.AtPrime` in Localization/AtPrime/Basic.lean: it is
   `Localization p.primeCompl`, with its canonical local-ring instance;
   `Localization.AtPrime.map_eq_maximalIdeal` identifies the displayed maximal
   ideal with the extension of p. I read `LocalizedModule` in
   Algebra/Module/LocalizedModule/Basic.lean and the AtPrime abbreviation:
   `LocalizedModule.AtPrime p M = LocalizedModule p.primeCompl M`, the fraction
   module with the canonical scalar action of the localized ring. These are
   precisely the applicable clauses of def-weil-pbc-localization-at-prime and
   def-weil-pbc-module-localization; no substitute definitions are introduced.
5. Premise: an element z of M_p with annihilator the maximal ideal of R_p:
   `h : ∃ z : LocalizedModule.AtPrime p M,
   IsLocalRing.maximalIdeal (Localization.AtPrime p) =
   (⊥ : Submodule (Localization.AtPrime p)
   (LocalizedModule.AtPrime p M)).colon {z}`. Exact. I read `Submodule.colon`
   and `mem_colon_singleton` in Ideal/Colon.lean: membership means that the
   scalar times z is in bottom, hence zero. There is no radical or weaker
   annihilator containment. The existential occurs after R, M, p and hp.
6. Conclusion: an element m of M with annihilator exactly p:
   `∃ m : M, p = (⊥ : Submodule R M).colon {m}`. Exact, using the same
   singleton-annihilator construction and the original module action.

Source reading: the repository's Stacks TeX is absent locally. I fetched the
upstream algebra.tex into the item's scratchpad and read the conventions
(lines 30-42), lemma-associated-primes-localize and its proof (15394-15421),
and lemma-ass-weakly-ass and its proof (16109-16144). I also opened stable
[Tag 0310](https://stacks.math.columbia.edu/tag/0310) and
[Tag 058A](https://stacks.math.columbia.edu/tag/058A). The ring conventions
include the zero ring and impose commutativity and a unit; neither lemma's
relevant implication assumes Noetherianity. Tag 0310(2) is precisely this
finitely generated prime descent, and Tag 058A uses it after producing an
exact annihilator in the localized module. No node correction is needed,
so there is no statement_change or corrected-citer audit to perform.

Edge cases: p = bottom is allowed when prime, including an empty generating
family (n = 0); the denominator product is then 1. The zero module and zero
localized module cannot meet the exact-annihilator premise, since their
annihilator is top while the maximal ideal is proper. The zero ring has no
prime ideal, as in the source, so no omitted applicable case results from
[p.IsPrime]. No characteristic, domain, field, nonzero-module or Noetherian
hypothesis is added. The universes u and v are explicitly bound independently;
the localized module is in Type (max u v). There is no scheme or external
index set in this statement, so empty schemes are inapplicable.

Independent searches (different wording from the first reader):

- LeanFinder via msearch: "Exact annihilator of a vector descends from the
  localized module when the prime ideal has finite generators". Eight hits;
  the closest is the associatedPrimes localization descent theorem. I opened
  AssociatedPrime/Localization.lean and Basic.lean: its conclusion uses
  `IsAssociatedPrime`, defined by equality with a RADICAL of an annihilator.
  The radical-free equivalence `isAssociatedPrime_iff` requires
  `IsNoetherianRing R`. Thus this candidate is not this node's statement.
  The other hits concern exact sequences or support containment.
- Loogle via msearch: `IsLocalRing.maximalIdeal, Submodule.colon`: zero hits.
- LeanSearch via msearch: "annihilator equality before localization finitely
  generated prime ideal": unavailable, Internal Server Error; no verdict
  inferred from the unavailable service.
- Grep via msearch: `0310|exists.*annihilator|annihilator.*exists`, restricted
  to Mathlib/RingTheory/Ideal/AssociatedPrime: zero hits reported.
- Direct rg across all Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json for `colon.*[Ll]ocal|[Ll]ocal.*colon|
  annihilator.*[Aa]tPrime|[Aa]tPrime.*annihilator` and the full proposed
  declaration name. Mathlib hits were the radical-based localization proofs.
  Source hits led to `Ideal.map_colon_of_isLocalization`; I opened its
  declaration in WeilConjectures/Mathlib/RingTheory/Localization/Ideal.lean.
  It concerns localization of the colon of TWO IDEALS, not annihilators of
  elements of arbitrary modules or existence of a descended witness.
  No exact existing statement or declaration-name collision was found in
  the source repository or project Lean. All notions already come from Mathlib;
  there are no new definition nodes or dependency modules to audit.

H5/H6/H8/H9: the module introduces no definition, hollow or otherwise, and
its only theorem has proof `by sorry`. Both docstrings name Tag 0310(2),
Tag 058A and the exact blueprint id. The theorem docstring reproduces all
three node steps: contraction of the original annihilator, clearing one
denominator per generator and multiplying them, and the two inclusions
using primality. The imports supply the four notions actually used. The
namespace is Module, all variables and universes are bound, every Lean line
is at most 100 characters, and the node's lean.statement is verbatim equal
to the signature extracted from the file. No mismatch was found or silently
changed. Compilation and delivery checks follow this review.
