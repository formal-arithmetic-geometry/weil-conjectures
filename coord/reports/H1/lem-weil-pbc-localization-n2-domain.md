## Worker report

The module `Sheaf.RingTheory.LocalizationJapaneseDomain` states
`localization_isN1_isN2`, with a single `sorry` and no definitions or proved lemmas.
The node statement is unchanged. No new nodes or dependency modules are needed.

Hypothesis and conclusion correspondence:

- The integral domain R is `(R : Type u) [CommRing R] [IsDomain R]`.
- Its fraction field K is `(K : Type v) [Field K] [Algebra R K]
  [IsFractionRing R K]`; this fixes the embedding R into K.
- The multiplicatively closed subset containing one is `(S : Submonoid R)`;
  closure and membership of one are part of that existing Mathlib structure.
- The exclusion of zero is `(hS : (0 : R) ∉ S)`.
- The localization is `(A : Type w) [CommRing A] [Algebra R A]
  [IsLocalization S A]`. This is Mathlib's universal-property presentation of
  the same ring localization, allowing any model of S⁻¹R. In particular take
  `A = Localization S`, which is definitionally `LocalizedModule S R` (see
  `example_localization_eq_localizedModule` in the recorded dependency's
  `Mathlib.Algebra.Module.LocalizedModule.Basic`). No private localization is defined.
- The conclusion that A is a domain is the existential `hD : IsDomain A`,
  installed with `letI := hD`; it is not an assumed instance.
- The map into K is the existential `a : Algebra A K`. Its algebra map is
  required to satisfy `IsScalarTower R A K` and the formula for EVERY
  `r : R` and `s : S`:
  `algebraMap A K (IsLocalization.mk' A r s) =
  algebraMap R K r / algebraMap R K (s : R)`.
  Every element of A has such a presentation, so this specifies exactly the
  canonical map r/s ↦ r/s, not an arbitrary embedding.
- Its injectivity is `Function.Injective (algebraMap A K)`.
- That the map identifies K as the fraction field of A is the existential
  `hF : IsFractionRing A K`, with respect to that SAME algebra map. Its local
  instance supplies the typeclass required in the following two conclusions.
- Clause (1) is `IsN1 R K → IsN1 A K`.
- Clause (2) is `IsN2 R K → IsN2 A K`.

Dependency declarations read and used:

- `Sheaf.RingTheory.JapaneseDomain`: `IsN1` and `IsN2`, full definitions read.
  These use `integralClosure` and `Module.Finite`; `IsN2` quantifies over finite
  extensions L of K with the composite R-algebra structure (`IsScalarTower`).
  `isN1_of_isN2` was also read, but is not needed for the signature.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`, its docstring,
  `mk`, and `mk_eq` read. Its ring specialization is the existing `Localization S`.
  The theorem uses Mathlib `IsLocalization S A` to cover every representation of
  that object; `IsLocalization.mk'` is its fraction constructor. The import of
  JapaneseDomain already supplies the ring-localization definitions, so there
  is no redundant direct import of the module-localization file.

Source read: [Stacks Tag 032G](https://stacks.math.columbia.edu/tag/032G),
Lemma 10.161.3, states preservation of N-1 and N-2 under localization;
its proof cites [Tag 0307](https://stacks.math.columbia.edu/tag/0307),
Lemma 10.36.11, for integral closure commuting with localization. The local
`literature/stacks-project/algebra.tex` is absent on this machine, so both tags
were opened online. The declaration docstring carries all four steps of the
node proof, including the unchanged fraction field, localization of extension
fields, the explicit finite-generator calculation, and the two applications.

Edge cases checked before writing: S = {1} gives the original domain; S all
nonzero elements gives K; when R is already a field every permitted localization
is R. S cannot be empty because it contains one. A zero localization is excluded
by the domain hypothesis and 0 ∉ S; no conclusion assumes nontriviality of A.
There is no characteristic, Noetherian, normality, or separability restriction.
The three carrier universes u, v, w are independent; no small-universe test
algebra quantifier was introduced. The N-2 conclusion uses the same K and its
recorded definition, hence precisely the same finite extensions as the premise.

Searches actually run with `msearch.py H1 lem-weil-pbc-localization-n2-domain`:

- `leanfinder`: `localization of a Japanese N-2 domain is Japanese and localization
  has the same fraction field`. Eight hits: fraction-field localization and
  integral-closure facts, but no N-1/N-2 theorem.
- `loogle`: `IsLocalization, IsFractionRing`. Twelve hits including
  `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization` and
  `Localization.mapToFractionRing`; neither includes N-1 or N-2 preservation.
- `grep`: `IsN1|IsN2|Japanese|isFractionRing`, restricted to
  `RingTheory/Localization`. Twenty-five hits, fraction-ring ingredients only.
- `leansearch`: `localization of an N-2 Japanese domain remains N-2`.
  Service unavailable (Internal Server Error); recorded in searches.jsonl.
- Local `rg -n 'IsN1|IsN2|Japanese|localization_n2'` on source
  `WeilConjectures` and project `lean/Sheaf`: only the Japanese-domain definition
  and unrelated uses in the project; no localization-preservation theorem.
- `grep -rn 'lem-weil-pbc-localization-n2-domain'` on source `WeilConjectures`:
  no match. `rg` on `dag/lean_names_upstream.json` for the item and IsN1/IsN2:
  no match. The declaration name is new in the searched source and project.

Server compile: `scompile.py H1 lem-weil-pbc-localization-n2-domain
< sandbox >/lean/Sheaf/RingTheory/LocalizationJapaneseDomain.lean` exited 0,
compiled in 1.4 seconds, no warnings or errors. Every universe and variable is
explicitly bound and `autoImplicit` is disabled in the module.

## Second reading by H1

I read the node as introducing an integral domain R, its fraction field K, a
multiplicative submonoid S avoiding zero, and the specific localization
`S⁻¹R`; its conclusions are that this localization is a domain, embeds in K by
r/s ↦ r/s, has fraction field K, and preserves N-1 and N-2. The Lean binders
`R`, `K`, `[CommRing R] [IsDomain R]`, `[Field K] [Algebra R K]
[IsFractionRing R K]`, `S`, and `hS` render these hypotheses. The existential
`hD`, algebra map `a`, fraction-field instance `hF`, scalar tower, injectivity,
explicit fraction formula, and the two implications render the domain, canonical
map, unchanged fraction field, and N-1/N-2 clauses.

The worker statement quantified over an arbitrary carrier `A` with
`[IsLocalization S A]`, which is stronger than the node's specified
`S⁻¹R` and introduced an extra object absent from the source. I changed it to
use Mathlib's `Localization S` throughout, preserving the same universal
property and the exact source object. The node copy was updated verbatim to the
repaired signature. No other mismatches were found.

Edge cases checked: S contains 1 and is therefore nonempty; hS excludes the
zero localization, S={1} gives R, and inverting all nonzero elements gives K.
The statement has no characteristic, Noetherian, separability, or nonzero-extra
hypothesis, and its universes cover arbitrary R and K.

Searches found no existing N-1/N-2 localization theorem in Mathlib or
WeilConjectures; grep, LeanFinder/Loogle, and msearch.py searches found only
localization and integral-closure ingredients. The module compiles cleanly with
`scompile.py`.
