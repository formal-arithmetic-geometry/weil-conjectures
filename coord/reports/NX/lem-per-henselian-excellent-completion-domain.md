## Worker report

The module `Sheaf.RingTheory.HenselianExcellentCompletionDomain` states
`AdicCompletion.isDomain_of_henselian_excellent`. Its sole theorem has proof `sorry`;
there are no definitions, auxiliary theorems, new nodes, or dependency repairs.
The node is changed only in `lean`.

I read the node's entire statement and six proof steps and all four statement
dependency records and their declarations. I also read the proof dependency records
to select the available proof imports. The source was opened locally using
`pdftotext -layout` on
`literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`:
Exposé I, Proposition 6.2 and Corollary 6.3(i)-(ii), printed p. 14, and the invocation
at the beginning of Exposé III, Proposition 3.1, printed p. 37. The source says
that a henselian excellent local Noetherian integral ring has integral completion.
No source or statement correction is needed.

Hypotheses and conclusion, clause by clause:

- A commutative ring A: `(A : Type u) [CommRing A]`, with `universe u` explicit
  and `set_option autoImplicit false`.
- Excellent: `(hA : IsExcellent A)`, using precisely the recorded definition
  `IsExcellent` from `Sheaf.RingTheory.ExcellentRing`. This unfolds to
  quasi-excellence and universal catenarity; no stronger regularity or normality
  condition is assumed.
- Henselian and local: `[HenselianLocalRing A]`. This recorded Mathlib class
  extends `IsLocalRing A`, so the unique maximal ideal is
  `IsLocalRing.maximalIdeal A`. No separate choice of ideal or locality assumption
  is needed. The dependency's recorded upstream module publicly imports the
  Mathlib class. Its root-lifting definition is the henselian notion used by the
  dependency record; its note explains the equivalence with the node's idempotent
  wording.
- Noetherian: `[IsNoetherianRing A]`, retained explicitly because the node states
  it explicitly, using the recorded Mathlib abbreviation meaning all ideals are
  finitely generated. Excellence also entails this condition.
- Integral domain, including nonzero one and the product condition:
  `[IsDomain A]`. With `CommRing`, Mathlib's `IsDomain` is the integral-domain
  mixin, extending multiplicative cancellation away from zero and `Nontrivial`;
  it is equivalent to the node's nonzero-one and no-zero-divisors wording.
- Maximal-ideal-adic completion: the literal type
  `AdicCompletion (IsLocalRing.maximalIdeal A) A`, using the recorded
  `AdicCompletion` from `Mathlib.RingTheory.AdicCompletion.Basic` and its
  commutative ring structure from `Mathlib.RingTheory.AdicCompletion.Algebra`.
  The definition is compatible sequences in `A ⧸ (m^n • ⊤)`, which for the module
  A over itself is `A/m^n`. Mathlib includes the n=0 coordinate; that quotient is
  the zero module and the coordinate is unique, so this is exactly the node's
  inverse limit over n≥1.
- The only conclusion is
  `IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)`, asserting the same
  nonzero-one and no-zero-divisors properties for that ring. No normality,
  injectivity assertion, or extra conclusion has been appended.

Statement dependency declarations used:

- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`.
- `def-weil-pbc-henselian-terminology`:
  `WeilConjectures.Mathlib.RingTheory.Henselian`, publicly exporting
  `HenselianLocalRing` from the module `Mathlib.RingTheory.Henselian`.
  The recorded `IsStrictlyHenselianLocalRing`
  declaration and its docstring were read, but strict henselianity is not assumed.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` and `isNoetherianRing_iff_ideal_fg`.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`; `Mathlib.RingTheory.AdicCompletion.Algebra` supplies its ring
  operations. The latter imports the former publicly.

All four statement modules are public imports. Available proof declarations are
imported privately: `isNagataRing_of_isQuasiExcellent`, `IsNagataRing`, `IsN2`,
`integralClosure`, `integralClosure.isFractionRing_of_finite_extension`,
`integralClosure.isIntegrallyClosedOfFiniteExtension`,
`HenselianLocalRing.finite_over_henselian_exists_algEquiv_pi`, `Algebra.FiniteType`,
`isExcellent_finiteType_localization`, `AdicCompletion.map_injective`,
`AdicCompletion.map_exact`, `AdicCompletion.map_surjective`,
`Ideal.isMaximal_of_isIntegral_of_isMaximal_comap'`, and
`AdicCompletion.completion_finite_extension`. Their modules are listed explicitly
in the delivered import block. The proof dependency
`lem-per-henselian-normal-completion-preparation` has no Lean record or Mathlib
match on the read base, so there is no module for it to import. It is not needed
to type this statement; its role is retained as step 4 of the proof docstring.
The remaining five proof steps are likewise reproduced with their node citations,
including finite normalization, its locality, excellence, the injection between
the distinct completions, and transfer of the domain property through that injection.

Edge cases checked before writing:

- A field has maximal ideal zero, and its completion is itself; the formulation
  permits this case and imposes no positive-dimension assumption.
- The zero ring is excluded exactly by `[IsDomain A]`; the conclusion also
  includes nontriviality rather than merely absence of zero divisors.
- A need not be normal or complete. In particular the proof passes through its
  normalization, whereas the theorem assumes neither integrally closedness nor
  completion surjectivity. Normal A is also allowed.
- There is no characteristic restriction and no finite residue-field condition.
- All ring universes are arbitrary: `u` is explicit and there are no test objects
  in an unrelated smaller universe.
- The n=0 inverse-limit coordinate adds no datum, as explained above. The proof's
  empty product case is excluded by nontriviality of the normalization, not by an
  extra theorem hypothesis.

Searches actually run through `msearch.py NX lem-per-henselian-excellent-completion-domain`:

- LeanFinder, query `The maximal ideal completion of an excellent henselian local
  integral domain is an integral domain`: 8 hits, concerning `PreTilt.isDomain`,
  henselian local rings, complete rings being henselian, and valuation/Dedekind
  completions. None states the excellent henselian domain result.
- Loogle, query `AdicCompletion, IsDomain`: 0 hits.
- LeanSearch, query `The completion of an excellent henselian local domain is a
  domain`: 8 hits, concerning Hensel lifting, valuation completion, and completeness.
  None states the result.
- Mathlib grep, query
  `excellent|Excellent|analyticallyIrreducible|completion.*[Dd]omain|[Dd]omain.*[Cc]ompletion`
  in `RingTheory`: 3 hits in Laurent series and Dedekind adic valuations, no match.
- Direct `rg` of the same concept in `lean/WeilConjectures` and `lean/Sheaf`
  found excellence definitions and specialized completion modules; a targeted
  `isDomain.*([Cc]ompletion|[Hh]enselian)|([Cc]ompletion|[Hh]enselian).*isDomain`
  search found no declaration stating this theorem. The upstream `Excellent.lean`
  was inspected; the recorded `IsExcellent` interface remains the one used here.
- `grep -rn lem-per-henselian-excellent-completion-domain lean/WeilConjectures`
  and `rg` of this id in `dag/lean_names_upstream.json` returned no attachment.
  Direct name search for `isDomain_of_henselian_excellent` over Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` had no hits.

Validation: the prescribed `scompile.py` compiled the delivered file both as
`Sheaf.Stage2.Sandbox0` and as
`Sheaf.RingTheory.HenselianExcellentCompletionDomain` on the server (1.3 s each),
without errors or warnings. No local or global build was run.

## Second reading by NX

This is the dispatcher's worker's second reading, not a claim of independent
review; the maintainer supplies the independent reading. I reopened the node's
statement and the delivered theorem signature. `A : Type u` with `CommRing`
matches the commutative ring; `HenselianLocalRing` supplies both henselianity and
locality; the maximal ideal is the canonical one belonging to that local ring;
`IsNoetherianRing` matches the stated Noetherian condition; `hA : IsExcellent A`
uses the exact recorded excellence definition; `IsDomain A` includes the stated
nonzero-one condition; and the conclusion is `IsDomain` of precisely the
maximal-ideal completion of A. I checked the inverse-limit indexing against
`AdicCompletion`'s definition and the coordinatewise ring structure in its Algebra
module. The additional n=0 coordinate is uniquely determined and changes nothing.
Every variable and universe in the signature is bound explicitly. The declaration
has no extra local notation or instance choices. Its proof is exactly `sorry`.
No mismatch or node fault was found, and no statement change was made. The
six-step docstring retains both completion ideals and their comparison, rather
than identifying them prematurely. There are no new nodes or dependency modules
to review.
