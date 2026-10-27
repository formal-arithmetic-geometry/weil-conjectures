## Worker report

The module `Sheaf.RingTheory.IntegralElementPrimeLocalCriterion` states
`isIntegral_iff_isIntegral_atPrime`, with its sole proof `by sorry`. It introduces
no definitions. Its docstring contains all six steps of the node's proof, including
the denominator annihilator argument inside the actual monogenic subalgebra.

Source checked: `literature/stacks-project/algebra.tex`, lines 7629–7663,
`lemma-integral-closure-stalks` (Stacks Tag 034K). The source explicitly concerns
an arbitrary ring map and one element, with the equivalence at every base prime.
There is no repair note for this item and no statement correction is needed.
Only the node's `lean` field changes.

Hypothesis and clause correspondence:

- The arbitrary commutative rings are `{R : Type u} {A : Type v}` with
  `[CommRing R] [CommRing A]`. Both universes are explicitly declared and
  independent. No domain or nonzero-ring class is required.
- The ring homomorphism is encoded by `[Algebra R A]`, whose `algebraMap R A`
  is an arbitrary unital map between commutative rings. Every such ring map
  gives this structure via `RingHom.toAlgebra`; neither injectivity nor finiteness
  is part of this binder.
- The given element is `(a : A)`. Its global integrality is `IsIntegral R a`.
  This is precisely existence of a monic polynomial evaluated at `a`, using
  the recorded dependency's `IsIntegral` definition.
- “For every prime ideal of R” is `∀ (p : Ideal R) [p.IsPrime]`. Mathlib's
  `Ideal.IsPrime` includes properness and the product membership condition.
- The multiplicative set `R ∖ p` is `p.primeCompl`. The base localization
  is `Localization.AtPrime p`, definitionally `Localization p.primeCompl`.
- The localization of A with denominators acting through R → A is
  `Localization (Algebra.algebraMapSubmonoid A p.primeCompl)`. Here
  `Algebra.algebraMapSubmonoid` is the image submonoid under `algebraMap R A`.
  This is the standard ring model for the module localization in the dependency,
  not a localization at a prime of A or a residue-field tensor product.
- The image a/1 is
  `algebraMap A (Localization (Algebra.algebraMapSubmonoid A p.primeCompl)) a`.
  The inferred algebra structure from `Localization.AtPrime p` on this ring
  is Mathlib's canonical `IsLocalization.localizationAlgebra`, defined using
  `IsLocalization.map` of the original ring map. Thus the right-hand
  `IsIntegral (Localization.AtPrime p) ...` uses the intended localized map.
- The `↔` gives exactly both implications and retains the same element at
  every prime. No extra hypothesis or conclusion is present.

Dependency declarations read and used:

- `def-weil-pbc-module-localization`: public import
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, declaration `LocalizedModule`,
  with `LocalizedModule.mk`, `mk_eq`, and `mkLinearMap` read in that source.
  The ring model above uses the same fraction construction. Mathlib's
  `isLocalizedModule_iff_isLocalization` and its instance in
  `Mathlib.Algebra.Module.LocalizedModule.IsLocalization` explicitly identify
  the algebra localization at the image submonoid with localization of the
  original R-module at the base submonoid. No new localization is defined.
- `def-weil-pbc-integral-closure`: public import
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, recorded declarations
  `integralClosure`, `IsIntegral`, `IsIntegrallyClosedIn`. The signature uses
  `IsIntegral`; its definition and docstring were read in
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`. The other recorded
  declarations were read in their source files as well.
- `Mathlib.RingTheory.Localization.AtPrime.Basic` publicly supplies
  `Localization.AtPrime`; its definition and the canonical localized-algebra
  instance in `Mathlib.RingTheory.Localization.Basic` were read.
- Proof dependency `lem-sc-finite-generated-integral-subring` is
  `Algebra.finite_adjoin_of_finite_of_isIntegral` in
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic`, already publicly
  imported through the integrality dependency.
- Proof dependency `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`
  uses `PrimeSpectrum.iSup_basicOpen_eq_top_iff`,
  `Ideal.span_singleton_eq_top`, and `PrimeSpectrum.compactSpace`; its
  `Mathlib.RingTheory.Spectrum.Prime.Topology` module is a plain proof import.
- Proof dependency `lem-weil-pbc-module-finite-of-localization-span` is
  `Module.Finite.of_localizationSpan_finite` from the plain proof import
  `Mathlib.RingTheory.Localization.Finiteness`.
- Proof dependency `lem-weil-pbc-finite-algebra-is-integral` is
  `Algebra.IsIntegral.of_finite`, already in the integrality import.
  All proof-dependency signatures were read. No project proof import is missing.

Edge cases checked mathematically before writing:

- If R is the zero ring, a unital map forces A to be the zero ring. There are
  no primes, so the right side is vacuous and the left side holds (polynomial X).
  The signature has no `Nontrivial` binder.
- If A is the zero ring with R nonzero, all localized images are zero and
  both sides hold. The algebra localizations are permitted to be zero rings.
- For the noninjective map Z → Z/6, every element is integral globally and
  locally. No injectivity is accidentally imposed by the image submonoid.
- Zero divisors in R are allowed: e.g. R = Z/6, and localization may kill
  elements. The proof docstring retains the annihilator multiplier u rather
  than cancelling a denominator in the original ring.
- Over a field, localization at its zero prime recovers the original question;
  the theorem does not assert all algebra elements are integral.
- For Z → Q and a = 1/2 the prime (2) detects nonintegrality; localizing the
  algebra is distinct from requiring its base map to be integral everywhere.
- A local target ring may be zero, so a monic relation can have degree zero.
  Replacing it by a monic degree-one relation X in that zero ring justifies
  the positive-degree choice in the node's proof, without an extra hypothesis.

Searches (2026-10-24 UTC; launcher results are in `searches.jsonl`):

- `msearch.py ... leanfinder "An algebra element is integral over a ring if and
  only if its image is integral after localization at every prime ideal of the
  base ring"`: eight hits, including `RingHom.isIntegral_ofLocalizationSpan`,
  `isIntegral_localization`, and the integral-extension localization instance.
  None states the two-way prime-local criterion for an individual element.
- `msearch.py ... loogle "IsIntegral, Localization.AtPrime"`: zero hits.
- `msearch.py ... leansearch "Integrality of a single element of an arbitrary
  commutative algebra can be checked after localization at every base prime
  ideal"`: eight hits, including localization preservation, integrally closed
  domain criteria, and `RingHom.isIntegral_ofLocalizationSpan`; no exact match.
- `msearch.py ... grep
  "isIntegral.*(local|Local|prime|Prime)|(local|Local|prime|Prime).*isIntegral"
  RingTheory`: 25 hits. These concern preservation of whole-map integrality,
  integrally closed rings, and domain/fraction-field facts. Read
  `RingHom.isIntegral_ofLocalizationSpan`: it assumes integrality of whole
  localized maps on a unit-ideal cover, so it is not this statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for integrality/prime and
  localization patterns found only unrelated integral-closure, normality,
  inertia, or coefficient statements, not this criterion.
- `grep -rn "lem-sfb-integral-element-prime-local-criterion"
  lean/WeilConjectures`: no hit. `rg` for
  `isIntegral_iff_isIntegral_atPrime` in Mathlib, both project roots, and
  `dag/lean_names_upstream.json`: no hit; the new name is unused.

No STATEMENT-DISPUTED flag, missing notion, dependency repair, or new node.

## Second reading by Q106

A second pass by this worker reopened the node and the finished Lean signature.
No separate agent was started, as the dispatcher brief forbids this; the
maintainer's independent review remains the independent reading.
The two CommRing binders, arbitrary Algebra structure and element binder match
all initial data. The iff compares the same `a` with its image in the localization
at the image of each base-prime complement; the inferred coefficient algebra
is the canonical localization map, not an arbitrary action. The `p.IsPrime`
binder supplies exactly the proper prime ideals. Independent universes, zero
rings, noninjective maps and zero divisors are retained. No mismatch was found,
so this reading made no statement changes. The only theorem is the item and
its proof is entirely `sorry`; no helper theorem or definition was introduced.

Validation: the prescribed `scompile.py Q106
lem-sfb-integral-element-prime-local-criterion` compiled both its sandbox probe
and the actual library module successfully, exit code 0, with no diagnostics.
The actual library-module check took 6.1 seconds. Every Lean line is at most
100 characters, and every variable and universe is explicitly bound.
