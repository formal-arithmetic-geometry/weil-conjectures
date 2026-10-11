## Worker report

The module `lean/Sheaf/RingTheory/InjectivePiLocalizationAssociatedPrimes.lean` states
`Module.injective_pi_localization_associatedPrimes` with a single `sorry` proof.
No definitions are introduced, no statement is corrected, and no dependency record is changed.

Hypothesis and clause correspondence:

- The commutative Noetherian ring is `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
  Commutativity is part of the dependency node and Stacks' ring convention.
- An arbitrary R-module is `(M : Type v) [AddCommGroup M] [Module R M]`.
  There is no finite-generation, nontriviality, or Noetherian-module hypothesis.
- Associated primes are `associatedPrimes R M`. Mathlib defines these using radical
  annihilators; the full signature of `isAssociatedPrime_iff` says, under the existing
  `[IsNoetherianRing R]`, `IsAssociatedPrime p M ↔ p.IsPrime ∧ ∃ x : M,
  p = Submodule.colon ⊥ {x}`. Membership in that colon is exactly `a • x = 0`.
  Thus this is precisely the node's set, including for arbitrary modules.
- `p : associatedPrimes R M` ranges over that set without choosing a finite list.
  Mathlib supplies `p.1.IsPrime` from membership. `p.1.primeCompl` is R minus p.
- `LocalizedModule.AtPrime p.1 M` unfolds to `LocalizedModule p.1.primeCompl M`,
  the dependency's module localization. The displayed linear-map type in the signature
  explicitly identifies each target with that prime localization.
- The canonical R-linear map is `LinearMap.pi (fun p =>
  LocalizedModule.mkLinearMap p.1.primeCompl M)`. Its p-coordinate sends m to m/1.
  `Function.Injective` is the first conclusion.
- The second conjunct states the node's equivalent formulation verbatim:
  `∀ m : M, (∀ p : associatedPrimes R M, ∃ s : R,
  s ∉ p.1 ∧ s • m = 0) → m = 0`. Each p has its own denominator.
- The dependent function type is the full product of the localized modules. When the
  index subtype is empty it is a subsingleton module, hence the zero module, as required.
  Stating both equivalent conclusions does not strengthen the node.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, imported transitively through AssociatedPrime.Basic.
- `def-weil-pbc-module-localization`: `Mathlib.Algebra.Module.LocalizedModule.Basic`,
  `LocalizedModule` and `LocalizedModule.mkLinearMap`, imported through AtPrime.
- `def-weil-pbc-localization-at-prime`: its Mathlib record identifies localization
  at `p.primeCompl`. We use `LocalizedModule.AtPrime` from
  `Mathlib.Algebra.Module.LocalizedModule.AtPrime`, whose complete abbreviation is
  `LocalizedModule P.primeCompl M`, exactly the module specialization specified in
  the item's statement. The dependency's ring localization `Localization.AtPrime`
  is not needed to form the module product; no separate ring carrier is chosen.
- The associated-prime definition, its Noetherian equivalence, and the prime instance
  are in `Mathlib.RingTheory.Ideal.AssociatedPrime.Basic`.
- `LinearMap.pi` is in `Mathlib.LinearAlgebra.Pi`; its signature and docstring were read.

Source checked: the local `literature/stacks-project/algebra.tex` is absent on this
machine, so I opened https://stacks.math.columbia.edu/tag/0311 directly. Lemma
10.63.19 has exactly arbitrary M, Noetherian R, and the injective canonical product
map. The declaration docstring gives all three proof steps of the node, with the
zero-divisor and submodule node ids and the denominator contradiction.

Edge cases checked before writing: zero/subsingleton M gives an empty associated-prime
set and a subsingleton source and target; the zero ring is allowed, as all its unital
modules are zero; infinite associated-prime sets are allowed by the dependent product;
M need not be finite or Noetherian; independent universes u and v admit arbitrary
modules and localizations live in `Type (max u v)`; empty Ass forces M to be zero by
exactly the nonzero cyclic-submodule argument in the docstring. No characteristic
restriction is present. No statement dispute or node fault was found.

Searches for existing declarations (2026-10-11):

- `msearch.py ... leansearch "An element of a module over a Noetherian ring is zero if
  it vanishes at all associated primes"`: unavailable, Internal Server Error; no
  mathematical verdict drawn from the unavailable service.
- `msearch.py ... leanfinder "module over a Noetherian ring injects into product of
  localizations at associated primes"`: eight hits, including
  `injective_of_isLocalized_maximal`, `injective_of_localized_maximal`,
  `isAssociatedPrime_iff_exists_injective_linearMap`, `associatedPrimes.finite`,
  `exists_le_isAssociatedPrime_of_isNoetherianRing`, and
  `IsAssociatedPrime.map_of_injective`. These concern all maximal ideals,
  injective maps from R/p, or proof ingredients; none is the requested theorem.
- `msearch.py ... loogle "Module.associatedPrimes, LocalizedModule,
  Function.Injective"`: zero hits, unknown identifier `Module.associatedPrimes`.
  The source inspection resolves this as the global `associatedPrimes`.
- `msearch.py ... grep 'associatedPrimes.*(injective|localiz)|injective.*associatedPrimes'`:
  eight hits, all on localization transport of associated primes or associated-prime
  inclusions under injective maps, none on injectivity of the product map.
- `rg` of associatedPrimes, IsAssociatedPrime, toPiLocalization, and mkLinearMap in
  Mathlib's AssociatedPrime and LocalizedModule directories: definitions and transport
  results only. The full associated-prime definition and Noetherian equivalence were read.
- `rg` of `associatedPrimes|lem-weil-pbc-module-injects-localizations-associated-primes`
  in source WeilConjectures and project lean/Sheaf: source regular-ring arguments and
  project associated-prime lemmas; the AnalyticallyUnramifiedPrincipalCriterion docstring
  cites this item but does not state it. No duplicate theorem was found.
- `rg` of `injective_pi_localization_associatedPrimes` in dag/lean_names_upstream.json,
  Mathlib, WeilConjectures, and lean/Sheaf: no hit, so the new full name is unused.

Validation: server single-file compilation passed in 1.3 seconds with no errors or
warnings. `deliver2.py --no-push` printed OK: compilation and preflight passed except
for the independent second reading, which the second reader writes. Nothing was pushed.

## Second reading by H1

I reread the node statement, its Stacks source (Algebra, Tag 0311 / Lemma
10.63.19), and the module independently.

- The ring object and hypotheses are rendered by `(R : Type u) [CommRing R]
  [IsNoetherianRing R]`. This is the commutative Noetherian ring assumed by the
  source; no finiteness, locality, domain, characteristic, or universe
  restriction is added.
- The module object and hypotheses are rendered by `(M : Type v)
  [AddCommGroup M] [Module R M]`. This permits arbitrary modules, including
  zero and non-finitely-generated modules, with independent universes.
- The associated-prime index set is Mathlib's `associatedPrimes R M`; under the
  Noetherian hypothesis `isAssociatedPrime_iff` gives the source's annihilator
  description. Its elements are used as `p : associatedPrimes R M`, with the
  prime ideal `p.1` and complement `p.1.primeCompl`.
- The localization object is rendered at each index by
  `LocalizedModule.AtPrime p.1 M`, i.e. localization of `M` at the complement
  of `p.1`, using the recorded module-localization and localization-at-prime
  notions.
- The canonical map is exactly the source map `m ↦ (m/1)_p`, rendered as
  `LinearMap.pi (fun p => LocalizedModule.mkLinearMap p.1.primeCompl M)`.
  The first conclusion is `Function.Injective` of this R-linear map.
- The equivalent elementwise clause is rendered with the same quantifier order:
  `∀ m : M, (∀ p : associatedPrimes R M, ∃ s : R, s ∉ p.1 ∧ s • m = 0) →
  m = 0`. Each associated prime has its own denominator, as in the source.

The conjunction states exactly the injectivity clause and its stated equivalent;
it introduces no stronger hypothesis or conclusion. The empty associated-prime
index gives the unique (zero) dependent product, and the theorem still forces a
zero module by the elementwise clause. The zero module, zero ring, arbitrary
infinite index set, and arbitrary module universe are all covered. There is no
characteristic or `n = 0` parameter in the source statement.

I searched Mathlib's associated-prime and localized-module files, the project
`WeilConjectures/` and `lean/Sheaf/`, and the upstream declaration index. I also
checked LeanFinder, Loogle, and the recorded LeanSearch query. The hits are
proof ingredients or localization results for other index sets; none states the
product-over-associated-primes injection. Thus no existing declaration replaces
this theorem.

No mismatch was found and no source or Lean change was necessary. The module
compiled cleanly with `scompile.py`; its only proof hole is the required named
statement `sorry`, and all variables and universes are explicit.
