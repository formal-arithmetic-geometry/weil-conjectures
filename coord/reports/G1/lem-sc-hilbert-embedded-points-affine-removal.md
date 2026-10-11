## Worker report

The module `Sheaf.RingTheory.RemoveEmbeddedPrimes` states
`Module.exists_maximal_nowhereDense_support_quotient`, with proof `sorry`.
It adds no definitions and changes only the item's `lean` record.

Hypothesis and clause matching:

- The ring R is bound in universe u with `[CommRing R] [IsNoetherianRing R]`.
  The commutativity is part of the dependency's definition of a Noetherian ring.
- The finite R-module M is bound independently in universe v with
  `[AddCommGroup M] [Module R M] [Module.Finite R M]`.
- Localization at a prime and support use `Module.support R M`: its definition is
  nontriviality of `LocalizedModule p.asIdeal.primeCompl M`, exactly M_p ≠ 0.
- Associated primes use `associatedPrimes R M`. The source signature and docstring of
  `isAssociatedPrime_iff` were read: over a Noetherian ring this is equivalently a prime
  equal to `Submodule.colon ⊥ {x}`, the annihilator of an element. Mathlib's general
  definition involving a radical therefore does not alter the notion here.
- An embedded prime is rendered inline as membership in `associatedPrimes R M`
  together with failure of `Minimal (fun q => q ∈ associatedPrimes R M) p`.
- Existence of a maximal submodule is `∃ K : Submodule R M, Maximal (...) K`.
  The predicate is `IsNowhereDense {p : Module.support R M | p.val ∈ Module.support R L}`.
  This is the support of L inside the support of M, equipped with the induced Zariski
  topology. `Maximal` includes membership in the predicate as well as order maximality.
  No greatest-element or uniqueness conclusion is substituted for maximality.
- M' is precisely `M ⧸ K`, rather than an arbitrary module with an unspecified quotient.
- Equal support is `Module.support R (M ⧸ K) = Module.support R M`.
- No embedded associated primes is the condition that every associated prime of
  `M ⧸ K` is `Minimal` among its associated primes.
- The final universal f binder has exactly the condition that f lies in every embedded
  associated prime of M. `Submonoid.powers f` localizes at f. The canonical localized
  quotient map is `IsLocalizedModule.map ... K.mkQ`, with both localization maps supplied
  explicitly. Its `Function.Bijective` means this linear map is an isomorphism, and
  specifies the canonical map, rather than merely asserting some unrelated equivalence.
  It is also linear over R_f: division by f commutes with the localized R-linear map,
  and its inverse likewise commutes with the invertible action of f.

Dependency declarations read and used (all three dependencies are Mathlib leaves):

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs` (available through AssociatedPrime.Basic).
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs` (available through the imports).
- `def-weil-pbc-module-localization`: `LocalizedModule` and
  `LocalizedModule.mkLinearMap`, `Mathlib.Algebra.Module.LocalizedModule.Basic`
  (available through Support); the actual map API is `IsLocalizedModule.map`, not
  `LocalizedModule.map` as the dependency's explanatory prose suggests.

Also read and used `Module.support` in Mathlib.RingTheory.Support,
`associatedPrimes` and `isAssociatedPrime_iff` in
Mathlib.RingTheory.Ideal.AssociatedPrime.Basic, `Minimal`/`Maximal` in
Mathlib.Order.Defs.Unbundled, and `IsNowhereDense` in Mathlib.Topology.GDelta.Basic.
The topology is imported from Mathlib.RingTheory.Spectrum.Prime.Topology.

Edge cases checked before writing: zero module (empty support and associated-prime set,
K = 0); zero ring (all modules are zero, and the spectrum is empty); no embedded primes
(K = 0 and the condition on f is vacuous); f = 0 (localizations are zero and the map is
bijective); f = 1 when there are no embedded primes. No nontriviality, domain, nonempty
spectrum, positive dimension, or nonzero f hypothesis is introduced. Independent
universes u and v cover rings and modules in different universes.

Source: local `literature/stacks-project/algebra.tex` is absent on this machine, so read
https://stacks.math.columbia.edu/tag/02M6 directly. The statement and its three conclusions
agree with the node. The website currently numbers it Lemma 10.67.2, whereas the node
records an older lemma number 10.63.4; the stable tag and label identify the right lemma.
This is a source-number observation, not a mathematical statement fault.

Searches (the real remote-search results are logged in searches.jsonl):

- msearch.py leansearch: `finite module quotient remove embedded associated primes same support`:
  service unavailable, Internal Server Error.
- msearch.py leanfinder: `Noetherian finite module maximal submodule nowhere dense support quotient no embedded associated primes`:
  eight hits on associated-prime existence and support, none stating this theorem.
- msearch.py loogle: `associatedPrimes`: twelve hits providing associated-prime definitions
  and elementary properties, none removing embedded primes.
- msearch.py grep: `embedded|associatedPrimes|def support`, RingTheory:
  associated-prime and support files and Lasker primary decomposition; no same theorem.
  Read the Lasker file's relevant names as well: no embedded-prime-removal statement.
- rg of `embedded|associatedPrimes|Module.support` in WeilConjectures and lean/Sheaf:
  unrelated embedded schemes, support applications, and associated-prime applications;
  no module-removal theorem or extra definition of these notions.
- grep of `lem-sc-hilbert-embedded-points-affine-removal` in WeilConjectures: no hits.
- rg of the DAG for associated primes, support of modules, nowhere density and embedded
  primes found existing related lemmas and this node; all notions used here already have
  Mathlib definitions or are explicit combinations of those definitions.

No STATEMENT-DISPUTED issue, statement correction, new nodes, or dependency modules.
The declaration docstring carries all four DAG proof steps, with their dependency ids,
for the stage-3 worker. No proof beyond the requested `sorry` was written.

## Second reading by G1

Independent reading of the sandbox node and `RemoveEmbeddedPrimes.lean`, all three
statement-dependency nodes and their Mathlib declarations. I also fetched the actual
Stacks `algebra.tex` from https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex
and read `lemma-remove-embedded-primes` and the chapter's Conventions. Those conventions
explicitly allow the zero ring and require rings to be commutative with identity.
The source agrees with the node; there is no corrected statement to review.

Object, hypothesis and conclusion checklist (all verdicts: exact):

1. R is a Noetherian ring: `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
   Dependency `def-weil-pbc-noetherian-ring` records `IsNoetherianRing`, whose
   Noetherian/Defs.lean definition is `IsNoetherian R R`, equivalently finite generation
   of every ideal. Commutativity is required by the source conventions, not an extra
   hypothesis; no field, domain, characteristic or nontriviality instance is assumed.
2. M is a finite R-module: `(M : Type v) [AddCommGroup M] [Module R M]
   [Module.Finite R M]`. Dependency `def-weil-finitely-generated-module` records
   `Module.Finite`; Finiteness/Defs.lean:117-119 makes this finite generation of top,
   with `Submodule.FG` defined by a finite spanning set. It does not mean a finite set M.
3. At a prime p, M_p and Supp(M): `Module.support R M` in Support.lean:50-51
   is `{p | Nontrivial (LocalizedModule p.asIdeal.primeCompl M)}`. The spectrum contains
   precisely proper prime ideals. Nontriviality means the localized module is nonzero.
   The localization dependency records `LocalizedModule`; Basic.lean's fraction
   construction and `mkLinearMap` provide exactly that dependency's notion.
4. Associated primes are annihilators of elements: `associatedPrimes R M` and the
   corresponding expression for `M ⧸ K`. AssociatedPrime/Basic.lean:98-116 defines
   membership via `IsAssociatedPrime`, includes primality, and `isAssociatedPrime_iff`
   over this same Noetherian R removes the radical. `colon ⊥ {x}` consists of precisely
   the scalars annihilating x. This equivalence also applies to the quotient module.
5. Embedded means nonminimal among associated primes:
   `p ∈ associatedPrimes R M` with
   `¬ Minimal (fun q : Ideal R => q ∈ associatedPrimes R M) p`.
   Unbundled.lean:279 defines minimality with ideal inclusion; it neither uses maximal
   primes nor minimal primes of R. Ideal quantifiers are restricted to primes by membership.
6. There exists a maximal submodule with nowhere dense support in Supp(M):
   `∃ K : Submodule R M, Maximal (fun L : Submodule R M =>
   IsNowhereDense {p : Module.support R M | p.val ∈ Module.support R L}) K`.
   `Maximal` includes the predicate at K and order maximality under submodule inclusion.
   The support of L is contained in Supp(M), since localization preserves its injection
   into M, so the displayed subtype set represents its whole support. The imported
   `PrimeSpectrum.zariskiTopology` and the subtype topology give exactly nowhere density
   relative to Supp(M); GDelta/Basic.lean:200 defines empty interior of the closure.
7. M' is the quotient by that same K: `M ⧸ K` throughout the remaining conjunctions.
   Equal support: `Module.support R (M ⧸ K) = Module.support R M`.
   The reversed order of this equality has no mathematical effect.
8. M' has no embedded associated primes: every `p ∈ associatedPrimes R (M ⧸ K)`
   satisfies `Minimal (fun q : Ideal R => q ∈ associatedPrimes R (M ⧸ K)) p`.
   This is exactly the negation of the embedded-prime condition, including an empty set.
9. For every f contained in all embedded associated primes of the original M:
   the final `∀ f : R` and its two restricted prime binders impose exactly that condition.
   The same chosen K works for every such f; it is chosen before f, as in the source.
   `Function.Bijective (IsLocalizedModule.map (Submonoid.powers f)
   (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
   (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ K)) K.mkQ)`
   says the canonical localized quotient map is an isomorphism.
   I read Basic.lean:1227-1247: `map_mk'` sends m/s to `K.mkQ m`/s.
   It is R-linear, commutes with invertible denominators, and hence is R_f-linear;
   bijectivity therefore gives the required localized-module isomorphism, with no
   arbitrary unrelated map or omitted surjectivity/injectivity condition.

Edge cases: M = 0 has empty support and empty associated primes, and K = 0 satisfies
all conclusions; the zero ring is admitted by CommRing and forces its modules to be zero.
If there are no embedded primes, the condition on f is vacuous and K = 0 works, including
f = 1. For f = 0 both localized modules are zero, and their canonical map is bijective.
Nilpotent f is also covered. There is no excluded characteristic and independent u and v
allow any ring/module universe pair. No index-set or dimension/n binder occurs; empty
prime collections and dimension zero are admitted. There are no schemes in this affine
module statement; the empty spectrum case is included.

Independent searches used different phrasing from the worker:

- `msearch.py ... leanfinder "quotient of finitely generated module eliminating nonminimal
  associated primes unchanged support"`: eight hits, notably `Module.support_quotient`,
  associated-prime finiteness and minimal-prime inclusion. None states removal by a
  maximal submodule with nowhere dense support; `support_quotient` is instead a quotient
  by I times M and an intersection with V(I).
- `msearch.py ... loogle "IsNowhereDense"`: twelve hits defining nowhere density and its
  elementary properties, with no module-removal theorem.
- Independent rg of `remove.*(prime|support)|embedded.*prime|nowhere.?dense` in Mathlib's
  RingTheory, WeilConjectures and the project's lean/Sheaf found only unrelated topology,
  stratification and Cartier-divisor material; no duplicate theorem. Also searched the
  declaration name and node id in `dag/lean_names_upstream.json` and WeilConjectures:
  no matches. The worker's LeanSearch failure and other searches remain documented above.

No H3/H4 mismatch was found. No definition or dependency module was introduced or is
needed: existing Mathlib notions and their explicit predicates suffice. All imports serve
support, associated primes or the relevant topology. The header, namespace, source and
blueprint docstrings conform; the theorem docstring includes the four DAG proof steps
and their dependency ids. There is exactly one named theorem with proof `sorry`, no
hollow definition, and no proof was supplied. Universes and variables are explicitly
bound; the node's `lean.statement` is verbatim the theorem signature.

Changes: appended this independent second-reading record only; the correct module and
node signature were preserved. Validation: server single-file compile, followed by the
stage-2 dry-run preflight and delivery checks.
