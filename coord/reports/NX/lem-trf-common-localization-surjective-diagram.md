## Worker report

The module `Sheaf.RingTheory.CommonLocalizationSurjectiveDiagram` states
`Localization.exists_commonLocalization_surjective_diagram`, with one `sorry`
as its entire proof. It defines no new notions. The node is unchanged except
for its `lean` record. No statement correction or dependency repair is needed.

The source read was `literature/stacks-project/algebra.tex`, Proposition
`proposition-universal-property-localization` (Tag 00CP, including its proof),
Definition `definition-local-ring` and the following prime-localization
paragraph (07BI), Lemma `lemma-characterize-local-ring` (00E9), and Lemma
`lemma-characterize-local-ring-map` (07BJ). The node's additional diagram
argument is written out in the theorem docstring in all six steps.

Hypotheses and conclusion, clause by clause:

- `D`, `P`, `Q`, and `A` have separate explicit universe variables and
  `[CommRing ...]` binders. The three `[IsLocalRing ...]` binders assert exactly
  one maximal ideal for each of `P`, `Q`, and `A`; Mathlib's class includes
  nontriviality, as the source's definition requires. No local-ring or
  nontriviality hypothesis is imposed on `D`.
- `(u : P →+* A)` and `(v : Q →+* A)` are the two quotient maps.
  `[IsLocalHom u]`, `[IsLocalHom v]` encode locality. Mathlib's
  `IsLocalRing.local_hom_TFAE` identifies this with carrying the source maximal
  ideal into the target maximal ideal, exactly as Tag 07BJ and the node say.
  `hu` and `hv` are their `Function.Surjective` hypotheses.
- `(f : D →+* P)` and `(g : D →+* Q)` are the given maps, and
  `hcomm : u.comp f = v.comp g` is their compatibility. The node's defined
  abbreviation `h` is written out as `u.comp f` everywhere. It is not supplied
  as an additional, unconstrained ring map.
- `hf : ∀ p : P, ∃ a t : D, IsUnit (f t) ∧ p * f t = f a` and the analogous
  `hg` with `q`, `c`, `z`, and `g` are verbatim the unit-denominator
  hypotheses. Neither `f` nor `g` is assumed surjective.
- `∃ n : PrimeSpectrum D` supplies the prime ideal and its proof of primality
  together. Its underlying ideal is `n.asIdeal`. The first equality identifies
  it with `(IsLocalRing.maximalIdeal A).comap (u.comp f)`, so this is the
  specified ideal, not an arbitrary prime. The next two equalities identify
  the same ideal with the maximal-ideal inverse images under `f` and `g`.
- `Localization.AtPrime n.asIdeal` is precisely `D_n`. Its canonical map is
  `algebraMap D (Localization.AtPrime n.asIdeal)`. The existential ring maps
  `α`, `β`, `γ` have this exact domain and codomains `P`, `Q`, `A`.
- The three `.comp (algebraMap ...)` equalities state `αι=f`, `βι=g`, and
  `γι=h`.
- The three `Function.Surjective` conjuncts and three `IsLocalHom` conjuncts
  assert surjectivity and locality of every extension. Again, the latter
  means the maximal-ideal condition by Tag 07BJ.
- `u.comp α = γ` and `v.comp β = γ` give the complete commuting diagram.
- Each of the three universal clauses over `α'`, `β'`, or `γ'` says that
  every ring map with the indicated restriction equals the supplied
  extension. Uniqueness is therefore among all ring maps extending the given
  map, rather than only among maps satisfying the extra conclusions.
- Each fraction formula quantifies over every `d : D` and every
  `t : n.asIdeal.primeCompl`. This subtype is exactly the elements of `D`
  outside the prime. `IsLocalization.mk' (Localization.AtPrime n.asIdeal) d t`
  is `d/t`. Their images are respectively `f d * Ring.inverse (f t)`,
  `g d * Ring.inverse (g t)`, and `(u.comp f) d * Ring.inverse ((u.comp f) t)`.
  `Ring.inverse` returns the actual inverse on units. These denominators are
  units by the established common-prime equalities and the local-ring unit
  criterion; they need no extra unit hypotheses.
- There are no Noetherian, regularity, completeness, domain, characteristic,
  finiteness, or equality-of-universes assumptions.

Dependencies read and used:

- `def-weil-pbc-localization-at-prime` records
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
  Its definition is `Localization P.primeCompl`; its local-ring instance is
  `Localization.AtPrime.isLocalRing`, and its maximal-ideal description is
  `Localization.AtPrime.map_eq_maximalIdeal`. The recorded dependency is
  used directly by public import, with its canonical `algebraMap`.
- The proof dependency `lem-weil-pbc-local-ring-unit-criterion` matches
  `IsLocalRing.notMem_maximalIdeal` in
  `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`. Its full signature was
  read; this module is publicly imported by the prime-localization module.
- The proof dependency `lem-weil-pbc-ring-localization-universal-property`
  matches `IsLocalization.lift` and `IsLocalization.ringHom_ext`, with
  `IsLocalization.lift_mk'`, `lift_eq`, and `lift_comp` in
  `Mathlib.RingTheory.Localization.Defs`. The signatures and docstrings were
  read; these are exposed transitively by the prime-localization import.
  No separate proof-only imports are needed because both proof dependencies
  are already in the statement imports' public closure.
- `Mathlib.RingTheory.LocalRing.RingHom.Basic` supplies the locality interface
  and `local_hom_TFAE`; `Mathlib.RingTheory.Spectrum.Prime.Defs` supplies the
  existing bundled prime ideal `PrimeSpectrum`. These are representations of
  notions already in the statement, with no new definition node required.

Edge cases checked mathematically before writing: the zero ring is excluded
for `P`, `Q`, and `A` by their having exactly one maximal ideal, as in
`IsLocalRing`; a zero `D` cannot admit the assumed unital map to nontrivial
`P`, so no valid instance is lost. Fields are included, with zero maximal
ideal. The source `D` need not be a domain or local; zero divisors and
noninjective localization maps are allowed. Denominators are all elements
outside the prime, including `1`. Zero numerators and arbitrary ring
characteristics are covered. The fraction hypotheses permit maps that are
not surjective before localization. Independent universes allow all four
rings to have different sizes. No noncanonical map or choice is introduced.

Searches for an existing full statement (2026-10-24):

- `msearch.py ... leanfinder "Compatible surjective local maps from a common
  prime localization to local rings with a common quotient and unit
  denominator representations"`: eight results, headed by
  `RingHom.surjective_localRingHom_iff`, followed by individual localization
  surjectivity results. None states the complete compatible diagram.
- `msearch.py ... loogle "IsLocalization, Function.Surjective, IsLocalHom"`:
  zero results.
- `msearch.py ... leansearch "Compatible surjective local ring maps from a
  common prime localization with fraction generating hypotheses"`: eight
  results, again individual localization/surjectivity facts, not this node.
- `msearch.py ... grep
  "lift_surjective_iff|localRingHom_unique|comap_maximalIdeal"
  RingTheory/Localization`: seven hits. Read `IsLocalization.lift_surjective_iff`
  and `Localization.localRingHom_unique` in full. The former treats one lift;
  the latter maps between two prime localizations. Neither states this result.
- `rg -n` for `common_localization|commonLocalization` and the exact node id in
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no matching declaration. A broader search for common localization and
  localization diagrams found only unrelated uses in other contexts.
- `grep -rn` for the node id in `lean/WeilConjectures`: no match. A final exact
  declaration-name search in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  the upstream-name index found no collision.

Validation: `scompile.py NX lem-trf-common-localization-surjective-diagram`
compiled both its sandbox probe and its library module successfully, with no
errors or warnings (1.1 seconds each). All variables and universes are
explicitly bound; the module starts with `module` and uses public imports and
`@[expose] public section`. The theorem proof is only `sorry`.

## Second reading by NX

A second in-thread reading compared the node and final module clause by
clause. The dispatcher expressly forbids starting other agents; this is a
worker self-check, with the maintainer's independent review still to follow.
The check verified the four ring hypotheses, locality and surjectivity of
both quotient maps, equality of composites, both precise denominator
hypotheses, all three prime inverse-image equalities, all three extension
identities, three surjectivity and three locality conclusions, both diagram
equalities, unrestricted uniqueness for each extension, and all three
fraction formulas. Bundling the prime as `PrimeSpectrum D` neither changes
which ideal is localized nor adds a hypothesis, because the first equality
fixes its ideal to the specified inverse image. The source's meaning of
local map agrees with `IsLocalHom` by `local_hom_TFAE`, and `Ring.inverse` is
the unit inverse on every permitted denominator. No mismatch or statement
fault was found, and no declaration changed during this rereading.
