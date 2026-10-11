## Worker report

The module `Sheaf.RingTheory.QuasiFiniteAtPrimePrincipalLocalization` states
`Algebra.isQuasiFiniteAtPrime_iff_principalLocalization`, with its only proof `sorry`.
No definition is copied, no dependency module or new node is needed, and no node
statement is corrected. The declaration docstring gives all nine proof steps.

Hypothesis and clause correspondence:

- Commutative rings R and S: `(R : Type u) (S : Type v) [CommRing R] [CommRing S]`,
  with independent explicit universes. The ring map φ is `algebraMap R S`, determined
  by `[Algebra R S]`; every unital map of commutative rings yields this structure.
- Finite type of φ: `[Algebra.FiniteType R S]`, the dependency's recorded definition.
- Prime q: `(q : PrimeSpectrum S)`, bundling the ideal and primality.
- p = φ⁻¹(q): the explicit ideal `q.asIdeal.comap (algebraMap R S)`; no separate
  choice or extra hypothesis on p is needed.
- f outside p and g outside q: `(f : R)` with `hf : f ∉ q.asIdeal.comap
  (algebraMap R S)` and `(g : S)` with `hg : g ∉ q.asIdeal`.
- R_f and S_fg: `Localization.Away f` and
  `Localization.Away (algebraMap R S f * g)`. These are the canonical quotient
  localizations from the recorded dependency; their structure maps are `algebraMap`.
- The induced map: the ring map binder `φ'` and commuting equation `hφ'` say
  exactly that φ' extends φ along the two localization maps. This is a
  characterization of the uniquely specified map, not a restriction on φ:
  φ(f) is a unit in S_fg since it divides φ(f)g, so the universal property
  always supplies φ'. Uniqueness forces the fractions formula in the node,
  φ'(r/f^n) = φ(r)g^n/(φ(f)g)^n. No new map notion is introduced.
- “It is of finite type”: the conclusion supplies `∃ hft : @Algebra.FiniteType
  (Localization.Away f) (Localization.Away (algebraMap R S f * g)) _ _ φ'.toAlgebra`.
  This avoids assuming the parenthetical assertion. The explicit hft argument
  then supplies the finite-type witness required by the dependency's predicate.
- qS_fg, a prime ideal: the conclusion supplies `∃ hq' : (q.asIdeal.map
  (algebraMap S (Localization.Away (algebraMap R S f * g)))).IsPrime`.
  `Ideal.map` is the extended ideal; in a localization its elements are exactly
  the fractions with numerator in q, as in the node's second proof step.
- The equivalence: `IsQuasiFiniteAtPrime R S q ↔ @IsQuasiFiniteAtPrime ...
  φ'.toAlgebra hft ⟨q.asIdeal.map ..., hq'⟩`. Both sides use the SAME recorded
  isolated-fibre-point predicate. The algebra on the right is induced by φ'.
  Existential primality/finite-type witnesses do not weaken the statement,
  because they are propositions and proof irrelevance identifies their uses.

Dependencies read and used:

- `Mathlib.RingTheory.FiniteType`, `Algebra.FiniteType`, through the import
  `Sheaf.RingTheory.QuasiFiniteAtPrime`: finite generation of the top subalgebra.
- `Mathlib.GroupTheory.MonoidLocalization.Away`, `Localization.Away`, through
  `Mathlib.RingTheory.Localization.Away.Basic`: localization at powers of the element.
- `Sheaf.RingTheory.QuasiFiniteAtPrime`, `Algebra.IsQuasiFiniteAtPrime`: open singleton
  of the canonically corresponding point of the fibre spectrum. Its full
  definition and docstring were read; no use is made of Mathlib's different
  `Algebra.QuasiFiniteAt` notion.

Source checked: the local `literature/stacks-project/algebra.tex` is not present
on this machine, so the full statement and proof of Stacks Tag 077H were read at
https://stacks.math.columbia.edu/tag/077H. They agree with the node and its proof route.

Edge cases checked before writing: the zero target ring has no prime q, so there
is no unintended nonzero-ring assumption. f = 0 or g = 0 is excluded exactly by
hf/hg, not by added assumptions. f = 1 or g = 1 and arbitrary units give the
expected restrictions. Zero divisors are allowed: being outside the specified
prime suffices, with no domain, reducedness, injectivity or Noetherian assumption.
The extension of q is proper because φ(f)g avoids q. No field or characteristic
restriction is imposed. Independent ring universes cover rings of different sizes.

Searches made (all through the prescribed tools or read-only rg):

- msearch leansearch: “quasi finite at prime invariant under principal localization”:
  service unavailable (Internal Server Error), recorded by the wrapper.
- msearch leanfinder: “finite type ring map quasi-finite at a prime iff quasi-finite
  after principal localization of base and target”: eight hits, including
  `RingHom.QuasiFinite.propertyIsLocal`, `.holdsForLocalizationAway`,
  `Algebra.QuasiFinite.of_isLocalization`, and `Algebra.QuasiFiniteAt`; none states
  this equivalence for the recorded isolated-fibre-point predicate.
- msearch loogle: `IsLocalization.Away.awayToAwayLeft, Algebra.QuasiFiniteAt`:
  zero hits.
- msearch grep: `QuasiFiniteAt|quasiFiniteAt`, Mathlib/RingTheory/Localization:
  zero hits. Direct rg in Mathlib/RingTheory/QuasiFinite/Basic.lean and
  ZariskisMainTheorem.lean found the alternate local-algebra predicate, its
  localization tools, and the bridge `quasiFiniteAt_iff_isOpen_singleton_fiber`,
  but no existing declaration with this statement.
- rg `quasi.*[Ff]inite.*[Aa]way|quasi.*[Ff]inite.*local|IsQuasiFiniteAtPrime` in
  WeilConjectures and lean/Sheaf: related scheme results and other uses of the
  recorded predicate, but no principal-localization equivalence. The exact
  blueprint-id grep in WeilConjectures returned no match.
- rg `isQuasiFiniteAtPrime_iff_principalLocalization` in dag/lean_names_upstream.json,
  Mathlib, WeilConjectures and lean/Sheaf: no collision.
- Read the complete docstrings/signatures of `IsLocalization.Away.lift`,
  `.awayToAwayLeft` and `.awayToAwayRight`, which verify that the commuting-square
  characterization is the canonical fractions map. No private definition needed.

Validation: server single-file compilation and delivery preflight dry run are
performed with scompile.py and deliver2.py --no-push. No delivery is pushed;
the independent second reader supplies the second-reading section.

## Second reading by M1

The node introduces a finite-type commutative-ring map `R → S`, a prime `q` of
`S`, its contraction `q.asIdeal.comap (algebraMap R S)`, elements `f` and `g`
outside those primes, the principal localizations `Localization.Away f` and
`Localization.Away (algebraMap R S f * g)`, the induced localization map, its
finite-type property, and the extended prime. The Lean statement renders these
as `(R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
[Algebra.FiniteType R S]`, `q : PrimeSpectrum S`, `f` with `hf`, `g` with `hg`,
`φ' : Localization.Away f →+* Localization.Away (...)`, and `hφ'` asserting the
commuting square. The conclusion existentially supplies the finite-type
instance `hft`, the primality witness `hq'` for
`q.asIdeal.map (algebraMap S (Localization.Away (...)))`, and exactly the
equivalence between `IsQuasiFiniteAtPrime R S q` and the corresponding predicate
for `φ'` at that mapped prime. Every object, hypothesis, quantifier, and
conclusion clause agrees with the node; no repair was needed.

Edge cases were reread: an empty prime spectrum (including the zero target ring)
is vacuous; `f = 0` and `g = 0` are excluded only by `hf` and `hg`; units and
`f = 1` or `g = 1` are allowed; zero divisors, different ring universes, and all
characteristics remain allowed. No Noetherian, domain, injectivity, reducedness,
field, or characteristic assumption is present.

I repeated the Mathlib, source-project, and project searches recorded above,
including searches for `isQuasiFiniteAtPrime_iff_principalLocalization`,
`IsQuasiFiniteAtPrime`, and localization-away quasi-finiteness. Mathlib's
`Algebra.QuasiFiniteAt` is a different localization-at-a-prime notion, related
only by a theorem, so no existing declaration replaces this statement. The
recorded dependency declarations (`Algebra.FiniteType`, `Localization.Away`, and
`Algebra.IsQuasiFiniteAtPrime`) have the required meanings. The module compiled
with `scompile.py`; no Lean or node changes were necessary in this second reading.
