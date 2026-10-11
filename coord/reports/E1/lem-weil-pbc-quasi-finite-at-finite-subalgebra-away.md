## Worker report

The module `Sheaf.RingTheory.QuasiFiniteAtFiniteSubalgebraAway` states
`Algebra.exists_finite_subalgebra_away_of_isQuasiFiniteAtPrime`, with its sole proof `sorry`.
The node is unchanged except for its `lean` record. No new notions, dependency modules,
or statement corrections are required.

Hypothesis and clause correspondence:

- The arbitrary commutative rings are `(R : Type u) (S : Type v) [CommRing R]
  [CommRing S]`, with independently bound universes. The map φ is the arbitrary
  `[Algebra R S]`, whose `algebraMap R S` is φ; every unital map between commutative
  rings determines such an algebra structure, so no injectivity is imposed.
- Finite generation as an R-algebra is `[Algebra.FiniteType R S]`.
- The prime ideal q is `(q : PrimeSpectrum S)`, with ideal `q.asIdeal`; bundling supplies
  precisely primality, without maximality or a domain assumption on S.
- Quasi-finiteness at that prime is `(hq : Algebra.IsQuasiFiniteAtPrime R S q)`, exactly
  the dependency's isolated-fibre-point definition, not Mathlib's localization predicate.
- The subalgebra is `∃ S' : Subalgebra R S`; its inclusion is `S'.val.toRingHom`.
- Finitely generated R-module is `Module.Finite R S'`, the recorded definition.
- An element lying in S' is `∃ g : S'`; being outside q is `g.1 ∉ q.asIdeal`.
- The stipulated canonical map on fractions is `Localization.awayMap S'.val.toRingHom g`.
  Its source is `Localization.Away g`, its target is `Localization.Away (S'.val g)`;
  its definition is `IsLocalization.Away.map`, sending y/g^n to y/g^n.
  `Function.Bijective` of this ring homomorphism says exactly that it is an isomorphism,
  rather than merely that some unrelated isomorphism exists.

Dependency declarations read and used:

- `Sheaf.RingTheory.QuasiFiniteAtPrime`, `Algebra.IsQuasiFiniteAtPrime`: full definition
  and docstring read; it takes a finite-type algebra and a `PrimeSpectrum S` point and
  asserts openness of the singleton corresponding fibre prime.
- `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`: full class signature and docstring
  read; its field is finite generation of the top submodule. Available through the
  finite-type dependency import.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule.Away`: full abbreviation
  and docstring read. The node explicitly allows its ring specialization for M = R;
  here the ring localization `Localization.Away` and its canonical `Localization.awayMap`
  from `Mathlib.RingTheory.Localization.Away.Basic` supply the ring objects and ring map.
  The module-localization import is unnecessary: this statement is about ring localizations.

Source inspection: the local Stacks text is absent on this machine. Read the primary online
pages https://stacks.math.columbia.edu/tag/00Q9,
https://stacks.math.columbia.edu/tag/00QA, and
https://stacks.math.columbia.edu/tag/00QB instead. The pointwise 00Q9 theorem and the
finite-subalgebra construction in the proof of 00QA give exactly the stated result;
00QB (3) repeats that construction. No global quasi-finiteness hypothesis was imported.
The declaration docstring carries all five DAG proof steps, including the injectivity
and surjectivity details omitted by 00QB.

Edge cases checked before writing: no Noetherian, domain, reduced, or injective-base-map
assumptions are needed. S = 0 has no prime-spectrum point, so the theorem has no such
instance; R = 0 forces S = 0 and is likewise covered. If S is already module-finite,
S' = S and g = 1 are legitimate witnesses. The condition g outside a prime automatically
rules out g = 0 and nilpotent g. The numerator construction works with no algebra
 generators as well as with nonzero finite lists. R and S may have different universe
levels. No statement dispute or node fault was found.

Searches performed (2026-10-11):

- `msearch.py ... leansearch "finite subalgebra localization at a quasi-finite prime"`:
  service unavailable (Internal Server Error); no verdict assigned to that unavailable search.
- `msearch.py ... leanfinder "finite type algebra quasi-finite at a prime admits a finite
  subalgebra with isomorphic localization away from an element outside the prime"`:
  eight hits including `Algebra.QuasiFiniteAt`, quasi-finiteness/localization stability,
  and finite-type results; none has this exact hypothesis and conclusion.
- `msearch.py ... loogle "Algebra.QuasiFiniteAt, Localization.awayMap"`: zero hits.
- `msearch.py ... grep "exists_fg_and_exists_notMem_and_awayMap_bijective" RingTheory`:
  six hits; read Mathlib's ZariskiMainTheorem lines 655–714. The lemma at line 703 gives
  the right conclusion but assumes `WeaklyQuasiFiniteAt`; it does not directly state the
  node's hypothesis. The integral-closure lemma at line 660 is also not this statement.
- `rg` in the source library and `lean/Sheaf` for `awayMap_bijective`,
  `IsQuasiFiniteAtPrime`, `finite_subalgebra`: the project's integral-closure theorem
  `Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime` concerns the entire integral
  closure, without its module finiteness; `Algebra.FiniteType.exists_finite_subalgebra_away`
  instead assumes a domain base and gives a Noether-normalization statement. Neither
  is an exact match. Read both signatures and docstrings.
- `grep -rn` for this node id in `WeilConjectures`: no hits.
- Name checked against the same source and project searches: the new full declaration
  name does not occur. No private definition of quasi-finiteness or localization is added.

Validation: server single-file compilation and `deliver2.py --no-push` are run before READY.
The independent second reading is reserved for the next worker, as instructed.

## Second reading by E1

I independently read the node statement, its Stacks source place (Tags 00Q9, 00QA,
and 00QB), the dependency declaration `Algebra.IsQuasiFiniteAtPrime`, and the Lean
signature. The correspondence is exact:

- The ring map is rendered by `(R : Type u) (S : Type v) [CommRing R] [CommRing S]
  [Algebra R S]`; the finite-type hypothesis is `[Algebra.FiniteType R S]`.
- The chosen prime ideal is `q : PrimeSpectrum S`, with ideal `q.asIdeal`.
- Pointwise quasi-finiteness is exactly `hq : IsQuasiFiniteAtPrime R S q`, the
  recorded isolated fibre-point predicate (and it uses the finite-type instance).
- The witness subalgebra is `∃ S' : Subalgebra R S`; module finiteness is
  `Module.Finite R S'`.
- The element witness is `∃ g : S'` with `g.1 ∉ q.asIdeal`.
- The final localization clause is precisely
  `Function.Bijective (Localization.awayMap S'.val.toRingHom g)`, the canonical
  map induced by the inclusion, matching `S'_g → S_g`, `y/g^n ↦ y/g^n`.

There are no omitted hypotheses, extra finiteness or Noetherian assumptions, map
injectivity assumptions, or altered quantifier order. The independent universes
`u` and `v` permit all cases covered by the node. The empty spectrum (including a
zero target ring), zero base ring, nilpotent/zero candidate `g`, and a module-finite
algebra (take the whole algebra and `g = 1`) are all covered by the quantified
statement; no nontriviality or nonempty-prime assumption was added.

I searched Mathlib, the slopmaster2 source, and the project with `rg` for the full
statement name and for `awayMap_bijective`, `finite_subalgebra`, and
`IsQuasiFiniteAtPrime`. Mathlib has the related
`Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`, but its
hypothesis is Mathlib's localization predicate and requires a translation theorem;
it is not an exact declaration of this node. The source and project contain no
exact existing declaration. No mismatch was found, so no Lean or node repair was
needed. The module compiles cleanly with `scompile.py`; its only proof is the
permitted `sorry` and its docstring records all source proof steps.
