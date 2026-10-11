## Worker report

The module `lean/Sheaf/RingTheory/IdempotentsDeterminedModuloRadical.lean` states
`IsIdempotentElem.eq_of_sub_mem_of_le_jacobson`, with `sorry` as its entire proof.
It adds no definition, dependency node, or statement correction.

Hypothesis and conclusion correspondence:

- A commutative ring R: `{R : Type u} [CommRing R]`, with the universe explicitly declared.
- An ideal J of R: `(J : Ideal R)`.
- J is contained in the Jacobson radical of R:
  `(hJ : J ≤ Ideal.jacobson (⊥ : Ideal R))`.
  Mathlib defines this as the infimum of maximal ideals containing the zero ideal,
  hence the intersection of all maximal ideals of R.
- Elements e and e': `{e e' : R}`.
- Both are idempotents: `(he : IsIdempotentElem e)` and
  `(he' : IsIdempotentElem e')`. Mathlib's predicate is exactly `e * e = e`,
  equivalent to the displayed square equations.
- Their difference is in J: `(hee' : e - e' ∈ J)`.
- They coincide: the conclusion `e = e'`.
- The final phrase about injectivity of the map on idempotents is the same conclusion:
  equality of quotient classes is equivalent to `e - e' ∈ J`; injectivity on
  the idempotent subtype is precisely equality under the two idempotence assumptions.
  It does not request a separate additional conclusion.

There are no `stmt_deps`. The existing Mathlib declarations used are:
`IsIdempotentElem`, defined in `Mathlib.Algebra.Group.Idempotent`, and
`Ideal.jacobson`, defined in `Mathlib.RingTheory.Jacobson.Ideal`.
Their source definitions and docstrings were read. The namespace/name was searched in
Mathlib, `dag/lean_names_upstream.json`, the source library, and `lean/Sheaf`; no collision.
The docstring carries both DAG proof steps: equality at maximal localizations, then the
annihilator argument detecting equality globally. No other proof nodes are needed.

Edge cases checked before writing: the zero ring is permitted (no `Nontrivial` assumption);
its elements coincide and the assertion holds. For J = zero the difference condition
already gives equality. For J = top the radical hypothesis forces the zero ring.
The idempotents zero and one cannot be congruent modulo such an ideal in a nonzero ring.
Arbitrary characteristic and rings with nonnilpotent Jacobson radical are included;
there is no nilpotence, locality, Noetherianity, or domain hypothesis.

Source checked: the local Stacks tex is absent on this machine, so the official pages
https://stacks.math.columbia.edu/tag/09XF and
https://stacks.math.columbia.edu/tag/0ELY were opened. Tag 09XF states injectivity
for a Zariski pair; Tag 0ELY defines that pair by the Jacobson radical containment.
The node agrees, with no disputed statement or node fault.

Searches (all msearch calls use group G1 and this item's id):

- `leanfinder`: "Two idempotents in a commutative ring whose difference belongs to an
  ideal contained in the Jacobson radical are equal". Eight hits; among them
  `existsUnique_isIdempotentElem_eq_of_ker_isNilpotent` (nilpotent kernel only),
  ideal-idempotence characterizations, `Ideal.jacobson_idem`, and
  `IsIdempotentElem.sub_iff`. None has this statement.
- `loogle`: `IsIdempotentElem, Ideal.jacobson`. Zero hits.
- `leansearch`: "Idempotent elements congruent modulo an ideal contained in the
  Jacobson radical are equal". Service unavailable: Internal Server Error;
  recorded as unavailable, without a search verdict.
- `grep` via msearch:
  `(idempotent|IsIdempotentElem).*(jacobson|radical)|(jacobson|radical).*(idempotent|IsIdempotentElem)`.
  Only two unrelated category-theoretic preradical hits.
- Local `rg -n` with
  `idempotents-determined|eq_of.*jacobson|idempotent.*radical|IsIdempotentElem.*jacobson`
  in Mathlib, the source `WeilConjectures`, and project `lean/Sheaf`:
  unrelated Krull dimension/Nakayama statements and a docstring citing this node
  in `HenselianOfEtaleSectionLifting.lean`; no matching declaration.
- Local `rg -n` of the exact node id in source `WeilConjectures`: no matches.
- Local `rg -n` of `eq_of_sub_mem_of_le_jacobson` in all libraries and the upstream
  name index: no matches.

Validation: the module is submitted to `scompile.py` for a single-file server compile,
and the complete sandbox to `deliver2.py --no-push`. The independent second reader
will add their own reading and deliver; this worker does not push.


## Second reading by G1

I independently read the sandbox node and module, both Mathlib definitions used
in the signature, and the source place. The local Stacks checkout is absent;
I read the official [09XF](https://stacks.math.columbia.edu/tag/09XF),
[0ELY](https://stacks.math.columbia.edu/tag/0ELY), and
[00HN](https://stacks.math.columbia.edu/tag/00HN) pages and the original
[more-algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex),
lines 2236–2262. The section's standing convention introduces a pair as a ring
and an ideal; it imposes no finiteness, locality, or nonzero-ring assumption.
Tag 0ELY adds precisely radical containment; Tag 09XF states injectivity.

Object, hypothesis, and conclusion checklist (H3):

- Object R, a commutative ring: `{R : Type u} [CommRing R]`. Exact; no
  domain, field, local, Noetherian, or Nontrivial instance is added.
- Object J, an ideal of that same R: `(J : Ideal R)`. Exact.
- Hypothesis J is contained in the Jacobson radical:
  `(hJ : J ≤ Ideal.jacobson (⊥ : Ideal R))`. Exact.
  I opened `Mathlib.RingTheory.Jacobson.Ideal`: `jacobson I` is the infimum
  of maximal ideals containing I; at bottom this is all maximal ideals.
  Its `jacobson_bot` also identifies it with `Ring.jacobson R`.
- Objects e and e', arbitrary elements of R: `{e e' : R}`. Exact; implicit
  binders still quantify universally and follow the ring and ideal hypotheses.
- Hypothesis e squared equals e: `(he : IsIdempotentElem e)`. Exact.
- Hypothesis e' squared equals e': `(he' : IsIdempotentElem e')`. Exact.
  I opened `Mathlib.Algebra.Group.Idempotent`: the predicate is literally
  `a * a = a`, which is the square equation in a ring.
- Hypothesis their difference lies in J: `(hee' : e - e' ∈ J)`. Exact.
- Conclusion the two elements coincide: `e = e'`. Exact.
- Clause the map on idempotents to R/J is injective: this is the same
  universal equality implication, not an independent stronger assertion.
  Quotient classes agree exactly when their difference lies in J; equality
  of underlying elements is equality of idempotent subtypes by proof
  irrelevance. Quotient ring maps preserve the square equation.

There are no statement dependencies, new nodes, dependency modules, or
statement corrections to audit (H12/H13 and correction-citer checks are
inapplicable). Both notions come directly from Mathlib, with no private copy.
No object, hypothesis, or clause mismatch was found.

Edge cases: the zero ring is included and has only one element, so equality
holds even though there are no maximal ideals. J = bottom reduces the
hypothesis to zero difference. J = top under radical containment forces the
zero ring. The cases e = 0 and e' = 1 are excluded by radical containment
only when the ring is nonzero, as intended. Arbitrary characteristic,
nonnilpotent radicals, and rings with infinitely many maximal ideals are
allowed. `universe u` is bound explicitly and arbitrary; no carrier-size
restriction arises. There is no index set, scheme, zero object, or natural
number parameter in this node, so their associated edge cases do not arise.

Independent H4 searches, using vocabulary different from the worker:

- `msearch.py ... leanfinder "The quotient map by an ideal in the Jacobson
  radical is injective on idempotent elements"`: eight hits. I opened the
  closest `PrimeSpectrum.basicOpen_injOn_isIdempotentElem` signature and
  the nilpotent-kernel uniqueness theorem in `RingTheory/Idempotents`.
  The former concerns equality of basic opens in the prime spectrum, while
  the latter assumes every kernel element nilpotent. Neither is this node.
  Other hits concern product maps, quotient radicals, and cotangent modules.
- `msearch.py ... loogle "IsIdempotentElem, Function.Injective"`: zero hits.
- `msearch.py ... grep` in RingTheory, with regex
  `(idempotent|IsIdempotentElem).*(quotient|injective|jacobson)|(quotient|injective|jacobson).*(idempotent|IsIdempotentElem)`:
  nine hits concerning orthogonal-family maps, localization away from an
  idempotent, and product quotients; none is this statement.
- Independently ran local `rg` with that vocabulary plus `radical` and the
  exact declaration name on the source `WeilConjectures`, project
  `lean/Sheaf`, and `dag/lean_names_upstream.json`. Only unrelated quotient
  localization/product results and docstring references were found; no
  existing declaration or name collision. The worker's LeanSearch outage
  remains recorded as unavailable, not as a mathematical search verdict.

H5/H6: the only declaration is this named theorem, with `sorry` as its
entire proof; no definition or auxiliary proof is added. H8: both docstrings
name the source and blueprint id. The theorem docstring follows both node
steps: local idempotents are zero or one and agree by their residue values;
then the annihilator argument detects zero difference globally. H9: imports
are used by the signature, the namespace is upstream-compatible, every line
is at most 100 characters, and all binders and the universe are explicit.
The node's `lean.statement` was mechanically compared with the file's
signature through the text immediately before `:= by`: verbatim equal.

Second reading changed only this report; the correct Lean and node record
were left unchanged. Validation is recorded below after server compilation
and the delivery dry run.

Validation: `scompile.py` returned exit code 0 (compiled in 1.1 s),
with no errors or warnings. `deliver2.py --no-push` printed OK: the
complete delivery passes preflight and server compilation.
