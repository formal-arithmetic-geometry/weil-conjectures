## Worker report

The module `Sheaf.Algebra.ZariskiPairFlatIntegralIsomorphism` states the theorem from
Stacks Tag 0ELZ. It binds commutative rings `R` and `S`, a ring map `f`, and an ideal
`I`. The Zariski-pair hypothesis is `hI : I ≤ Ring.jacobson R`; flatness,
integrality, and finite presentation are respectively `hflat : f.Flat`,
`hintegral : f.IsIntegral`, and `hfinitePresentation : f.FinitePresentation`. The
reduction map is Mathlib's `Ideal.quotientMap (Ideal.map f I) f
(Ideal.le_comap_map)`, and `hquotient` asserts its bijectivity. The conclusion
`Function.Bijective f` says that the original ring map is an isomorphism.

The dependency declaration used is Mathlib `RingHom.Flat` (module
`Mathlib.RingTheory.RingHom.Flat`). Integrality and finite presentation use
Mathlib's `RingHom.IsIntegral` and `RingHom.FinitePresentation`; Jacobson radical
and quotient maps use `Ideal.jacobson`, `Ring.jacobson`, and
`Ideal.quotientMap`.

Edge cases checked include `I = ⊥`, `I = ⊤`, zero rings, and the empty finite
presentation (the Mathlib predicates allow these); no finiteness of generators was
added beyond `FinitePresentation`.

Searches made: `msearch.py leanfinder` for the full flat-integral-finite-presentation
isomorphism statement (no match); `msearch.py loogle` for
`Module.Flat, Algebra.IsIntegral, Algebra.FinitePresentation,
Function.Bijective (algebraMap _ _)` (no result); grep of Mathlib RingTheory and
project `lean/Sheaf` for Jacobson, quotient-map, and bijective algebra-map results
(found only component lemmas, including `RingHom.Flat` and `Ideal.quotientMap`).
The source repository search found no existing declaration of this theorem.

## Earlier second reading (a previous round; superseded)

I reread the node statement and Stacks Tag 0ELZ. Each hypothesis is present: the
commutative rings and map, the ideal in the Jacobson radical, flatness, integrality,
finite presentation, and the quotient isomorphism. The quotient clause is rendered
by the canonical map from `R ⧸ I` to `S ⧸ Ideal.map f I`, with its required ideal
containment supplied by `Ideal.le_comap_map`; this is exactly the induced map in the
source. The conclusion is the stated isomorphism of rings expressed as bijectivity
of `f`, with no extra assumptions or dropped cases.

## Second reading by M1

I independently opened the item node, its Lean module, and the recorded statement
and Mathlib declarations of `def-weil-pbc-flat-ring-map`. The local Stacks checkout
is absent on this machine, so I read the official Stacks source at
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex,
section `section-zariski-pairs`, definition `definition-zariski-pair` (0ELY),
and lemma `lemma-check-isomorphism-zariski` (0ELZ), including its proof.
The section introduces arbitrary rings and ideals; it imposes no Noetherian,
local, characteristic, or nonzero assumption. The node agrees with that source.

Object/hypothesis/conclusion inventory and H3 verdicts:

- Arbitrary commutative base ring A: `{R : Type u} [CommRing R]`. Exact.
- Arbitrary commutative target ring B: `{S : Type v} [CommRing S]`. Exact;
  its universe is independent of that of R.
- The specified unital ring map A -> B: `(f : R →+* S)`. Exact; all the
  properties and the conclusion concern this same map.
- The ideal I of A: `(I : Ideal R)`. Exact; not assumed finitely generated.
- The Zariski-pair condition: `(hI : I ≤ Ring.jacobson R)`. Exact.
  I opened `Ideal.jacobson`, its maximal-ideal infimum definition, and
  `Ideal.jacobson_bot`, identifying the radical of the zero ideal with
  `Ring.jacobson R`. This is containment in every maximal ideal.
- Flatness: `(hflat : f.Flat)`. Exact. The dependency's recorded declaration
  `RingHom.Flat` in `Mathlib.RingTheory.RingHom.Flat` defines `Module.Flat R S`
  using `f.toAlgebra`. I also checked the tensor-injectivity characterization
  `Module.Flat.iff_lTensor_preserves_injective_linearMap` in Flat/Basic.lean.
  The recorded declaration is usable and no replacement dependency is needed.
- Integrality: `(hintegral : f.IsIntegral)`. Exact. I opened IsIntegral/Defs.lean:
  every target element satisfies a monic polynomial evaluated with f.
- Finite presentation as an algebra: `(hfinitePresentation : f.FinitePresentation)`.
  Exact. I opened the RingHom definition and `Algebra.FinitePresentation.out`:
  a surjection from `MvPolynomial (Fin n) R` with finitely generated kernel,
  equivalent to the node's finite list of generators and relations.
- The specified induced map A/I -> B/IB is an isomorphism: `hquotient` is
  `Function.Bijective (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map)`.
  Exact. I opened quotientMap's signature and formula on quotient classes:
  it sends the class of x to the class of f(x). `Ideal.map f I` is the extended
  ideal IB. The implicit source ideal is I, fixed by `Ideal.le_comap_map`;
  this containment is construction data, not an extra hypothesis.
- Conclusion: `Function.Bijective f`. Exact: a bijective unital ring homomorphism
  has a ring-homomorphic inverse. This states that f itself is an isomorphism,
  rather than the mere existence of an unrelated isomorphism R ≃+* S.

Edge cases: I = zero is allowed and the quotient premise already identifies f
as an isomorphism. I = top is allowed precisely when R is the zero ring, since
its Jacobson radical can equal top only then; a unital map out of that ring forces
S to be zero as well. Both zero rings and a zero target are admitted by CommRing;
for a nonzero R, the quotient premise excludes a zero target because I lies in
its proper Jacobson radical. Empty spectra are therefore covered. There is no
index-set binder; algebra presentations allow n = 0 and an empty relation set.
No nontriviality, field, characteristic, or Noetherian assumption occurs, and
universes u and v are explicitly bound. None of the hypotheses is universally
true for arbitrary f and I.

Independent H4 searches (different phrases from the first reader):

- `msearch.py leanfinder`: "A flat integral ring homomorphism of finite
  presentation is bijective if its reduction modulo an ideal contained in the
  Jacobson radical is bijective". Eight component results, including
  `Module.IsLocalRing.linearCombination_bijective_of_flat`,
  `RingHom.Flat.of_bijective`, and `RingHom.FinitePresentation.of_bijective`;
  none states this global implication.
- `msearch.py loogle`: `RingHom.Flat, RingHom.FinitePresentation,
  Function.Bijective`. Zero hits.
- `msearch.py leansearch`: "flat integral finitely presented ring map
  isomorphism modulo Jacobson radical". Service unavailable (Internal Server
  Error); this is recorded as unavailable, not a no-match verdict.
- Independent rg of all Mathlib, WeilConjectures, project lean/Sheaf, and
  dag/lean_names_upstream.json for `bijective.*jacobson`,
  `jacobson.*bijective`, `zariskiPair`, `ZariskiPair`,
  `check.isomorphism.zariski`, and `0ELZ` found only Jacobson-radical transport
  under an already bijective map. The related project declaration
  `RingHom.bijective_quotientMap_pow_of_flat` was opened: it propagates a
  quotient isomorphism to positive powers, not to the original map.
  `Module.algebraMap_bijective_iff_rankAtStalk` is likewise only the final
  rank-one ingredient. No existing statement renders this node.

Repairs: the initial `Sheaf.Algebra` topic did not follow the RingTheory
convention, so the module is now
`Sheaf.RingTheory.ZariskiPairFlatIntegralIsomorphism` and its lean.module and
lean.file records were updated. Added the standard license/author header.
The original proof docstring omitted module finite presentation and the fibre
and maximal-ideal argument; expanded it into the node's three proof steps with
all their dependency names. Narrowed the integrality import from Basic to Defs,
which supplies the definition actually used. No signature or mathematical
statement changed; lean.statement remains verbatim equal to the signature.
The earlier worker report's old module path describes the original submission.

No new definition nodes or dependency modules are needed. The module contains
one named theorem, with its sole proof `by sorry`, and no definitions, private
copies, file-local notation, hidden let/show binders, or proved auxiliaries.
Every declaration has the source and blueprint tag, and lines are at most 100
characters. Server single-file compilation via scompile.py succeeded cleanly
(exit 0, 1.9 seconds), with no warnings.
