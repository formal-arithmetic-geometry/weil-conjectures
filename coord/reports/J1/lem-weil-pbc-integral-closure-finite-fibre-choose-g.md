## Worker report

The module `Sheaf/AlgebraicGeometry/IntegralClosureFiniteFibreChooseG.lean` states
`AlgebraicGeometry.integralClosure_finite_fibre_choose_g` with `sorry` as required for
stage 2. It uses Mathlib's `IsIntegralClosure B' A B` for the integral closure, ideal
quotients `(B ⧸ Ideal.map (algebraMap A B) I)` and `(B' ⧸ Ideal.map (algebraMap A B') I)`,
ring equivalences to `C₁ × C₂`, and `morphismRestrict` to express the assumed isomorphism
of the restriction over the open `U`. The conclusion chooses `g : B'` lifting the first
idempotent, states that every prime in `D(g)` lies in `U`, and states that the induced
localization map `Localization.awayMap (algebraMap B' B) g` is bijective.

The hypotheses render the source clauses as follows: `A B B' C₁ C₂` and commutative-ring
instances provide the rings; the three `Algebra` instances and `Algebra.FiniteType A B`
encode the ring map and finite-type assumption; `hclosure` is the integral-closure clause;
`I` is the ideal; `eB` and `eB'` are the two product decompositions; `U` is an open of
`Spec B'`; `hU` says the primes of the first factor map into `U`; and `hIso` says the
restricted scheme morphism is an isomorphism. In the conclusion, `Ideal.Quotient.mk ... g
= eB'.symm (1,0)` is the prescribed idempotent lift, the quantified prime condition is
`D(g) ⊆ U`, and `Function.Bijective (Localization.awayMap ...)` is the localization
isomorphism.

Dependencies used from the node statement are the Mathlib notions corresponding to
`def-weil-affine-spectrum` (`AlgebraicGeometry.Spec` and `Spec.map`),
`lem-weil-pbc-spec-clopen-idempotent` (`PrimeSpectrum` basic-open/idempotent framework),
`lem-weil-pbc-integral-spec-closed-map` (`PrimeSpectrum.comap` for integral maps), and
`lem-weil-pbc-spec-integral-ring-map-integral` (`IsIntegralClosure`/integrality notions).
Their recorded matches were inspected; no project declaration states this theorem.

Edge cases checked: `C₁` may be empty/zero, `U` may be empty only when the first-factor
condition is correspondingly vacuous, and `g = 0` is allowed (then the quantified basic-open
condition is vacuous). No finiteness or nonzeroness assumptions were added.

Searches made: `msearch.py ... leanfinder` for an idempotent lift and localization
isomorphism (no exact match); `msearch.py ... loogle` for localization-map bijectivity
(no combined result); `msearch.py ... grep` and `rg` over Mathlib and
`WeilConjectures/` for integral-closure/spec-localization declarations (only separate
ingredients); `rg` over `lean/Sheaf` for existing declarations (none).

## Earlier second reading (a previous round; superseded)

- Item statement: checked the finite-type ring map, integral-closure condition, quotient product decompositions, neighbourhood condition, restricted scheme isomorphism, idempotent lift, principal-open inclusion, and localization bijectivity against Stacks Tag 09XH.
- Lean rendering: `IsIntegralClosure B' A B`, the two quotient ring equivalences, `hU` via the two `PrimeSpectrum.comap` maps, `hIso` via `morphismRestrict`, and `Localization.awayMap` match those clauses.
- Edge cases: zero factors and vacuous principal opens remain permitted; no extra nonzero or finiteness assumptions were introduced.
- No new nodes or statement correction.


## Second reading by J1

Independent second reading of the node and the complete delivery (one node, one
module). The earlier second reading is superseded. The Worker report is preserved
as the history of the first draft, but its claims about the hypotheses are corrected
below. No node statement correction, new definition node, or dependency module.

Source read: Stacks `more-algebra.tex`, Lemma `lemma-helper-finite-type`, Tag 09XH,
including its hypotheses and the whole proof (local text at
`/home/ubuntu/c1-stacks-review/more-algebra.tex`, lines 2505–2552). The source assumes
only a pair `(A,I)`, a finite-type map, and finiteness of the first quotient factor;
it introduces separate primed factors before identifying the first factor at the
END of the argument. In particular that identification cannot be assumed here.
The node extracts the choice-of-g step with the neighbourhood isomorphism supplied
as a hypothesis. I checked the five proof steps against this extracted statement.

Object/hypothesis/conclusion checklist, in the order of the node:

1. Commutative ring A: `(A : Type v) [CommRing A]`. Exact.
2. Ideal I of A: `(I : Ideal A)`. Exact, including I = top or bottom.
3. Finite-type map A → B: `(B : Type u) [CommRing B] [Algebra A B]
   [Algebra.FiniteType A B]`. Exact; no finite-module or Noetherian hypothesis.
4. B/IB = C₁ × C₂: separate rings `C₁`, `C₂`, their CommRing instances,
   `Algebra (A ⧸ I)` instances, `eB`, and `heB`. `heB` says that the quotient
   decomposition preserves the base scalar map; checking it on representatives
   a : A checks every element of A/I since the quotient map is surjective. Exact.
5. C₁ finite over A/I: `[Module.Finite (A ⧸ I) C₁]`. Previously missing; repaired.
6. B' is the integral closure inside B: `B'`, CommRing/Algebra instances,
   `hclosure : IsIntegralClosure B' A B`. I opened its definition: it requires
   injectivity of `algebraMap B' B` and says its image is precisely the elements
   integral over A. Thus it represents the inclusion, not an arbitrary map.
   `[IsScalarTower A B' B]` now ensures that the A-structure on B' is the one
   inherited from B, as the node requires. Exact.
7. φ is the inclusion-induced map: `Spec.map (CommRingCat.ofHom
   (algebraMap B' B))`. Exact, with the right contravariant orientation.
8. B'/IB' = C₁' × C₂' as A/I-algebras: independent `C₁'`, `C₂'`, their
   CommRing and A/I-Algebra instances, `eB'`, `heB'`. Previously the primed
   factors were replaced by C₁ and C₂, an unjustified stronger assumption.
   Repaired; no equality or isomorphism of the corresponding factors is assumed.
9. The two factors map respectively into C₁ and C₂: `f₁`, `f₂` are
   A/I-algebra homomorphisms and `hprod` makes the inclusion-induced quotient
   map their product under the decompositions. The equality is checked on all
   b : B', hence covers the whole quotient. Previously missing; repaired.
10. ε' = (1,0): `eB'.symm (1, 0)` in the primed quotient. Exact.
11. Open neighbourhood U of Spec(C₁'): `(U : (Spec ... B').Opens)` and `hU`
    use comap of the first-factor projection followed by comap of the quotient
    map. This is precisely the composite surjection B' → B'/IB' → C₁', not
    the spectrum of C₁. Corrected along with the factor rings. Exact.
12. φ⁻¹(U) → U is an isomorphism of locally ringed spaces: `hIso : IsIso
    (Spec.map ... ∣_ U)`. Opened `morphismRestrict`: it is the canonical
    restriction from the inverse-image open, identified with the pullback of U.
    Schemes form a full subcategory of locally ringed spaces, so this is exactly
    the required isomorphism. This hypothesis is substantive, not automatic.
13. There exists g in B': `∃ g : B'`. Exact; one g serves all conclusions.
14. g maps modulo IB' to ε': `Ideal.Quotient.mk ... g = eB'.symm (1, 0)`.
    Exact, with the corrected primed product.
15. D(g) ⊆ U: the quantified implication for every `p : PrimeSpectrum B'`
    with g not in p. This is the definition of the principal open. Exact.
16. For that g, B'_g → B_g is an isomorphism: `Function.Bijective
    (Localization.awayMap (algebraMap B' B) g)`. Opened awayMap: its target
    localizes B at the image of g. Bijectivity of a ring hom is precisely the
    existence of its inverse ring hom. Exact, without choosing a different map.

Dependency audit: opened all four stmt_deps and their recorded Mathlib signatures.
`def-weil-affine-spectrum` is Mathlib `AlgebraicGeometry.Spec` and `Spec.map`
(Scheme.lean), which are used directly. The other three are theorem ingredients,
not new notions required to type the statement: `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen`
(Topology.lean:1084), `PrimeSpectrum.isClosedMap_comap_of_isIntegral`
(Topology.lean:1156), and `AlgebraicGeometry.IsIntegralHom.SpecMap_iff`
(Morphisms/Integral.lean:94). None is replaced by a private definition; their
mathematical contents and quantifiers were checked. Their signatures do not need
repair for this delivery. Mathlib also supplies IsIntegralClosure, quotient rings,
finite modules, product algebras, restriction, and localization maps. No absent
notion required a new node.

Edge cases: no Nontrivial, domain, field, characteristic, Noetherian, or proper-ideal
assumption. All zero rings and zero factors remain permitted; C₁' = 0 makes hU
vacuous and ε' = 0, allowing g = 0 and empty principal opens. If U is empty,
hIso is the isomorphism between the empty restrictions; the neighbourhood condition
then forces the first factor spectrum empty, as in the node. If I = top both
quotient products are zero and the conclusion still permits g = 0. There is no
index set or n in this statement. A and the four factors now have independent
universes; B and B' share the arbitrary universe u of Mathlib's scheme category.
Any pair of rings can be represented in a common universe, and there is no
quantification over tests in a potentially smaller universe. Every variable and
universe is bound explicitly; the server compile confirms this.

Independent searches: msearch LeanFinder for a prescribed residue-idempotent lift
with a principal open inside a neighbourhood and localization bijectivity found
only StructureSheaf fraction/basic-open ingredients. Loogle `Localization.awayMap`
found the map, its injective/surjective criteria, and pointwise local-ring lifting
lemmas, none the prescribed-idempotent neighbourhood statement. LeanSearch for
existence of such a lift was attempted but returned service unavailable (Internal
Server Error); no negative verdict is claimed from it. `rg` by concepts
`idempotent.*lift`, `lift.*idempotent`, `integral closure`, `integralClosure`,
`exists.*basicOpen`, and `localization` across Mathlib, WeilConjectures, and
lean/Sheaf found the clopen-idempotent theorem, basic-open section descriptions,
ZariskisMainAway, and unrelated henselian idempotent lifting. Those do not state
this node (ZariskisMainAway chooses an element away from a single quasi-finite
prime, without the prescribed residue or arbitrary neighbourhood). The chosen
full declaration name is absent from upstream-name records and the source/library.
No exact existing declaration found; the module is retained.

Repairs: restored the distinct primed factors, C₁ finiteness, base-algebra
compatibility, and product-map compatibility. Expanded the docstring to all five
proof steps with their node references, restored the standard copyright header,
and made lean.statement byte-for-byte equal to the signature. No definitions,
proved claims, additional axioms, or untracked supporting modules. The only proof
is the named theorem's stage-2 sorry. All lines are at most 100 characters.

Validation: server single-file compilation passed with no errors or warnings.
