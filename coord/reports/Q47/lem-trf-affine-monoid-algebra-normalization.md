## Worker report

Q47 states `lem-trf-affine-monoid-algebra-normalization` in
`Sheaf.RingTheory.AffineMonoidAlgebraNormalization`, with the sole postponed theorem
`MonoidAlgebra.affine_monoid_algebra_normalization`. Its proof is exactly `by sorry`.
The five accompanying definitions construct the canonical monoid/algebra maps; none
chooses an unspecified map, object or algebra structure. No natural statement,
statement dependency, proof, proof dependency or other node field was changed.

I opened the node, its statement dependency, the recorded dependency source and the
proof-dependency nodes. I read ILO Exposé VIII 3.1.17 and 3.2.9 directly from the PDF
(printed pp. 101 and 104; PDF p. 110 contains printed p. 104). The source says that
saturation induces a finite morphism, an isomorphism on the dense group-completion
open, and the normalization. This delivery retains the node's more explicit algebraic
clauses, including normality inside the full fraction field.

Hypotheses and objects, clause by clause:

- The field is `(k : Type v) [Field k]`, with no characteristic restriction.
- The commutative monoid is `(P : Type u) [CommMonoid P]`. The source's additive
  notation is presented multiplicatively: identity `1` is source `0`, a product is
  source addition, and a positive power is a positive integer multiple. This is the
  same convention as the dependency's recorded `FineFan.IsFine` and saturation.
- Fineness is precisely `hP : AlgebraicGeometry.FineFan.IsFine P`, whose full
  definition is `Monoid.FG P ∧ Function.Injective (Algebra.GrothendieckGroup.of)`.
  Thus finite generation and integrality are both present, with neither sharpness
  nor saturation assumed.
- `G = P^gp` is the dependency's canonical `Algebra.GrothendieckGroup P`.
  `[IsMulTorsionFree (GrothendieckGroup P)]` states exactly torsion freeness of this
  abelian group, not of some independently supplied group.
- The image of `P` inside `G` is `MonoidHom.mrange (GrothendieckGroup.of (M := P))`.
  Its saturation is the recorded `FineFan.saturation` of that image. This definition
  is the submonoid closure of `{g | ∃ n : ℕ, 0 < n ∧ g ^ n ∈ image P}`. This root
  set is itself a submonoid in a commutative group: identity has witness 1, and
  products combine positive witnesses by their product. Hence the recorded closure
  is exactly the root subset in the node; no new saturation definition is introduced.
- `MonoidAlgebra k T` is Mathlib's finite-support monoid algebra, with monomials
  multiplying by addition in the source's notation, and identity the monomial at
  the identity of `T`.

Conclusions, in the order of the conjunction:

1. `Function.Injective (normalizationAlgebraMap k P)` is the natural embedding
   `k[P] → k[P^sat]`. Its data is `mapDomainRingHom k (normalizationMonoidMap P)`;
   the monoid map first restricts completion to its range and then uses the recorded
   `FineFan.intoSaturation`. Thus the map sends each monomial to that same exponent.
2. `Function.Injective (normalizationAmbientMap k P)` is the natural embedding
   `k[P^sat] → k[G]`, obtained by `mapDomainRingHom` of the subtype monoid map.
   The composite of these two maps is the canonical completion map on monomials.
3. The explicit injectivity of `algebraMap k[G] (FractionRing k[G])` includes the
   ambient group algebra in `K`. The preceding maps and this map therefore give
   the claimed nested subrings, all under the specified canonical maps.
4. The next three conjuncts are `IsDomain` for exactly `k[P]`, `k[P^sat]`, and
   `k[G]`, separately, with no domain hypotheses smuggled into the binders.
5. `K` is literally `FractionRing (MonoidAlgebra k (GrothendieckGroup P))`.
   Its canonical fraction-ring instance supplies the group-algebra clause, and the
   domain conclusion makes this total fraction ring a field. The two explicit
   `@IsFractionRing` conjuncts assert it is also the fraction field of `k[P]` and
   `k[P^sat]`. Their algebra structures are specifically `.toAlgebra` of the
   canonical composite maps `normalizationFractionMap` and
   `normalizationSaturatedFractionMap`, not arbitrary existential structures.
6. For every `x : K`, `(normalizationFractionMap k P).IsIntegralElem x ↔
   x ∈ Set.range (normalizationSaturatedFractionMap k P)` says precisely that the
   saturated algebra's image is the entire integral closure. Mathlib defines
   `RingHom.IsIntegralElem f x` as the existence of a monic polynomial over the
   source ring whose `eval₂ f x` is zero. Both directions and every element of the
   full fraction field are included; the quantifier is not restricted to `k[G]`.
7. `(normalizationAlgebraMap k P).Finite` is finite generation of `k[P^sat]` as
   module over `k[P]` via this particular map. Mathlib's `RingHom.Finite` uses the
   map's `.toAlgebra` and `Module.Finite`.
8. The final universal implication uses
   `(normalizationSaturatedFractionMap k P).IsIntegralElem x` and concludes
   membership in its range. It states integral closedness of the saturated
   algebra in the same full field `K`, separately from the preceding closure
   identification, exactly as requested.

Dependency declarations used:

- `def-trf-fine-fan-blowup`, module
  `Sheaf.AlgebraicGeometry.FineFanBlowup`: `AlgebraicGeometry.FineFan.IsFine`,
  `AlgebraicGeometry.FineFan.saturation`, and
  `AlgebraicGeometry.FineFan.intoSaturation`. I opened these full definitions and
  docstrings. No copy of one is defined here.
- Mathlib `Algebra.GrothendieckGroup`, `Algebra.GrothendieckGroup.of`,
  `MonoidHom.mrange`, `MonoidHom.mrangeRestrict`, `Submonoid.subtype`, and
  `MonoidAlgebra.mapDomainRingHom` give the actual canonical constructions.
- Mathlib `FractionRing`, `IsFractionRing`, `RingHom.IsIntegralElem` and
  `RingHom.Finite` give the mathematical predicates, with their definitions read.
- Proof-only imports retain the stated input
  `fine_monoid_finite_saturation` from `Sheaf.GroupTheory.FineMonoidFiniteSaturation`
  and the Mathlib leaves: `Module.basisOfFiniteTypeTorsionFree'`, the normality
  instance for polynomials, `isIntegrallyClosed_of_isLocalization`,
  `IsFractionRing.isFractionRing_of_isLocalization`, and domain localization APIs.
  These appear in the proof docstring, with all eight steps of the node's proof.
- The four proof dependencies `lem-trf-monoid-algebra-domain-fraction`,
  `lem-trf-monomial-integrality`, `lem-trf-integral-support-saturation` and
  `lem-trf-saturated-monoid-algebra-normal` currently have neither `lean` nor
  `mathlib_match` records. They are proof inputs only: the statement needs none of
  their interfaces, so there is no missing statement prerequisite to supply and
  no importable module to invent. Their full node statements were read and their
  planned uses remain explicit in the theorem's proof docstring.

Edge cases checked mathematically before writing:

- The singleton additive monoid has singleton group completion and saturation;
  all algebras become the coefficient field. No nonzero-rank, nontrivial-monoid,
  nonempty-generator or positive dimension binder excludes it.
- A fine monoid may have units; a finitely generated torsion-free abelian group
  viewed as a monoid is allowed, with saturation the whole group and both inclusions
  identities after the canonical identifications. No `IsSharp` assumption occurs.
- The additive submonoid generated by 2 and 3 gives a genuine nonsaturated input,
  with saturation the nonnegative lattice. Saturation is a conclusion/construction,
  never a hypothesis on `P`.
- Arbitrary fields, including positive characteristic, are included. Torsion freeness
  is imposed on the group completion as stated; allowing torsion here would indeed
  invalidate the domain assertion in general. No extra order or basis is assumed.
- `u` and `v` are independent and explicitly declared. There is no quantifier over
  test objects with a universe too small, no local notation/instance, and no `let`
  or hidden arbitrary algebra map in the statement.

Searches made with the prescribed wrapper, group Q47 and this exact item:

- LeanFinder: "The integral closure of a fine torsion free additive monoid algebra
  over a field is the algebra of its saturation in the group completion". Eight
  returned hits concern general complete integral closure, fraction rings of
  integral closures, function-field integers and normal closure. None identifies
  a saturated monoid algebra with this integral closure.
- Loogle: `AddMonoidAlgebra, IsIntegral`. Zero hits.
- Mathlib grep: `(MonoidAlgebra|AddMonoidAlgebra).*(integralClosure|IsIntegrallyClosed)|saturat.*monoid.*algebra`.
  Zero hits.
- LeanSearch: "The integral closure of an affine torsion free monoid algebra over
  a field is its saturated monoid algebra". Eight hits on general integral closure,
  `IsIntegralClosure.of_isIntegrallyClosed`, and normal closure. They do not state
  monoid-algebra saturation normalization.
- `rg` of `WeilConjectures` and `lean/Sheaf` for monoid normalization/integrality
  and saturation/algebra patterns found complete toric model, formal dimension,
  fan and unrelated derived monoidal modules, without this theorem. Searching
  upstream `WeilConjectures` for this exact blueprint id returned no hit.
- `rg` of Mathlib, upstream `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for each of the six chosen declaration names
  returned no hit. No declaration is duplicated.

Validation: `scompile.py Q47 lem-trf-affine-monoid-algebra-normalization` compiled
this file separately as a sandbox module and under its final library module name,
both cleanly in under five seconds. The compile initially exposed that the recorded
fine-fan module is a legacy non-`module` file, so this module uses compatible legacy
imports; all imports are ordinary imports and the definitions/theorem are public
in the ordinary legacy sense. The unrelated generalized `MonoidHom.mrange` API
requires an explicit function call rather than field notation; that was repaired.
The theorem remains unproved as required. No statement dispute, correction, new
notion node or dependency replacement is necessary.

## Canonical helper declarations

The five definitions belong to the canonical maps already named in the item's own
statement; they introduce no separate mathematical notion. Every one carries the
item's blueprint id and source in its docstring, and every one is listed in
`lean.declarations`. Their bodies are compositions of the recorded maps and Mathlib
maps, not `sorry` data. The only `sorry` belongs to the item's own named theorem.
Independent review is supplied by the maintainer, as required by the dispatch brief.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
