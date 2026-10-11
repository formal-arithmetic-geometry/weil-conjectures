## Worker report

The module states `purelyInseparable_integral_prime_unique` in
`Sheaf.RingTheory.PurelyInseparableIntegralPrimeUnique`. It uses commutative domain
rings `A` and `B`, an `Algebra A B` inclusion, normality of `A` as
`IsIntegrallyClosed A` together with `[IsDomain A]`, and finite generation as
`[Module.Finite A B]`. It introduces fraction fields `K` and `L` through
`[Field]` and `[IsFractionRing]`, with scalar-tower structures expressing the
maps induced by `A → B`; finite purely inseparable extension is rendered by
`[Module.Finite K L] [IsPurelyInseparable K L]`. For each prime ideal `p : Ideal A`
(the `[p.IsPrime]` hypothesis), the conclusion is `∃! q : Ideal B` with
`q.IsPrime` and `q.comap (algebraMap A B) = p`, exactly the lying-over clause.
The proof is `sorry` as required; its source proof is the three-step power,
existence, and uniqueness argument recorded in the node.

Dependencies used are Mathlib's `IsIntegrallyClosed`, `IsDomain`,
`IsFractionRing`, `IsPurelyInseparable`, and `Module.Finite`; the dependency
nodes `def-weil-pbc-normal-ring`, `def-pc-field-extension`, and
`def-weil-pbc-finite-purely-inseparable-extension` record these Mathlib notions.

Edge cases checked: characteristic zero is covered by Mathlib's purely
inseparable predicate; characteristic positive extensions use arbitrary powers;
`p` may be any prime ideal, including zero; and no nonemptiness or finite-index
assumption is introduced.

Searches performed with msearch.py:
- LeanSearch: "normal domain finite extension purely inseparable fraction fields unique prime
  lying over" returned service unavailable (Internal Server Error); no verdict drawn.
- LeanFinder: "finite extension of normal domains with purely inseparable fraction fields unique
  prime over each prime" returned eight hits on unramified extensions and Dedekind-domain
  primesOver cardinality; none states this lemma for arbitrary normal domains.
- Loogle: "IsIntegrallyClosed, IsPurelyInseparable" returned zero hits.
- Mathlib grep: "purely inseparable.*prime|unique.*prime.*integral|IsPurelyInseparable"
  under RingTheory returned 15 hits, chiefly tensor-product spectrum homeomorphisms and
  the ring-hom predicate. They do not state this finite-domain-extension assertion.
- rg of WeilConjectures and lean/Sheaf for FractionRing, IsPurelyInseparable, primesOver,
  and comap_surjective found relevant fraction-field and spectrum APIs but no exact theorem.
- rg of dag/lean_names_upstream.json, WeilConjectures and lean/Sheaf for the node id,
  chosen declaration name and "purely inseparable.*prime" found no exact declaration.

The local Stacks source is absent, so the source was read at
https://stacks.math.columbia.edu/tag/07PR, proof, the finite-subalgebra paragraph.
No correction to the node is needed. Only A is assumed normal; B is merely a domain.
The two scalar towers express equality of the composites A → K → L and A → B → L.
Since A → K and K → L are injective, these equalities also ensure A → B is injective,
so the algebra binder really is the inclusion required by the node. Conversely any
inclusion in the node admits exactly these compatible induced fraction-field maps.
Four independently bound universes cover rings and fraction fields in arbitrary universes.

Module sources of dependency notions: Mathlib.Algebra.Algebra.Defs (`Algebra`),
Mathlib.RingTheory.IntegralClosure.IntegrallyClosed (`IsIntegrallyClosed`), and
Mathlib.FieldTheory.PurelyInseparable.Basic (`IsPurelyInseparable`, with
`isPurelyInseparable_iff_pow_mem` identifying all characteristics). `Module.Finite`
is Mathlib's finite-generation predicate. No new nodes or dependency modules are needed.


## Second reading by M1

Independently read the item and all three statement-dependency nodes, the
Mathlib declarations implementing them, and the delivered module. Read the
Stacks `more-algebra.tex` source at `lemma-helper-G-ring` (07PR) from the
Stacks upstream raw source because the local literature checkout is absent:
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex.
Its finite-subalgebra paragraph uses a regular base, finite domain extensions,
and purely inseparable fraction fields. The node explicitly extracts the
normal-domain argument; regularity is not needed beyond normality for this
prime-uniqueness assertion. No node correction is necessary.

Object/hypothesis/conclusion checklist, each with verdict:

- Integral domains A and B: `(A : Type u) (B : Type v) [CommRing A]
  [CommRing B] [IsDomain A] [IsDomain B]`. Exact; B is not assumed normal.
- Inclusion A into B: `[Algebra A B]`, with its map `algebraMap A B`.
  Exact: both scalar towers identify the composite A -> B -> L with
  A -> K -> L. The latter is injective since A -> K is the fraction-field
  embedding and K -> L is a field map. Hence A -> B is injective without
  an omitted hypothesis. Conversely an inclusion gives these structures.
- B finitely generated as an A-module: `[Module.Finite A B]`. Exact:
  Mathlib Finiteness/Defs defines this as finite generation of the top
  submodule; there is no extra finite-presentation or Noetherian assumption.
- Normal domain A: `[IsDomain A]` and `(hA : IsIntegrallyClosed A)`.
  Exact domain clause of def-weil-pbc-normal-ring. Read
  IntegrallyClosed.lean: IsIntegrallyClosed is integral closure in FractionRing.
  Using a proof binder rather than an instance does not change the hypothesis.
- K = Frac(A), L = Frac(B): `[Field K] [Field L]`, `[Algebra A K]
  `[IsFractionRing A K]`, `[Algebra B L] [IsFractionRing B L]`.
  Exact: FractionRing.lean defines IsFractionRing as localization at the
  non-zero-divisors. Arbitrary models of the fraction fields are permitted.
- The induced inclusion K into L: `[Algebra K L] [Algebra A L]`
  `[IsScalarTower A K L] [IsScalarTower A B L]`. Exact compatibility,
  not an unrelated field extension. The maps from K are uniquely determined
  by agreement on A, because K is its fraction field.
- Finite purely inseparable L/K: `[Module.Finite K L]
  [IsPurelyInseparable K L]`. Exact recorded conjunction of
  def-weil-pbc-finite-purely-inseparable-extension. Read Basic.lean's class
  and `isPurelyInseparable_iff_pow_mem`, covering all characteristics.
- Every prime p of A: `(p : Ideal A) [p.IsPrime]`. Exact universal
  quantification after the extension data, not only maximal ideals.
- Exactly one prime q of B lying above p: `∃! q : Ideal B,
  q.IsPrime ∧ q.comap (algebraMap A B) = p`. Exact: uniqueness is among
  prime ideals satisfying the contraction equality, not all ideals.

Edge cases: the zero ring and empty spectra are excluded by the node's
integral-domain assumptions themselves, so IsDomain adds no restriction.
The zero prime and all nonmaximal primes are included. The identity extension
A = B is included. Characteristic zero forces the purely inseparable extension
to be trivial and is included; positive characteristic has no fixed prime
binder. The power argument permits n = 0 and e^0 = 1. No index set, scheme,
or positivity assumption is introduced. Universes u, v, w, x are all bound,
independent, and unrestricted; no test-object quantifier can become vacuous.

Independent searches (different search words from the worker):

- LeanSearch: "uniqueness of a prime lying over a prime of a normal domain
  in a finite radicial extension of fraction fields". Service unavailable
  (Internal Server Error); no negative verdict inferred.
- Loogle: `IsFractionRing, IsPurelyInseparable`: zero hits.
- LeanFinder: "finite algebra over an integrally closed domain has a bijection
  on prime spectra when its fraction field extension is radicial": eight
  hits, including going-down, lying-over existence, Zariski's Main Property,
  and quasi-finiteness; none gives the required uniqueness assertion.
- Source grep: read Mathlib Spectrum/Prime/Homeomorph.lean's
  `PrimeSpectrum.isHomeomorph_comap`. Its positive-power-in-range hypothesis
  still requires the entire first proof step here, so it is not an existing
  statement of this node. Tensor-product purely inseparable variants are
  base changes of fields, not this domain extension. Searched Mathlib's
  fraction-ring, purely-inseparable, integral-closure and finiteness APIs.
- Searched WeilConjectures, repository lean/Sheaf, and
  dag/lean_names_upstream.json for the declaration name, 07PR,
  `integrally.closed.*prime`, `radicial.*fraction`, and purely inseparable
  ring statements. Existing finite-subalgebra and formal-fibre modules have
  different conclusions. No duplicate statement or private definition found.

No new nodes or dependency modules are present or needed. All notions use
Mathlib's recorded declarations; the normal-domain conjunction follows the
recorded Mathlib match and the project's NORMAL RING convention.
No mismatches found and no Lean or node text changed. Only this independent
second-reading section was added. The sole theorem proof is `sorry`, with no
hollow definitions or proved auxiliary results. Its source docstrings carry
the blueprint id and all three proof steps (power in A, lying over, uniqueness).
The node's lean.statement matches the file signature verbatim. Single-file
scompile.py completed with exit code 0 and no warnings or errors.
