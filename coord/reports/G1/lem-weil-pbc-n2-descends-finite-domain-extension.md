## Worker report

The module `lean/Sheaf/RingTheory/IsN2OfFiniteExtension.lean` states
`isN2_of_finite_extension`, with its sole proof `sorry`. It introduces no definitions,
new nodes, or dependency modules, and changes only the item's `lean` record.

Hypothesis and clause matching:

- Integral domains A and B: `[CommRing A] [IsDomain A] [CommRing B] [IsDomain B]`.
- The inclusion A ⊆ B: `[Algebra A B]` and
  `hAB : Function.Injective (algebraMap A B)`. An injective algebra map is precisely
  a ring inclusion after identifying A with its image; no surjectivity is imposed.
- A Noetherian: `[IsNoetherianRing A]`.
- B finitely generated as an A-module: `[Module.Finite A B]`.
- The fraction fields: `[Field K] [Algebra A K] [IsFractionRing A K]` and
  `[Field E] [Algebra B E] [IsFractionRing B E]`. These are auxiliary choices of
  the fields already implicit in the N-2 conditions; they add no mathematical restriction.
- B N-2: `hB : IsN2 B E`.
- A N-2: conclusion `IsN2 A K`. Unfolding the dependency's definition gives exactly
  every finite field extension L/K (`[Field L] [Algebra K L] [FiniteDimensional K L]`),
  its composite A-algebra structure (`[Algebra A L] [IsScalarTower A K L]`), and
  `Module.Finite A (integralClosure A L)`. Thus the node's explanatory final clause
  is included in the conclusion, without a duplicate definition or redundant conjunction.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (and read
  `isNoetherianRing_iff_ideal_fg`), the exact Noetherian-ring predicate.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, available via JapaneseDomain.
- `Sheaf.RingTheory.JapaneseDomain`: `IsN2`; its full signature and docstring read
  in the repository's `lean/Sheaf/RingTheory/JapaneseDomain.lean`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, available transitively.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, available
  through JapaneseDomain and used by `IsN2`.
- Fraction-field and finite-dimensional structures are also provided by the same
  JapaneseDomain import (`Mathlib.RingTheory.Localization.FractionRing` and
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`).

Edge cases checked before writing: A = B is permitted; fields and degree-one L = K
are permitted, so normalization in the fraction field is included. No separability,
characteristic, positive dimension, or normality condition is imposed. The zero ring
is excluded exactly by the domain hypothesis. The algebra map must be injective:
merely an algebra structure would admit quotient maps. The two rings have independent
universes u and v; both auxiliary fraction fields lie in `Type (max u v w)`, which
can contain both rings and extensions. `IsN2` quantifies over extensions in that same
universe; every finite extension has a representative there. Arbitrary fraction fields
can likewise be lifted to this common universe. No small-universe test-algebra
hypothesis is used. Every variable and universe is explicitly bound, with
`set_option autoImplicit false`.

Source checked: the local literature clone is absent on this machine. Opened
https://stacks.math.columbia.edu/tag/032K instead: Lemma 10.161.7 requires a Noetherian
base domain and a finite inclusion of domains and gives precisely the N-2 implication.
Its proof is omitted with an integral-closure containment hint. The declaration docstring
expands the node's six proof steps with all their named dependencies. No statement
correction or disputed statement is needed.

Searches:

- `msearch.py ... leanfinder "N-2 Japanese domain descends along a finite injective
  extension of Noetherian domains"`: eight hits, including `fg_of_fg_of_fg`, Jacobson
  finite-type results and `IsIntegralClosure.isNoetherianRing`; none is N-2 descent.
- `msearch.py ... loogle "IsN2, Module.Finite, integralClosure"`: zero hits,
  unknown identifier IsN2 (the predicate is project-specific).
- `msearch.py ... leansearch "Japanese domain finite extension descent integral
  closure finite module"`: unavailable, Internal Server Error; no verdict inferred.
- `msearch.py ... grep "Japanese|IsN2|N-2|finite.*extension.*descent" RingTheory`:
  zero Mathlib hits.
- `rg -n 'IsN2|Japanese|n2_descend|032K'` over upstream WeilConjectures and
  repository lean/Sheaf: only the project's JapaneseDomain, NagataRing,
  LocalizationJapaneseDomain and existing related modules; no descent declaration.
- `grep -rn 'lem-weil-pbc-n2-descends-finite-domain-extension'` over upstream
  WeilConjectures: no hits.
- `tools/lean_names_upstream.py show lem-weil-pbc-n2-descends-finite-domain-extension`:
  no declarations for the item.

Validation: server compilation and the delivery dry run are run after writing the
module and node record. The independent second reading is left to the second reader.

## Second reading by G1

The node statement was read as the following list and checked against
`isN2_of_finite_extension` in `lean/Sheaf/RingTheory/IsN2OfFiniteExtension.lean`:

1. `A` and `B` are integral domains. Lean renders these as `(A : Type u)
   (B : Type v)`, `[CommRing A] [IsDomain A]`, and `[CommRing B] [IsDomain B]`.
   Verdict: exact.
2. The inclusion `A ⊆ B` is rendered by `[Algebra A B]` together with
   `hAB : Function.Injective (algebraMap A B)`. This is precisely an injective
   ring inclusion and imposes no extra finiteness or field hypothesis. Verdict:
   exact.
3. `A` is Noetherian. Lean has `[IsNoetherianRing A]`, the Mathlib predicate
   recorded by `def-weil-pbc-noetherian-ring`. Verdict: exact.
4. `B` is a finitely generated `A`-module. Lean has `[Module.Finite A B]`,
   the recorded rendering of `def-weil-finitely-generated-module`. Verdict:
   exact.
5. `K` and `E` are fraction fields of `A` and `B`, respectively. Lean
   introduces `K E : Type (max u v w)` with `[Field K] [Algebra A K]
   [IsFractionRing A K]` and `[Field E] [Algebra B E] [IsFractionRing B E]`.
   These are choices of the fraction fields and do not strengthen the statement.
6. `B` is N-2. Lean renders this as `hB : IsN2 B E`, using the project's
   `IsN2` definition: every finite-dimensional field extension of `E`, with the
   scalar tower, has finite integral closure. Verdict: exact.
7. The conclusion is that `A` is N-2. Lean concludes `IsN2 A K`, with the
   same quantifier, field-extension, scalar-tower, integral-closure, and
   `Module.Finite` clauses supplied by `JapaneseDomain.IsN2`. Verdict: exact.

The source is Stacks Algebra, Tag 032K (Lemma 10.161.7), lines 45256--45266;
its N-2 clause assumes a Noetherian domain included in a finite domain extension
and concludes N-2 descent. The Lean docstring records the source's omitted proof
hint expanded through the cited dependency nodes. No hypothesis or conclusion
was added, dropped, weakened, or strengthened, so no node or statement correction
was needed.

Edge cases were checked: `A = B` is allowed; the degree-one extension `L = K`
is included; zero rings are excluded exactly by `IsDomain`; no characteristic,
separability, positive-dimension, normality, or nonempty-index assumption is
introduced; and the common `Type (max u v w)` universe does not exclude finite
extensions or fraction fields. The scalar-tower clause is inherited from `IsN2`
and is not silently omitted.

Searches found no existing declaration in Mathlib, `WeilConjectures`, or the
repository's `lean/Sheaf`: grep for `IsN2`, Japanese/N-2 terminology and the
item id, plus `msearch.py` LeanFinder/Loogle searches for finite-extension
integral-closure descent, all returned no matching declaration. The only project
declaration of the notion is `Sheaf.RingTheory.JapaneseDomain.IsN2`, which was
read and used directly. The item has one citer,
`lem-weil-pbc-power-series-n2`; its proof uses this lemma for exactly the finite
power-series domain extension, so the use still holds.

No mismatch was found and no source or Lean file required alteration. The
unchanged module compiles with `scompile.py` (no errors or warnings other than
the permitted `sorry` declaration warning).

## Reviewer fix (R-n2d1157)

The delivered statement forced both fraction fields into `Type (max u v w)`, so it did not
cover a fraction field `K` of `A` living in a universe below `B`'s (e.g. `A K : Type`,
`B : Type 1`): a weakening of the node, which concerns the fraction field of `A` whatever
its model. Since `IsN2 R K` quantifies over extensions in `K`'s own universe and every finite
extension has a copy there, no common universe is needed. The fix gives independent universes
`(A : Type uA) (B : Type uB) (K : Type uK) (E : Type uE)`, the spelling of the landed sibling
`isN1_of_finite_domain_extension` (1623122bc). Every other binder is unchanged.
