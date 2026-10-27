## Worker report

Item: `lem-sfb-affine-associated-points-primes`, group Q66, stage 2.
Module: `Sheaf.AlgebraicGeometry.AffineAssociatedPointsPrimes`.
Declaration: `AlgebraicGeometry.Scheme.Modules.affine_associated_points_primes`.
The one theorem has proof `sorry`; no definitions or proofs were added.
The node is unchanged except for its `lean` record.

Source read: `literature/stacks-project/divisors.tex`, Tag 02OK,
`lemma-associated-affine-open`, statement and complete proof (lines 67–116).
This gives exactly the two implications and the Noetherian consequence.
The node states that consequence for a Noetherian affine coordinate ring,
which is precisely the condition the source uses in its last paragraph.

Hypotheses and objects, clause by clause:

- Any scheme X: `{X : Scheme.{u}}`, with an explicit unrestricted universe u.
- An O_X-module F: `(F : X.Modules)`; quasi-coherence is
  `(hqc : F.IsQuasicoherent)`. No coherence or finite-type hypothesis is imposed.
- An affine open W = Spec R inside X: `(W : X.Opens) (hW : IsAffineOpen W)`.
  Here R is `X.presheaf.obj (op W)`, its actual coordinate ring.
  This is the canonical affine-chart presentation, with `hW.fromSpec`
  identifying `Spec R` with W; the inclusion into X is an open immersion.
  No extra choice of chart or map is introduced.
- The module M = Gamma(W,F): `F.val.obj (op W)`, with its existing action of
  `X.presheaf.obj (op W)`.
- A point of W: `(x : W)`, and its point in X is `(x : X)`.
- Its corresponding prime ideal is `(hW.primeIdealOf x).asIdeal`.
  This construction returns a prime spectrum point, so primality is built in.
- Associated primes throughout are the exact element-annihilator predicate
  `RingTheory.annihilatorAssociatedPrimes R M`. The associated points are
  `Scheme.Modules.associatedPoints F`, defined using that same predicate
  for the maximal ideal of the stalk ring and the actual module stalk.
- First conjunct: membership of that prime in the annihilator-associated
  primes of the section module implies `(x : X) ∈ associatedPoints F`.
  This direction has no finite-generation or Noetherian assumption.
- Second conjunct: `(x : X) ∈ associatedPoints F` and
  `(hW.primeIdealOf x).asIdeal.FG` imply membership in those associated primes.
  Curried implications express the two hypotheses without imposing FG elsewhere.
- Third conjunct: `IsNoetherianRing (X.presheaf.obj (op W))` implies the
  requested iff, with the associated point on the left and associated prime
  on the right.
- No finite generation of M: there is no `Module.Finite` or other finiteness
  condition on `F.val.obj (op W)` in any binder or conjunct.

Dependency interfaces read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and its scheme morphisms.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType` exposes
  `SheafOfModules.IsQuasicoherent`, listed in that node's `lean.declarations`.
  Its `IsQuasiCoherentFiniteType` conjunction is deliberately not assumed:
  this item needs only the node's quasi-coherence clause.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, via the affine-open presentation.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; the canonical `hW.fromSpec` is an open
  immersion by `IsAffineOpen.isOpenImmersion_fromSpec`. The statement encodes
  the open subscheme directly as `W : X.Opens`, so no redundant hypothesis is needed.
- `def-weil-pbc-annihilator-associated-primes`:
  `WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes`,
  `RingTheory.annihilatorAssociatedPrimes`.
- `def-trf-relative-assassin`: `Sheaf.AlgebraicGeometry.RelativeAssassin`,
  `AlgebraicGeometry.Scheme.Modules.associatedPoints` (the node's absolute notion).
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; `isNoetherianRing_iff_ideal_fg` identifies its meaning.

Proof interfaces and imports:

- `lem-weil-pbc-affine-open-stalk-localization`: the Mathlib interfaces
  `IsAffineOpen.fromSpec_app_self`, `IsOpenImmersion` stalk-map isomorphism,
  `Scheme.Hom.germ_stalkMap`, `IsAffineOpen.fromSpec_primeIdealOf`, and
  `IsAffineOpen.isLocalization_stalk` are supplied by the affine-scheme import.
- `lem-sbc-affine-module-germ-localization`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization`,
  `AlgebraicGeometry.Scheme.isLocalizedModule_affine_germ`, ordinary proof import.
- `lem-weil-pbc-associated-prime-localize-at-prime`:
  `Sheaf.RingTheory.AssociatedPrimeLocalizeAtPrime`,
  `Module.associated_prime_localize_at_prime`, ordinary proof import.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` from
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, transitively imported by
  `AssociatedPrimeLocalizeAtPrime`.
- `def-weil-pbc-module-localization`: `LocalizedModule` from
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, transitively imported by
  the affine module-germ localization theorem.

The theorem docstring includes each of the five DAG proof steps: stalk
localization, forward preservation, finite-generator denominator product,
reverse annihilator inclusion by primality, and the Noetherian consequence.

Edge cases checked mathematically before writing:

- Empty X or empty W (including the zero coordinate ring): no x exists,
  so the pointwise assertion is vacuous; no Nonempty hypothesis excludes it.
- Zero F: zero stalks and zero section modules have no prime element
  annihilators, so both association predicates are false.
- A field and p = 0: the zero ideal is finitely generated by the empty family;
  the reverse proof uses the empty product 1, as the docstring specifies.
- Infinite-rank quasi-coherent modules: included without any finite-generation
  binder. The finite-generator argument concerns p alone.
- Non-Noetherian rings: the forward implication remains unconditional;
  the converse applies to every finitely generated prime, and the iff is
  asserted only conditionally on the coordinate ring being Noetherian.

Searches made with the prescribed msearch.py wrapper:

- LeanFinder: "Associated points of a quasi coherent sheaf on an affine open
  correspond to element annihilator associated primes of its sections with
  converse for finitely generated primes". Eight hits, concerning ideal-sheaf
  support and basic-open sections; none states this comparison.
- Loogle: `"associatedPrimes", "stalk"`. Zero hits.
- grep, AlgebraicGeometry: `associatedPoints|assassin|associated.*[Ss]talk|[Ss]talk.*associated`.
  Three hits in Morphisms/RingHomProperties, about checking morphism properties
  on stalks, not associated points.
- LeanSearch: "Associated points of a quasi coherent module sheaf on an affine
  open correspond to annihilator associated primes of its sections". Eight
  hits: algebraic associated-prime definitions/localization, primeIdealOf,
  and quasicoherence. No exact scheme-level theorem.
- Local rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `associatedPoints|annihilatorAssociatedPrimes|associated.*affine|affine.*associated`:
  found the recorded definitions and algebraic/local germ inputs, together with
  results about the structure sheaf or detection of sections, not this statement
  for arbitrary quasi-coherent F. A narrower search of affine-named modules in
  Sheaf/AlgebraicGeometry found no such theorem.
- Local rg for the item id in `lean/WeilConjectures`: no hits.
- Local rg for `affine_associated_points_primes` in the upstream declaration
  index and both source trees: no pre-existing declaration.

The source of Mathlib's associated-prime definition was read:
`Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean` explicitly uses radical
annihilators in the non-Noetherian setting. Thus that definition and its
localization results cannot silently substitute for the recorded
`RingTheory.annihilatorAssociatedPrimes` here.

No statement fault or disputed clause was found. No new node, dependency
repair, or statement correction is needed.

## Second reading by Q66

Performed a separate rereading of the source node and the final Lean file in
this same worker session, as the dispatcher forbids starting other agents.
The maintainer's independent review remains the independent reading.

The binders were checked again against each hypothesis: arbitrary scheme,
arbitrary quasi-coherent module, affine open, and a point of that open.
`hqc` imposes only quasi-coherence. `F.val.obj (op W)` is the actual section
module, and `hW.primeIdealOf x` is the canonical corresponding prime.
The two memberships use exactly the recorded annihilator-associated and
associated-point definitions. The first conjunct has no finiteness condition;
the second has FG on the prime only; the third has Noetherianity on the
coordinate ring only and the exact iff. Empty W, zero modules, and the zero
prime remain covered. The conjunction is precisely the three conclusions of
the node, with no additional claim. No mismatch was found and no change was
needed during this rereading. All proof bodies remain `sorry`.

Validation: the prescribed `scompile.py Q66 lem-sfb-affine-associated-points-primes`
command passed both sandbox and library compilation for the delivered module,
with no compiler errors or unexpected warnings. A local data comparison confirms
that only the item's `lean` field changes, its signature is copied verbatim,
and no Lean line exceeds 100 characters.
