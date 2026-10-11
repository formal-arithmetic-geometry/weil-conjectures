## Worker report

The module `lean/Sheaf/RingTheory/StrictHenselizationRegular.lean` states
`isRegularLocalRing_iff_strictHenselization`, with proof `by sorry`, exactly the equivalence
of the first and third conditions of Stacks Tag 06LN. Its docstring carries all three
proof steps and their four DAG inputs. No proof is supplied in stage 2.

Hypothesis and clause correspondence:

- The arbitrary commutative local ring R is `{R : Type v} [CommRing R] [IsLocalRing R]`.
- R is Noetherian: `[IsNoetherianRing R]`, the declaration of
  `def-weil-pbc-noetherian-ring` in `Mathlib.RingTheory.Noetherian.Defs`.
- Its strict henselization is the arbitrary local commutative ring S, with
  `[CommRing S] [IsLocalRing S]`, `f : R →+* S`, and `h : IsStrictHenselization f e`.
  The local-ring assumption on S is part of specifying that object, not an extra
  restriction on strict henselizations. No Noetherianity assumption on S is imposed.
- The chosen separable closure of the residue field is `[Field K]` and
  `[Algebra (ResidueField R) K]`; `IsStrictHenselization f e` includes
  `IsSepClosure (ResidueField R) K`. The identification of S's residue field with
  that chosen closure is `e : ResidueField S ≃+* K`, compatible with f.
- R regular if and only if its strict henselization regular is precisely
  `IsRegularLocalRing R ↔ IsRegularLocalRing S`. This is the ring-level declaration
  recorded in the `mathlib_match` of `def-weil-regular-scheme`, from
  `Mathlib.RingTheory.RegularLocalRing.Defs`. Its full definition extends local and
  Noetherian and equates the maximal ideal's spanFinrank with ringKrullDim. The
  scheme-level part of that dependency is not needed here.

The additional dependency is `def-sc-ring-strict-henselization`, declaration
`IsStrictHenselization` in `Sheaf.RingTheory.StrictHenselization`. It uses the existing
`IsStrictlyHenselianLocalRing` from `Sheaf.RingTheory.HenselianTerminology`, and Mathlib's
`HenselianLocalRing`, `IsSepClosure`, `IsLocalRing.ResidueField`, `IsLocalRing.residue`,
and `IsLocalHom`. The two original dependency nodes and their signatures/docstrings
were read; the henselian terminology module and the separable-closure source module
were also read. The latter explicitly says that the separable closure itself is
Mathlib's `IsSepClosure`; the recorded upstream theorem describes the union of its
finite separable subextensions, not a competing definition.

Edge cases checked: dimension zero (a field, whose strict henselization is its
separable closure); positive dimension including DVRs; nonregular Noetherian local
rings (neither side is asserted regular independently); nonperfect residue fields
(the closure is separable, not replaced by an algebraic closure); all characteristics.
The zero ring has no local-ring instance and is not a local ring in the source's
convention. No dimension, domain, characteristic or finite-residue-field hypothesis
is imposed. The universe is explicit and arbitrary. All R, S, K can be placed in a
common universe, and the defining universal property tests T in that universe. This
suffices to identify S with the usual strict henselization: both objects are in the
same universe and the two inverse maps follow by uniqueness. Thus it does not lose
larger examples. No definition has postponed data or a postponed internal proof.

Searches (actual msearch results are in searches.jsonl):

- LeanFinder: "A Noetherian local ring is regular if and only if its strict
  henselization is regular": eight hits for henselian rings, regular sequences and
  DVR criteria; no equivalence.
- Loogle: `IsRegularLocalRing, HenselianLocalRing`: zero hits.
- Mathlib grep: `StrictHensel|strict.henseli`: zero hits.
- LeanSearch: "strict henselization of a local ring universal property henselian local
  ring separable closure residue field": unavailable, Internal Server Error.
- LeanFinder: "strict henselization local ring universal property": eight hits, all
  on henselian rings and root lifting; no strict-henselization definition.
- Loogle: `HenselianLocalRing`: seven hits; existing root-lifting class and its API,
  no strict-henselization universal property.
- Mathlib grep: `IsStrictHenselization|StrictHenselization|strict.henseli`: zero hits.
- Direct rg of the upstream WeilConjectures and local lean/Sheaf trees for strict
  henselization finds explanatory comments only, and no construction or predicate.
  Searching the item id upstream finds nothing. Full proposed declaration names
  were also searched in Mathlib, upstream, lean/Sheaf and dag/lean_names_upstream.json:
  no collisions.
- DAG search via rg and `tools/blueprint_refs.py search 'strict henselization'` finds
  `def-weil-pbc-strict-henselization-limit`, whose scheme-level pointed-neighbourhood
  construction has no Lean record, and statements using strict henselization.
  None gives the ring-level universal-property predicate delivered here.

The literature checkout is absent on this machine. The cited source was read directly
on the Stacks website: https://stacks.math.columbia.edu/tag/06LN and
https://stacks.math.columbia.edu/tag/0BSK, together with
https://stacks.math.columbia.edu/tag/08HR. There is no statement correction or dispute.

Validation: both modules compiled together on the server with scompile.py, exit 0,
without warnings. The initial combined compile redeclared a universe name across
modules; the theorem's explicit universe was renamed to v and the clean compile
followed. The theorem's proof remains exactly `by sorry`.

## New nodes

`def-sc-ring-strict-henselization` gives the ring-level universal-property predicate
`IsStrictHenselization` in `lean/Sheaf/RingTheory/StrictHenselization.lean`. Its source
is Stacks 04GQ/04GP, with the lifting property of 08HR and uniqueness of 08HS.
For a local map f and residue identification e it requires the specified separable
closure, strictly henselian S, compatibility over R, and unique compatible local
maps to all henselian local targets with a specified map from K on residue fields.
In Lean these are respectively `IsSepClosure`, `IsLocalHom f`,
`IsStrictlyHenselianLocalRing S`, the first equality of ring-hom compositions, and
`∀ T ... ∃! l ...`, including locality, `l.comp f = g` and the residue equality.
Every binder and universe is explicit. This characterizes the usual ring up to unique
compatible isomorphism: 08HR supplies the map out of the usual strict henselization;
the delivered universal property supplies the reverse map, and uniqueness gives the
inverse identities. It places no regularity or Noetherianity conditions in the
notion. Its dependencies cite the existing separable-closure and henselian terminology
nodes. The searches above found no ring-level definition; the existing scheme-limit
node states a different construction, not this predicate. No dependency module is
required and no existing node is copied or redefined.

## Second reading by C1

I reread the node statement, its source (Stacks Tag 06LN), the dependency records, and both
modules. The objects and hypotheses render as follows:

- The Noetherian local commutative ring is `{R : Type v}` with `[CommRing R]`,
  `[IsLocalRing R]`, and `[IsNoetherianRing R]`; these are exactly the node's R hypotheses.
- The strict henselization candidate is `{S : Type v}` with `[CommRing S]` and
  `[IsLocalRing S]`, together with `f : R →+* S`, `e : ResidueField S ≃+* K`, and
  `h : IsStrictHenselization f e`. The latter expands to the chosen separable closure,
  locality, strict henselianity, residue compatibility, and the universal property in
  `StrictHenselization.lean`.
- The residue-field closure is `{K : Type v}` with `[Field K]` and
  `[Algebra (ResidueField R) K]`, as required by the strict-henselization data.
- The conclusion is exactly `IsRegularLocalRing R ↔ IsRegularLocalRing S`, rendered by
  `isRegularLocalRing_iff_strictHenselization`. Mathlib's `IsRegularLocalRing` is the
  ring-level regular-local notion recorded by `def-weil-regular-scheme`, including the
  local and Noetherian fields and the maximal-ideal/Krull-dimension equality.

No hypothesis is added: in particular S has no separately imposed Noetherian instance;
that property is part of the regularity conclusion, as in the source. No clause or
quantifier is dropped. The source Tag 06LN states the equivalence of regularity of R and
its strict henselization under only Noetherian-local hypotheses, matching the Lean shape.
The source's henselization and strict-henselization comparisons supply the proof steps
recorded in the theorem docstring; the theorem remains intentionally `sorry` at stage 2.

I checked dimension-zero fields, positive-dimensional DVRs, nonregular Noetherian local
rings, arbitrary characteristics, nonperfect residue fields, and the empty/zero edge
convention (the zero ring has no `IsLocalRing` instance in the source convention). No
finite-residue-field, domain, dimension, or characteristic assumption is present, and
using an explicit common universe does not remove any source case.

The worker's searches were independently checked in Mathlib, the upstream
`WeilConjectures` tree, and `lean/Sheaf` for strict-henselization and regularity
statements, with LeanFinder/Loogle searches recorded in `searches.jsonl`; no existing
strict-henselization regularity theorem or predicate was found. The dependency
`IsRegularLocalRing` declaration was checked against Mathlib's source, and the new
`IsStrictHenselization` definition was checked against its dependency nodes and Stacks
Tags 04GQ/04GP/08HR. I found no mismatch and made no changes.

## Reviewer fix (R-shr1307, 2026-10-11)

F1's delivery landed first (4f26cb852) with the same new node id def-sc-ring-strict-henselization,
recorded as `Algebra.IsStrictHenselization R K C` (Stacks 04GW: colimit of pointed etale
R-algebras in `Over (CommAlgCat.of R K)`, K with `IsSepClosure` of the residue field). One
definition per notion (H4/H12): C1's second definition `IsStrictHenselization f e` and its module
lean/Sheaf/RingTheory/StrictHenselization.lean are not merged, and the theorem is restated as
`Algebra.isRegularLocalRing_iff_strictHenselization` over the landed predicate: R Noetherian local,
K a separable closure of its residue field (R acting through it), C an R-algebra with
`Algebra.IsStrictHenselization R K C`; conclusion `IsRegularLocalRing R ↔ IsRegularLocalRing C`.
No local or Noetherian instance on C is assumed (`IsRegularLocalRing C` contains both).
