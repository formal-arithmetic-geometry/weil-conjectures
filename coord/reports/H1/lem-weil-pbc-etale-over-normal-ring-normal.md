## Worker report

Item: lem-weil-pbc-etale-over-normal-ring-normal. The module
`Sheaf.RingTheory.EtaleNormalRing` states `RingHom.Etale.isNormalRing`, with its only
proof `by sorry`. The node statement and all other node fields are unchanged except `lean`.

Hypothesis and conclusion correspondence:

- Commutative rings A and B: `{A : Type uA} {B : Type uB} [CommRing A] [CommRing B]`.
  Both universes are explicitly declared and independent.
- A homomorphism A → B: `{f : A →+* B}`.
- Spec B → Spec A is etale (`def-weil-etale-morphism`): `(hf : f.Etale)`.
  This uses Mathlib's `RingHom.Etale`, the ring-map form explicitly permitted by
  brief-stage2 §3 (ÉTALE RING MAPS). It says precisely that the algebra induced by f
  is etale. For affine schemes this is equivalent to `AlgebraicGeometry.Etale`
  by the recorded Mathlib `HasRingHomProperty @Etale RingHom.Etale` instance and
  Stacks Tag 02GJ (2). No extra algebra structure is chosen or quantified over.
- A is normal (`def-weil-pbc-normal-ring`): `(hA : RingTheory.IsNormalRing A)`.
- B is normal: the conclusion `RingTheory.IsNormalRing B` uses the same definition.

Dependency declarations read and used:

- `def-weil-etale-morphism`: recorded `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`; read its full signature, docstring,
  and the affine ring-property instance. The imported ring form is
  `RingHom.Etale` from `Mathlib.RingTheory.RingHom.Etale`, whose full definition
  is `@Algebra.Etale R S _ _ f.toAlgebra`.
- `def-weil-pbc-normal-ring`: the old record gives ingredients only. The dependency
  module `Sheaf.RingTheory.NormalRing` supplies `RingTheory.IsNormalDomain` and
  `RingTheory.IsNormalRing`, using `IsDomain` from `Mathlib.Algebra.Ring.Defs`,
  `IsIntegrallyClosed` from `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  and `Localization.AtPrime` from `Mathlib.RingTheory.Localization.AtPrime.Basic`.
  Their full signatures and docstrings were read. `IsIntegrallyClosed` uses
  `FractionRing R`, so it is closure in the field of fractions when R is a domain.

The theorem docstring reproduces all three proof steps and their dependency node
ids: etale affine scheme morphism is smooth; affine smoothness is equivalent to
smoothness of the ring map; apply normality ascent for smooth maps (033C).

Sources checked directly online because the local Stacks source is not installed:
[033C](https://stacks.math.columbia.edu/tag/033C) gives ascent for arbitrary normal
rings, with no Noetherian assumption; [06DI](https://stacks.math.columbia.edu/tag/06DI)
uses this for etale algebras. [02GJ](https://stacks.math.columbia.edu/tag/02GJ)
gives the affine etale equivalence. The definitions are exactly
[0309](https://stacks.math.columbia.edu/tag/0309) and
[00GV](https://stacks.math.columbia.edu/tag/00GV).

Edge cases checked before writing:

- The zero ring is normal: there are no prime ideals, so the universal condition
  is vacuous. It is not a normal domain because `IsDomain` includes `Nontrivial`.
  The theorem imposes no nontriviality on A or B; in particular the map to the
  zero ring (empty affine scheme) is allowed.
- A product of normal domains may be normal without being a domain. Normality
  is required only of prime localizations, not of A or B themselves.
- Arbitrary non-Noetherian normal rings and rings of all characteristics are
  included. No finiteness hypothesis beyond etaleness is added.
- Identity maps and localizations satisfy the expected normality assertion.
- Universes are unrestricted independently for A and B; all binders are explicit.

Searches (msearch commands were run with group H1 and this item):

- LeanFinder: `An etale algebra over a normal ring is a normal ring` — eight
  results about standard etale algebras, `RingHom.Etale.toAlgebra`, composition,
  and `Algebra.Etale`; no normality ascent theorem.
- Loogle: `IsIntegrallyClosed, Algebra.Etale` — zero hits.
- msearch grep, RingTheory: `IsNormalRing|isNormalRing|[Ee]tale.*[Ii]ntegrallyClosed|[Ii]ntegrallyClosed.*[Ee]tale`
  — zero hits.
- LeanSearch: `normal ring defined by all prime localizations being integrally closed domains`
  — service unavailable, Internal Server Error; recorded as unavailable.
- Loogle: `IsNormalRing` — unknown identifier, zero hits.
- Direct rg of Mathlib/RingTheory, source WeilConjectures, and project lean/Sheaf:
  `IsNormalRing|isNormalRing|def.*Normal|normal.*[Ee]tale|[Ee]tale.*normal` — found
  normal scheme and normal integral component statements, but no declaration
  for general normal rings or the item's assertion.
- Direct rg of all Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json:
  `\b(IsNormalDomain|IsNormalRing)\b` — no existing declarations.
- Direct rg of the item's id in source WeilConjectures — no hits.
- Project `EtaleNormalComponents` cites this item in a proof docstring; it states
  a scheme component decomposition under additional Noetherian and integral
  hypotheses, so it is not an existing match.

Server verification: both sibling modules compile together cleanly (1.5 seconds),
with no errors or warnings. The first combined compile revealed a duplicated
universe name in the tool's concatenated file; the theorem now uses uA and uB,
which also makes the two independent universe parameters explicit.
No statement dispute, correction, or new DAG node is needed.

## Dependency modules

`def-weil-pbc-normal-ring` receives `Sheaf.RingTheory.NormalRing`. The old
`mathlib_match` supplies three general ingredients, not a usable named normal-ring
predicate. Its file is copied with only the `lean` field changed, including the
required explanatory note. Its `mathlib_match` stays unchanged.

Clause-by-clause rendering of the dependency node:

- A commutative ring R: `(R : Type u) [CommRing R]` in both definitions.
- R is an integral domain: `IsDomain R` in `IsNormalDomain R`.
- R is integrally closed in its fraction field: `IsIntegrallyClosed R`, conjoined
  with the domain condition. Mathlib's integral-closure predicate means every
  integral element of the fraction field lies in the image of R, equivalently
  every root of a monic polynomial lies in R.
- Every prime ideal p of R: `∀ (p : Ideal R) (_ : p.IsPrime)`.
- Its localization is a normal domain:
  `IsNormalDomain (Localization.AtPrime p)`.

Both definitions have complete data and no `sorry`. Both have source docstrings
with `(blueprint: def-weil-pbc-normal-ring)`; the module belongs to this one node.

## Second reading by H1

I independently compared the node, its source place, the dependency declarations, and the
Lean modules.

- The objects are commutative rings `A` and `B`, with independent explicit universes
  `uA` and `uB`; Lean renders these as `{A : Type uA} {B : Type uB}` with
  `[CommRing A] [CommRing B]`.
- The ring homomorphism is exactly `f : A →+* B`, rendered by the implicit binder
  `{f : A →+* B}`.
- The etale hypothesis on `Spec B → Spec A` is represented by the permitted equivalent
  ring-map form `hf : f.Etale`; no extra algebra, finiteness, or Noetherian assumptions
  occur.
- The normality hypothesis is `hA : RingTheory.IsNormalRing A`, using the dependency
  module's definition that every prime localization is a normal domain.
- The conclusion is exactly `RingTheory.IsNormalRing B`, with no dropped or strengthened
  clause and the same quantifier order.

The dependency module `Sheaf.RingTheory.NormalRing` was reread against
`def-weil-pbc-normal-ring`: `IsNormalDomain R` is `IsDomain R ∧ IsIntegrallyClosed R`,
and `IsNormalRing R` universally quantifies prime ideals and their `Localization.AtPrime`
localizations. Its definitions contain no hollow data. The etale predicate is Mathlib's
`RingHom.Etale`, the ring-map form allowed by the project convention and corresponding to
the affine etale morphism in the node.

I checked edge cases: zero rings and the resulting empty affine scheme are permitted;
normal rings need not be domains; identity maps and localizations are included; no
Noetherian, characteristic, nontriviality, or finiteness hypothesis is introduced; and
all characteristics and independent universes are covered. The empty prime-index family
is handled by the universal definition.

I searched the project, source checkout, Mathlib, and `dag/lean_names_upstream.json` by
normal-ring and etale-normality names and concepts, and used LeanFinder, Loogle, and
LeanSearch queries recorded in the worker report. No existing declaration states this
result or the named normal-ring predicate. The only issue found was procedural: the
worker report lacked this independent-reading section. I added this section; the Lean
statements and node statement required no mathematical correction.

## Reviewer fix (R-enn0959, stage 2)

The dependency module `Sheaf.RingTheory.NormalRing` (`RingTheory.IsNormalDomain`,
`RingTheory.IsNormalRing`) is left out and def-weil-pbc-normal-ring is kept as on
sheaf-dag (no record): the landed K1 statement
`CommAlgCat.isDomain_isIntegrallyClosed_injective_of_etale_colimit` (ccd06d885) already
writes "normal ring" out inline as
`∀ (p : Ideal A) [p.IsPrime], IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`,
and a second, packaged spelling would give the notion two forms (H4). The item's
hypothesis and conclusion now use that same inline spelling; `hf : f.Etale` is unchanged.
