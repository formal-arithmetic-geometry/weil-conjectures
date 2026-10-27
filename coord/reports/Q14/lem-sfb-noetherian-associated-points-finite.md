## Worker report

Item: `lem-sfb-noetherian-associated-points-finite`, group Q14, stage 2.

The delivery adds `Sheaf.AlgebraicGeometry.NoetherianAssociatedPointsFinite`, containing
`AlgebraicGeometry.finite_associatedPoints`. The only proof is `by sorry`, as required
at this stage. No definition, dependency interface, statement, proof plan, or dependency
list is changed. The node copy changes only its `lean` field.

The source is Stacks Project, `literature/stacks-project/divisors.tex`,
`lemma-finite-ass` (Tag 05AF), lines 150-169: specialize the coherent module to the
structure sheaf and the quasi-compact open to the whole scheme. I also read
`lemma-associated-affine-open` (Tag 02OK), lines 68-120, which supplies the affine
translation in the node's proof. No source correction is needed.

Hypothesis and clause correspondence:

- A scheme X: `(X : Scheme.{u})`, with `universe u` explicitly declared and
  `set_option autoImplicit false`. There is no size restriction or fixed base.
- Locally Noetherian: `[IsLocallyNoetherian X]`, using the exact recorded Mathlib
  class. Its every-affine-open definition is equivalent to the stated existence
  of a Noetherian affine cover by the recorded cover equivalence theorems.
- Quasi-compact, every open cover having a finite subcover: `[CompactSpace X]`.
  Mathlib's class does not require a separation axiom or nonemptiness; it means
  compactness of the whole underlying space and hence exactly this open-cover
  property. No separatedness hypothesis is introduced.
- The stated set Ass(X): `associatedPoints X`, from the dependency's recorded
  `AlgebraicGeometry.associatedPoints`; it is not redefined. Its stalk predicate
  is `IsAssociatedPrime (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
  (X.presheaf.stalk x)`. Mathlib initially expresses association using a radical
  annihilator. The Mathlib instance in `AlgebraicGeometry.Noetherian`, line 349,
  makes every stalk Noetherian under the existing hypothesis, and
  `isAssociatedPrime_iff` in `AssociatedPrime.Basic`, lines 114-116, identifies
  this with primality and equality to an actual single-element annihilator.
  The maximal ideal of the local stalk is prime. The colon of the zero submodule
  by a singleton means exactly the set of scalars killing that element. Thus
  this recorded definition gives precisely the node's annihilator condition
  on every scheme quantified over by this theorem.
- Finiteness: `(associatedPoints X).Finite`, finiteness of this set of points.
- The empty scheme is allowed: no `Nonempty X` or point is required.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, and its
  `Scheme.Hom` signature and docstring, for `def-pc-scheme`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`
  and its affine-cover equivalences, for `pqf-def-locnoeth`.
- `Sheaf.AlgebraicGeometry.AssociatedPoints`: `AlgebraicGeometry.associatedPoints`,
  for `def-sc-associated-points`; the full definition and docstring were read.
- Proof import `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`,
  `isNoetherianRing_iff_ideal_fg`, `Ideal.fg_of_isNoetherianRing`.
- Proof import `Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness`:
  `associatedPrimes.finite`, with both `[IsNoetherianRing A]` and
  `[Module.Finite A M]`, for `lem-weil-pbc-noetherian-associated-primes-finite`.
- Proof imports `Mathlib.AlgebraicGeometry.AffineScheme`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`: the recorded
  `IsAffineOpen.fromSpec_app_self`, `IsAffineOpen.isOpenImmersion_fromSpec`,
  `IsAffineOpen.fromSpec_primeIdealOf`, `IsAffineOpen.isLocalization_stalk`,
  the open-immersion stalk-map isomorphism instance and
  `Scheme.Hom.germ_stalkMap` (the latter is in the public Scheme import),
  for `lem-weil-pbc-affine-open-stalk-localization`.
- Proof import `Sheaf.RingTheory.AssociatedLocalizationFg`:
  `Module.exists_annihilator_eq_of_localization_atPrime`, for
  `lem-sc-associated-localization-fg`. Its full localized-module hypothesis and
  annihilator conclusion match the use with the regular module.

All recorded proof dependencies that have declarations have imports, with
proof-only imports non-public. The docstring follows all four DAG proof steps:
a finite affine subcover, finite associated primes of each coordinate ring,
descent from stalk localization, and a finite union of finite images. No
additional postponed theorem is introduced.

Edge cases checked mathematically before writing:

- Empty scheme, including the spectrum of the zero ring: the set is empty;
  both hypotheses permit it, and no prime or point is selected by the signature.
- Spectrum of a field: the unique point is associated and the singleton is finite.
- Nonreduced schemes with embedded associated points, for example
  `Spec(k[x,y]/(x^2,xy))`: the predicate retains embedded points. It is not
  replaced by the set of generic points or irreducible components.
- Schemes need not be separated or affine. The node's proof uses a finite affine
  open cover rather than an added global affine or separation hypothesis.
- An infinite disjoint union of spectra of a field is locally Noetherian and
  has infinitely many associated points; it is excluded precisely by the
  explicit compactness hypothesis. Local Noetherianity alone is not substituted.

Searches for an existing statement (all run with the prescribed `msearch.py`
wrapper under Q14 and this item, unless stated otherwise):

1. LeanFinder: `The set of associated points of a quasi-compact locally
   Noetherian scheme is finite`. Eight hits; returned finite irreducible
   components, Artinian-scheme finiteness and Noetherian-scheme definitions.
   None states finiteness of the associated-point set.
2. LeanSearch: `A quasi-compact locally Noetherian scheme has finitely many
   associated points`. Eight hits; notably `associatedPrimes.finite` is the
   affine algebra input, and `finite_irreducibleComponents_of_isNoetherian`
   does not account for embedded associated points. No exact match.
3. Loogle: `AlgebraicGeometry.associatedPoints, Set.Finite`. Zero hits:
   Mathlib's search endpoint does not know the project-defined associatedPoints.
4. Mathlib grep: `associatedPoints|associated.points|finite_associated` in
   `AlgebraicGeometry`: zero hits.
5. Direct `rg -n` of `associatedPoints|finite_associated|associated.points` in
   `lean/WeilConjectures` and `lean/Sheaf`: found the recorded scheme definition,
   the distinct module-associated-points predicate, and unrelated assassin,
   weak-association, and base-change statements. None is this finiteness theorem.
6. Direct `rg -n` of `finite_associatedPoints|associatedPoints_finite` across
   Mathlib, `lean/WeilConjectures`, and `lean/Sheaf`: zero hits. The proposed full
   declaration name is unused.
7. Required `grep -rn` of the item id in `lean/WeilConjectures`: zero hits.
8. Direct `rg` of `associatedPoints|finite_associatedPoints` in
   `dag/lean_names_upstream.json`: zero hits.

There is no released repair note for the item. No statement dispute or node
fault was found. No new node or dependency module is needed.

Validation: `scompile.py Q14 lem-sfb-noetherian-associated-points-finite` compiled
the delivered module in both sandbox and library modes, each in 1.9 seconds,
with no diagnostic errors or unexpected warnings. The compiler is run only by
the authorized wrapper; the shared repository is read-only throughout.

## Second reading by Q14

The dispatcher explicitly prohibits starting other agents and assigns the
maintainer's independent review to the delivery. This section records a
separate in-thread rereading, not an independent-agent review.

I reopened the node and the finished module and compared every clause. The
scheme binder has an explicit universe; both local Noetherianity and
quasi-compactness remain separate hypotheses; the conclusion is exactly
finiteness of the recorded stalkwise associated-point set. In particular, the
radical-annihilator convention in Mathlib disappears by `isAssociatedPrime_iff`
because the stalks are Noetherian. CompactSpace imposes neither separation nor
nonemptiness. The empty case and embedded points remain present. All four
natural-language proof steps are in the docstring and all recorded proof
dependencies have imports. No mismatch was found, and no correction was made.
The independent mathematical reading remains with the maintainer as specified
in the dispatcher's brief.
