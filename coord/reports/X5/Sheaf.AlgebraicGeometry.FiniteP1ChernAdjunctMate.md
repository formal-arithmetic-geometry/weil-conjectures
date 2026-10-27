## What changed

Proved `AlgebraicGeometry.Etale.ordinaryFiniteP1_chern_adjunct_of_map_baseChange`
in `Sheaf.AlgebraicGeometry.FiniteP1ChernAdjunctMate`, preserving the original
signature and docstring. The proof transports the exact inverse-image mate to
the left-derived adjunctions. Compatibility of the canonical constant
comparisons with composition gives the constant square. Mate naturality and
the assumed Chern-map square then give the required adjunct square.
All new proof helpers are private and proved; the comparisons are the existing
canonical constructions.

The complete proof initially exceeded 60 seconds during kernel conversion.
`OrdinaryFiniteP1Kummer.ordinaryFiniteUnit` now uses the existing
`ordinaryFiniteDegreeZero`, sharing the cached embedding used by the twist line.
Its signature and mathematical object are unchanged. The two degree-zero
concentration instances now explicitly rewrite `ordinaryFiniteSingleFunctor_eq`
instead of asking conversion to unfold the object construction.

In `OrdinaryFiniteP1Arrows`, the constant comparison reuses the existing
`genericConstantIso` construction in `RelativeKummerExchangeGenerators`.
Its body expands to the original construction with the same arguments.
The new public import provides this definition body. Existing signatures,
attributes and visibility are preserved. Both definition modules are unclaimed.
The definition changes and users are recorded in
`coord/changes/X5-finite-p1-canonical-comparisons.md` and submitted for independent
review of their use in the targets.

The unclaimed `VectorIntegrationIdentityUnit` needs `genericConstantIso` in its
existing unfolding simp list: otherwise its `rw [constant_identity]` cannot see
the constant-sheaf comparison. A private import of the changed arrows module
makes this proof dependency explicit. Its signature and remaining proof stay
unchanged.

Private proof imports supply derived-adjunction compatibility, single-functor
composition, constant-sheaf composition, derived mates and derived base change.
The mate transport follows the existing private calculation in
`AffineTraceLineOpenCounitBaseChange`; the adjunct calculation follows
`WeilConjectures.AlgebraicGeometry.CartesianChartExchangeAdjunction`.
The item and definition nodes record the actual proof and implementation changes
in their proof steps, dependencies and origins.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Etale.ordinaryFiniteP1_chern_adjunct_of_map_baseChange`
(node `lem-sp-finite-p1-chern-adjunct-mate`).
No holes remain in the assigned module. Added holes: none. Split off: none.
The four supporting modules also have zero holes, before and after this change.
All five changed modules compile in the repaired delivery. The original consumers
`FiniteP1ChernAdjunctBaseChange`, `FiniteP1TwistedUnitBaseChange` and
`OrdinaryFiniteP1KummerMaps` also compile against the changed definitions.
The private overlay additionally rebuilt the scalar-faithfulness and fibre
homology dependencies successfully. `#print axioms` for the assigned theorem gives
only `propext`, `Classical.choice` and `Quot.sound`.

## No longer needed

Removed the unused proof dependency `lem-amb-mate-unit-counit` from the item node:
`unit_mateEquiv` and naturality of the adjunction Hom equivalence suffice.
No Lean module or declaration is withdrawn; no original import is removed.
The Mathlib declaration attached to that leaf remains in the library.

LeanFinder and Loogle found the generic mate identities. Searches of Mathlib and
the adopted source library identified the existing comparison APIs used here;
no theorem already supplied the entire normalized Chern adjunct square.

## Where the brief, the DAG or earlier work was wrong

The formal mate step also needs the identification of exact inverse-image
exchange with the left-derived mate, and composition compatibility of the
constant comparisons. Existing proved source APIs supply both. No mathematical
correction or unit-route change is needed. The categorical argument also works
for the zero coefficient ring, empty schemes and N = 1; no additional
nonvanishing assumption is used.

## Forced adaptations

Repair of reviewer C-66dc5's return on delivery `66dc52b8862`:
`Sheaf.AlgebraicGeometry.VectorTraceGeometricDescent` is unclaimed. The reviewer
confirmed its original compiles against the published build (57.8 seconds) but
fails against this delivery at lines 119:14 and 131:21:

```text
rw [hell, ← Category.assoc]
Did not find an occurrence of the pattern ?f ≫ ?g ≫ ?h
not type-correct under implicit transparency
```

The abbreviation `ordinaryFiniteUnit` now exposes the cached
`ordinaryFiniteDegreeZero`, whose object is obtained from
`ordinaryFiniteSingleFunctor`. The private proof
`vectorIntegration_eq_of_normalization` compares these objects with explicit
`DerivedCategory.singleFunctor` objects using `rw`. A command scoped to exactly
this private theorem marks the two cached wrappers locally `implicit_reducible`.
Thus its existing rewrite steps see the same single-functor objects they saw
before the definition change. No global attribute, declaration signature,
public import or other proof step changes. This is the only Lean change in the
newly adapted module. The complete repaired set compiles, including this
previously failing importer; no holes were added.

The second return point is repaired by adding
`lem-pur-relative-kummer-exchange-generators` to the item's `proof_deps` and to
the constant-comparison proof step's `uses`, since that step uses
`genericConstantIso` directly. The existing source and unit route are preserved.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
