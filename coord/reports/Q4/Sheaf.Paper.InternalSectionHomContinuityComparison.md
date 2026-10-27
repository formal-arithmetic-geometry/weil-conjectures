## What changed

In `Sheaf.Paper.InternalSectionHomContinuityComparison`, prove two existing
clauses without changing their statements or any public definitions.

`internalHomRepresentative_computes` lifts the entire natural comparison through
the fully faithful derived equivalence. The comparison is the composite of the
localization isomorphism, the actual representative counit, and the inverse
K-injective Hom factorization. A private categorical lemma checks that its
components satisfy the prescribed localization square. Naturality of the
K-injective factorization is taken directly from `Localization.fac`. The identity
calculation is proved for arbitrary functors before specializing to sheaves,
avoiding expensive unfolding of the localization construction.

`algebra_colimit_iff` constructs full faithfulness and essential surjectivity of
`sectionRingFunctor`. Ring maps lift to monoid maps on abelian groups, then on
presheaves and sheaves. For essential surjectivity, the abelian sheaf underlying
a ring sheaf has the canonical monoid structure transported along sheafification's
counit. The unit and multiplication comparison equations identify its section
ring with the original ring sheaf. Thus `Under.post sectionRingFunctor` is an
equivalence and preserves and reflects the colimit universal property.

All helper theorems are private and proved; the private reconstruction witnesses
are explicit constructions. There are no new public declarations,
statement changes, definition repairs, consumer adaptations, or new nodes. The
unit route is unchanged. These are DAG steps 3--4 and 10.

Keep the three private full-faithfulness witnesses irreducible. At the final
coefficient-diagram theorem, also keep the comparison, scalar-extension and
scalar-restriction functors folded; their stated APIs suffice there. This avoids
expanding localization and restriction implementations while checking its large
statement, without altering any public statement or global reducibility.

## Proved and sorry left

Closed 2 of the module's 9 original holes:

- `AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.internalHomRepresentative_computes`.
- `AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.algebra_colimit_iff`.

Added 0 holes. The following 7 named theorems retain their existing `sorry`, all
attached to node `lem-sfb-internal-section-hom-continuity-comparison` in
`dag/nodes/sec-six-functors-basics/` and all in namespace
`AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison`:

- `homPresentation_nonempty`.
- `internalScalarHom_identity`.
- `internalScalarHom_composition`.
- `scalarTransport_composition`.
- `restricted_hom_transport`.
- `internal_section_hom_continuity_comparison`.
- `scalarTransport_identity`.

This is a partial proof delivery, with no decomposition into new holed statements.

## No longer needed

Removed four private proof imports that no completed proof uses:

- `Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison`.
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`.

No module is withdrawn, and no whole-library declaration is removed. The DAG
still records the dependencies of the seven unfinished clauses; in particular,
the scalar comparison lemmas remain in their proof plans. No unit statement or
unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

DAG step 3's reference to `moduleObject_ringedSite_derived_comparison` produces
some closed tensor model, whereas `homPresentation_nonempty` asks for a
presentation for every prescribed model. A model-independence argument is still
needed there. The representative-computation clause proved in this delivery
already receives its prescribed normalized `HomPresentation`, so it needs only
its natural Hom isomorphism and the fixed K-injective factorization.

A complete development check with the new dependency predicates supplied at the
import boundary passed without warnings in 59.8 s. All temporary test modules
were removed. A direct server check confirms that the current dependency names
are available there; the local mirror still has older artifacts. The delivery
command uses `LCOMPILE_NO_LOCAL=1` for its final module compilation and axiom
probe against the server's published build.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
