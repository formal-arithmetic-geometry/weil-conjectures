## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.nagata_density_normalization`
in `Sheaf.Compactification.NagataDensityNormalization`, with its statement and
public imports unchanged. The proof derives the existing sheaf normalization,
using exact closed direct image from `condensed_open_closed_recollement`.
A proved private categorical lemma normalizes that isomorphism by the open
adjunction Hom bijection. Its invertibility follows from the invertible open
units and the sheaf-derived isomorphism. The second isomorphism is the precise
whiskered composite with `RootCoordinateFace.lowerComp` required by the statement.

The common-open square is a pullback by the schematic-image factorization and
injectivity of its closed inclusion. The existing
`derivedOpenRestrictionNormalization` theorem makes its actual derived mate
invertible for arbitrary commutative condensed coefficients. The remaining
identity comparison and unitor are already isomorphisms. This uses the stated
normalization dependency directly; no new intermediate statement is required.

Added private proof imports of `Sheaf.Paper.CondensedOpenClosedRecollement` and
`Sheaf.Paper.DerivedOpenRestrictionNormalization`. A private `import all` of the
already-public sheaf-comparison module reuses its proved `openUnit` helper.
Removed the two transparency-disabling settings. The command-change record is
`coord/changes/S2-nagata-density-proof-context.md`; no consumer requires adaptation.
Updated the item's node proof, proof dependencies and proof origin to match Lean.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.nagata_density_normalization`
(node `sk-lem-nagata-density-normalization`).

There are zero holes in the delivered module and zero added holes. The private
`isoOfOpenNormalization` lemma is completely proved. The proof uses the existing
stated `derivedOpenRestrictionNormalization`, whose own proof is still `sorry`;
that dependency is not duplicated or claimed proved here. This is a proof from
existing declared dependencies, not a new decomposition.

The remote Lean compile completed in 15.9 seconds. The suggested style cleanups
are included; final compilation, axiom and preflight checks run in `deliver3.py`.

## No longer needed

Removed the private import
`Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits`. The item's direct
proof no longer needs `det-sf-open-closed-pullback-limits`: exactness is provided
by the proved condensed open/closed recollement. This does not withdraw that
module or claim that its other consumers have disappeared.

The separate `det-nagata-density-normalization-pushforward` dependency is
unnecessary here: the second isomorphism is the explicit whiskered composite
with the compositor already specified in the conclusion. Its recorded module
is absent from the live source; this delivery neither deletes nor withdraws it.

The specialized `identity_open_derived_restriction` theorem and its normalization
formula are not used. In particular, no coefficient-admissibility hypothesis
is added. `lem-sfb-module-derived-compositor-coherence` is not a proof dependency:
its canonical identity isomorphism definition is enough, and is already public
through the unchanged statement imports. The coordinate-face theorem is likewise
not used; its module's public `lower` and `lowerComp` definitions remain needed.

The setup geometry and sheaf comparison stay used. Both paragraphs of the unit's
proof remain: exact termwise open/closed comparison, then derived composition.
No module is withdrawn, and no source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The specialized public `identity_open_derived_restriction` theorem assumes
localizing admissible coefficients, whereas this item's statement allows every
commutative condensed ring. The existing general pullback restriction theorem
supplies the required invertibility without changing either statement.

The latest blueprint states its conclusion for bounded constructible objects
and ell-adic fields. The assigned Lean statement is stronger: ordinary unbounded
objects over any commutative condensed coefficient ring and a Noetherian
compactification. Its exact termwise argument has the same route, and its entire
statement is preserved.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
