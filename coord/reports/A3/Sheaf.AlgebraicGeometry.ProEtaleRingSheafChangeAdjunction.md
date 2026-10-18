## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleRingRestrictionDerivedDirectImage_exists`
in `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`. The proof constructs the
already specified derived mate, proves its normalization, and proves it invertible first
on K-injective representatives and then on every derived object.

The essential acyclicity input is the resolution clause of the existing
`CategoryTheory.ringedToposDerivedPushforwardComposition`. The source restriction and
pro-etale direct image are presented on AsSmall sites, and exact module equivalences
transport that clause back. Extracted the two existing generic ringed-topos constructors into
`Sheaf.CategoryTheory.ContinuousRingedToposModuleDirectImage` and
`Sheaf.CategoryTheory.RestrictionRingedToposModuleDirectImage`, imported only for the proof.
The old private constructor names in `EtaleModuleAbelianRingedPresentation` now abbreviate
these constructions. Its public theorem and proof are byte-for-byte unchanged. Added
proved public existence theorems for the generic constructions, and updated the existence
and étale-presentation DAG nodes.
The unchanged direct consumer `ModuleAbelianKInjectiveDirectImageAcyclic` compiles against
the adapted presentation (12.4 seconds). The generic interfaces are public and proved;
all helpers in the item are private and proved. The current completed item compiles
cleanly in 54.6 seconds. The adapted étale module was unclaimed; its constructor extraction
uses the unclaimed-module rule, and preserves its entire public theorem and proof.

The actual derived mate now has one private irreducible definition,
`canonicalDerivedMate`, with the proved API `canonicalDerivedMate_factors`. The existence
and final compatibility proofs reuse this normalization instead of expanding the same
concrete derived mate twice. All public definitions retain their original bodies.


## Proved and sorry left

Closed one of one initial holes:
`AlgebraicGeometry.Scheme.proEtaleRingRestrictionDerivedDirectImage_exists`, node
`lem-weil-pbc-ring-sheaf-change-adjunction-existence`.

Holes added: zero. Holes left in the delivered module: zero. Split-offs: zero.
The pre-existing uniqueness proof is retained. The final adjunction-compatibility proof
reuses the shared mate and its normalization; its statement is unchanged.
The sectionwise transport and the resolution clause are factored into private generic
lemmas in the same item file, reducing repeated checking of concrete sheaf definitions.

## No longer needed

For the existence node, `lem-pc-pre-derived-adjoint-functors-general`
(`Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`) is unnecessary: the proved
canonical derived-mate factorization supplies the normalization directly. No direct
import of that module was present to remove, and no module is withdrawn globally.
The composition theorem itself remains essential. The étale presentation replaces its proof-only
`Sheaf.CategoryTheory.GeometricModuleConstruction` import with the new generic modules;
the former remains an indirect dependency of the continuous constructor module. The
restriction constructor does not need its private operation maps, so its unused import
was removed.

## Where the brief, the DAG or earlier work was wrong

The planned transport of all three existential total right derived functors is
unnecessary. Only the composition theorem's resolution clause is needed. Naturality of
the derived unit and the already proved mate-factorization identity finish the existence
argument. No public statement, target signature, or unit route was changed. The two generic
private constructor definitions moved to the shared modules, with old names retained as
abbreviations; their bodies and meaning are unchanged.
Restriction is not assumed to preserve K-injective complexes, and no flatness of either
coefficient map is imposed.

## New nodes

`lem-weil-pbc-continuous-ringed-topos-module-direct-image` records the extracted,
fully proved construction. Its public theorem exposes the equality of the module
functor with continuous-site pushforward. The formula does not assume nonzero rings,
nonempty sites, or flat coefficient maps. Both constructors also retain their original
proofs of the generalized-element ring and module identities.

Change record: `coord/changes/A3-continuous-ringed-topos-constructors.md`.

`lem-weil-pbc-restriction-ringed-topos-module-direct-image` records the extracted,
fully proved identity-site restriction construction, including its module-functor equality.
It retains the original ring and module proofs, with no nonzero-ring assumption.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
